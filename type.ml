type program = exp
and exp = 
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | ISZERO of exp
  | READ
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | PROC of var * exp
  | CALL of exp * exp
and var = string

exception TypeError

type typ = TyInt | TyBool | TyFun of typ * typ | TyVar of tyvar
and tyvar = string
type typ_eqn = (typ * typ) list

let rec string_of_type ty = 
  match ty with
  | TyInt -> "int"
  | TyBool -> "bool"
  | TyFun (t1,t2) -> "(" ^ string_of_type t1 ^ " -> " ^ string_of_type t2 ^ ")"
  | TyVar x -> x

let print_typ_eqns eqns = 
  List.iter (fun (ty1,ty2) -> print_string (string_of_type ty1 ^ " = " ^ string_of_type ty2 ^ "\n")) eqns;
  print_endline ""

(* type environment : var -> type *)
module TEnv = struct
  type t = var -> typ
  let empty = fun _ -> raise (Failure "Type Env is empty")
  let extend (x,t) tenv = fun y -> if x = y then t else (tenv y)
  let find tenv x = tenv x
end

(* substitution *)
module Subst = struct
  type t = (tyvar * typ) list
  let empty = []
  let find x subst = List.assoc x subst

  (* walk through the type, replacing each type variable by its binding in the substitution *)
  let rec apply : typ -> t -> typ
  =fun typ subst ->
    match typ with
    | TyInt -> TyInt
    | TyBool -> TyBool 
    | TyFun (t1,t2) -> TyFun (apply t1 subst, apply t2 subst)
    | TyVar x -> 
      try find x subst
      with _ -> typ

  (* add a binding (tv,ty) to the subsutition and propagate the information *)
  let extend tv ty subst = 
    (tv,ty) :: (List.map (fun (x,t) -> (x, apply t [(tv,ty)])) subst)

  let print : t -> unit
  =fun subst -> 
      List.iter (fun (x,ty) -> print_endline (x ^ " |-> " ^ string_of_type ty)) subst
end

let tyvar_num = ref 0

(* generate a fresh type variable *)
let fresh_tyvar () = (tyvar_num := !tyvar_num + 1; (TyVar ("t" ^ string_of_int !tyvar_num)))

let rec gen_equations : TEnv.t -> exp -> typ -> typ_eqn 
=fun tenv e ty -> match e with 
  | CONST n -> [(ty,TyInt)]
  | VAR x -> [(TEnv.find tenv x,ty)]
  | ADD (e1,e2) ->
    let t1 = gen_equations tenv e1 TyInt in
    let t2 = gen_equations tenv e2 TyInt in
    [(ty,TyInt)] @ t1 @ t2
  | SUB (e1,e2) ->
    let t1 = gen_equations tenv e1 TyInt in
    let t2 = gen_equations tenv e2 TyInt in
    [(ty,TyInt)] @ t1 @ t2
  | MUL (e1,e2) ->
    let t1 = gen_equations tenv e1 TyInt in
    let t2 = gen_equations tenv e2 TyInt in
    [(ty,TyInt)] @ t1 @ t2
  | DIV (e1,e2) ->
    let t1 = gen_equations tenv e1 TyInt in
    let t2 = gen_equations tenv e2 TyInt in
    [(ty,TyInt)] @ t1 @ t2
  | ISZERO e1 ->
    let t1 = gen_equations tenv e1 TyInt in
    [(ty,TyBool)] @ t1
  | READ -> [(ty,ty)]
  | IF (e1,e2,e3) ->
    let t1 = gen_equations tenv e1 TyBool in
    let t2 = gen_equations tenv e2 ty in
    let t3 = gen_equations tenv e3 ty in
    t1 @ t2 @ t3
  | LET (x,e1,e2) ->
    let nty = fresh_tyvar () in
    let t1 = gen_equations tenv e1 nty in
    let t2 = gen_equations (TEnv.extend (x,nty) tenv) e2 ty in
    t1 @ t2
  | LETREC (f,x,e1,e2) ->
    let nty1 = fresh_tyvar () in
    let nty2 = fresh_tyvar () in
    let extenv = TEnv.extend (f,(TyFun (nty2,nty1))) tenv in
    let t1 = gen_equations (TEnv.extend (x,nty2) extenv) e1 nty1 in
    let t2 = gen_equations extenv e2 ty in
    t1 @ t2
  | PROC (x,e1) ->
    let nty1 = fresh_tyvar () in
    let nty2 = fresh_tyvar () in
    let t1 = gen_equations (TEnv.extend (x,nty1) tenv) e1 nty2 in
    [(ty,TyFun (nty1,nty2))] @ t1
  | CALL (e1,e2) ->
    let nty = fresh_tyvar () in
    let t1 = gen_equations tenv e1 (TyFun (nty,ty)) in
    let t2 = gen_equations tenv e2 nty in
    t1 @ t2

let rec unify : (typ * typ) -> Subst.t -> Subst.t
= fun ty subst -> match ty with
  | (TyInt,TyInt) -> subst
  | (TyBool,TyBool) -> subst
  | (TyVar a,ty1) ->
    begin match ty1 with
    | TyVar b ->
      if a = b then subst
      else Subst.extend a ty1 subst
    | TyFun (ty2,ty3) ->
      if TyVar a = ty2 || TyVar a = ty3 then raise TypeError
      else Subst.extend a (TyFun (ty2,ty3)) subst
    | _ -> Subst.extend a ty1 subst
    end
  | (ty1,TyVar a) -> unify (TyVar a,ty1) subst
  | (TyFun (ty1,ty2),TyFun (ty11,ty22)) ->
    let s = unify (ty1,ty11) subst in
    let st1 = Subst.apply ty2 s in
    let st2 = Subst.apply ty22 s in
    let ss = unify (st1,st2) s in
    ss
  | (_,_) -> raise TypeError

let rec unifyall : typ_eqn -> Subst.t -> Subst.t
= fun eqns subst -> match eqns with
  | [] -> subst
  | (ty1,ty2)::tl ->
    let st1 = Subst.apply ty1 subst in
    let st2 = Subst.apply ty2 subst in
    let s = unify (st1,st2) subst in
    unifyall tl s

let solve : typ_eqn -> Subst.t
= fun eqns -> unifyall eqns Subst.empty

let typeof : exp -> typ 
=fun exp ->
  let new_tv = fresh_tyvar () in
  let eqns = gen_equations TEnv.empty exp new_tv in
  let _ = print_endline "= Equations = ";
          print_typ_eqns eqns in
  try 
    let subst = solve eqns in
    let ty = Subst.apply new_tv subst in
      print_endline "= Substitution = ";
      Subst.print subst;
      print_endline "";
      print_endline ("Type of the given program: " ^ string_of_type ty);
      print_endline "";
      ty
  with TypeError -> (print_endline "The program does not have type. Rejected."); exit (1);;

(* typeof(LET ("f", PROC ("x", VAR "x"),
IF (CALL (VAR "f", ISZERO (CONST 0)),
CALL (VAR "f", CONST 11),
CALL (VAR "f", CONST 22))));; *)

typeof(IF (CALL (PROC ("x", VAR "x"), ISZERO (CONST 0)),
 CALL (PROC ("x", VAR "x"), CONST 11), CALL (PROC ("x", VAR "x"), CONST 22)));;
(* typeof(PROC ("f",
PROC ("x", SUB (CALL (VAR "f", CONST 3),
CALL (VAR "f", VAR "x")))));;

typeof(PROC ("f", CALL (VAR "f", CONST 11)));;

typeof(DIV(ADD(CONST 1,CONST 3),CONST 0));;

typeof(IF (ISZERO (CONST 10),CONST 1, READ));; *)
(* typeof(LET("x",READ,IF(ISZERO(VAR "x"),ADD(VAR "x",CONST 1),IF(ISZERO(ADD(VAR "x",CONST 1)),VAR "x",CONST 0))));; *)
(* typeof(PROC("x",PROC("y",ISZERO(VAR "x"))));;
typeof(PROC("f",PROC("x",ADD(CONST 1,CALL (VAR "f",VAR "x")))));;
typeof(PROC("f",PROC("x",IF(CALL(VAR "f",VAR "x"),CONST 1,CONST 0))));;
typeof(LET("x",CONST 1,LETREC("f","x",IF(ISZERO (VAR "x"),CONST 1,CONST 2),VAR "x")));; *)
(* typeof(LET ("x", CONST 1,
IF (VAR "x", SUB (VAR "x", CONST 1), CONST 0)));; *)
(* typeof(LET("x",READ,IF(ISZERO(VAR "x"),ADD(VAR "x",CONST 1),IF(ISZERO(ADD(VAR "x",CONST 1)),VAR "x",CONST 0))));; *)

(* typeof(LET("f",PROC("y",VAR "y"),LET("g",CALL(VAR "f",CONST 1),LET("h",CALL(VAR "f",CONST 2),VAR "g"))));; *)
(* TyInt *)
(* let f = proc (y) (y) in
  let g = f 1 in
    let h = f 2 in
      g *)

(* typeof(LET("f",PROC("y",VAR "y"),LET("g",CALL(VAR "f",CONST 1),LET("h",CALL(VAR "f",ISZERO(CONST 0)),VAR "g"))));; *)
(* exception *)

(* typeof(LET("f",PROC("x",PROC("y",ADD(VAR "x",VAR "y"))),ADD(CALL (VAR "f",CONST 1),CONST 2)));; *)
(* typeof(LET("x",CONST 1,LET("f",PROC("x",IF(VAR "x",CONST 1,CONST 2)),LET("g",PROC ("x",PROC("y",ADD(VAR "y",CONST 1))),CALL(VAR "g",CALL(VAR "f",ISZERO(CONST 0)))))));;
typeof(LET("f",PROC("f",CALL(VAR "f",CONST 11)),LET("g",PROC("g",ADD(VAR "g",CONST 10)),PROC("c",ADD(CALL(VAR "f",VAR "g"),VAR "c")))));;
typeof(LETREC("bin2dec","bin",PROC("depth",IF(ISZERO(VAR "bin"),CONST 0,LET("remainder",SUB(VAR "bin",MUL(DIV(VAR "bin",CONST 10),CONST 10)),ADD(MUL(VAR "remainder",VAR "depth"),CALL(CALL(VAR "bin2dec",DIV(VAR "bin",CONST 10)),MUL(VAR "depth",CONST 2)))))),VAR "bin2dec"));;
typeof(LET("modular",PROC("x",PROC("y",SUB(VAR "x",MUL(VAR "y",DIV(VAR "x",VAR "y"))))),CALL(VAR "modular",READ)));;
typeof(LETREC("reverse","n",PROC("result",IF(VAR "n",VAR "result",LET("remainder",SUB(VAR "n",MUL(DIV(VAR "n",CONST 10),CONST 10)),CALL(CALL(VAR "reverse",DIV(VAR "n",CONST 10)),ADD(MUL(VAR "result",CONST 10),VAR "remainder"))))),CALL(CALL(VAR "reverse",READ),CONST 0)));; *)