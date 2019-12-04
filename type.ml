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
  | READ
  | IF (e1,e2,e3) ->
    let t1 = gen_equations tenv e1 TyBool in
    let t2 = gen_equations tenv e2 ty in
    let t3 = gen_equations tenv e3 ty in
    t1 @ t2 @ t3
  | LET (x,e1,e2) ->
    let nty = fresh_tyvar () in
    let t1 = gen_equations tenv e1 nty in
    let t2 = gen_equations (TEnv.extend (x,nty) tenv) e1 ty in
    t1 @ t2
  | LETREC (f,x,e1,e2)
  | PROC (x,e1) ->
    let nty1 = fresh_tyvar () in
    let nty2 = fresh_tyvar () in
    let t1 = gen_equations (TEnv.extend (x,nty1) e1 nty2) in
    [(ty,TyFun (nty1,nty2))] @ t1
  | CALL (e1,e2)) ->
    let nty = fresh_tyvar () in
    let t1 = gen_equations tenv e1 (TyFun (nty,ty)) in
    let t2 = gen_equations tenv e2 nty in
    t1 @ t2

let solve : typ_eqn -> Subst.t
=fun eqns -> Subst.empty (* TODO *)

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
