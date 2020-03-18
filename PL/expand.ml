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

module Env = struct
  type t = (var * exp) list
  let empty = []
end

let rec find : var -> Env.t -> exp
  = fun x env -> match env with
    | (y,e)::tl -> if x = y then e else find x tl
    | [] -> VAR x

let rec sub : exp -> Env.t -> exp
= fun e env -> match e with
  | CONST n -> CONST n
  | VAR x -> find x env
  | ADD (e1,e2) -> ADD (sub e1 env,sub e2 env)
  | SUB (e1,e2) -> SUB (sub e1 env,sub e2 env)
  | MUL (e1,e2) -> MUL (sub e1 env,sub e2 env)
  | DIV (e1,e2) -> DIV (sub e1 env,sub e2 env)
  | ISZERO e1 -> ISZERO (sub e1 env)
  | READ -> READ
  | IF (e1,e2,e3) -> IF (sub e1 env,sub e2 env,sub e3 env)
  | LET (x,e1,e2) -> 
    let se1 = sub e1 env in
    let se2_ = sub e2 env in
    let se2 = sub se2_ ((x,se1)::env) in
    if se2 = se2_ then LET (x,se1,se2_) else se2
  | LETREC (f,x,e1,e2) -> LETREC (f,x,sub e1 ((x,VAR x)::env),sub e2 ((f,VAR f)::env))
  | PROC (x,e1) -> PROC (x,sub e1 ((x,VAR x)::env))
  | CALL (e1,e2) -> CALL (sub e1 env,sub e2 env)

let expand : exp -> exp 
=fun e -> match e with
  | LET (x,e1,e2) -> sub e []
  | LETREC (f,x,e1,e2) -> sub e []
  | _ -> e
;;

expand (LET ("x", CONST 1, VAR "x"));;
expand (
LET ("f", PROC ("x", VAR "x"),
IF (CALL (VAR "f", ISZERO (CONST 0)),
CALL (VAR "f", CONST 11),
CALL (VAR "f", CONST 22))));;
expand (LET ("x", ADD (CONST 1, ISZERO (CONST 0)), CONST 2));;
expand(PROC("x",VAR "x"));;
expand(LET("x",CONST 1,VAR "x"));;
expand(LET("x",PROC("x",VAR "x"),VAR "x"));;
expand (LET("x",ADD(VAR "x",CONST 1),VAR "x"));;
expand(LET("x",PROC("x",ADD(VAR "x",CONST 1)),VAR "x"));;
expand(ADD(LET("x",CONST 1,CONST 1),VAR "x"));; 
expand(LET("t",DIV(CONST 11,CONST 11),IF(ISZERO (VAR "t"),CONST 1,CONST 2)));;
expand(LET("t",MUL(CONST 1,CONST 12),PROC ("t",VAR "t")));;
expand(LET("x",CONST 1,ADD(PROC("x",VAR "x"),VAR "x")));;
expand(LETREC("f","x",CONST 1,LET("x",CONST 2,CALL(VAR "f",VAR "x"))));;
expand(LET("y",IF(CONST 11,CONST 12,CONST 13),PROC ("t",VAR "y")));;
expand(LET("x",LET("y",VAR "x",VAR "x"),CALL(VAR "x",CONST 1)));;
expand(LET("x",CONST 20,LETREC("f","x",CALL(VAR "f",VAR "x"),VAR "x")));;
expand(LET("t",CONST 15,LETREC("t","x",CONST 10,VAR "t")));;


(* expand(LET("f",PROC("f",VAR "f"),LET("f",CALL(PROC("f",VAR "f"),VAR "f"),VAR "f")));;
let f = proc f f in
  let f = CALL (proc f f) f in f
     *)
(* expand(LET("f",CALL(VAR "y",CONST 2),LET("f",VAR "f",CONST 1)));;
expand(LET("f",ISZERO(ISZERO (CONST 1)),LET("f", CONST 2,VAR "f")));;
expand(LETREC("f","x",CALL(VAR "f",SUB(VAR "x",CONST 1)),CALL (VAR "f",CONST 1)));;
expand(LET("x",CONST 1,LET("x",CONST 2,LET("x",ADD(CONST 3,VAR "x"),ADD(CONST 1,CONST 2)))));;
expand(LET("x",ADD(ISZERO (CONST 10),CONST 10),PROC("x",LET("x",CONST 10,VAR "x"))));; *)
