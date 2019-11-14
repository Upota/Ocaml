type program = exp
and exp = 
  | UNIT
  | TRUE
  | FALSE
  | CONST of int
  | VAR of var
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | NIL
  | CONS of exp * exp      
  | APPEND of exp * exp
  | HEAD of exp
  | TAIL of exp
  | ISNIL of exp
  | IF of exp * exp * exp
  | LET of var * exp * exp
  | LETREC of var * var * exp * exp
  | LETMREC of (var * var * exp) * (var * var * exp) * exp
  | PROC of var * exp
  | CALL of exp * exp
  | PRINT of exp
  | SEQ of exp * exp
and var = string

type value = 
  | Unit 
  | Int of int 
  | Bool of bool 
  | List of value list
  | Procedure of var * exp * env 
  | RecProcedure of var * var * exp * env
  | MRecProcedure of (var * var * exp * env) * (var * var * exp * env)
and env = (var * value) list

let rec string_of_value v = 
  match v with
  | Int n -> string_of_int n
  | Bool b -> string_of_bool b
  | List lst -> "[" ^ List.fold_left (fun s x -> s ^ ", " ^ x) "" (List.map string_of_value lst) ^ "]"
  | _ -> "(functional value)"

exception UndefinedSemantics

let empty_env = []
let extend_env (x,v) e = (x,v)::e
let rec lookup_env x e = 
  match e with
  | [] -> raise (Failure ("variable " ^ x ^ " is not bound in env")) 
  | (y,v)::tl -> if x = y then v else lookup_env x tl

let rec eval : exp -> env -> value
=fun exp env ->
  match exp with
  | UNIT -> Unit
  | PRINT e -> (print_endline (string_of_value (eval e env)); Unit)
  | TRUE -> Bool true
  | FALSE -> Bool false
  | CONST n -> Int n
  | VAR var -> lookup_env var env
  | ADD (e1,e2) ->
    (match eval e1 env, eval e2 env with
    | Int n1, Int n2 -> Int (n1 + n2)
    | _ -> raise UndefinedSemantics)
  | SUB (e1,e2) ->
    (match eval e1 env, eval e2 env with
    | Int n1, Int n2 -> Int (n1 - n2)
    | _ -> raise UndefinedSemantics)
  | MUL (e1,e2) -> 
    (match eval e1 env, eval e2 env with
    | Int n1, Int n2 -> Int (n1 * n2)
    | _ -> raise UndefinedSemantics)
  | DIV (e1,e2) ->
    (match eval e1 env, eval e2 env with
    | Int n1, Int 0 -> raise UndefinedSemantics
    | Int n1, Int n2 -> Int (n1 / n2)
    | _ -> raise UndefinedSemantics)
  | EQUAL (e1,e2) ->
    (match eval e1 env, eval e2 env with
    | Int n1, Int n2 -> if n1 = n2 then Bool true else Bool false
    | Bool b1, Bool b2 -> if b1 = b2 then Bool true else Bool false
    | _ -> raise UndefinedSemantics)    
  | LESS (e1,e2) ->
    (match eval e1 env, eval e2 env with
    | Int n1, Int n2 -> if n1 < n2 then Bool true else Bool false
    | _ -> raise UndefinedSemantics)
  | NOT e ->
    (match eval e env with
    | Bool true -> Bool false
    | Bool false -> Bool true
    | _ -> raise UndefinedSemantics)
  | NIL -> List []
  | CONS (e1,e2) -> 
    (match eval e1 env, eval e2 env with
    | v, List l -> List (v::l)
    | _ -> raise UndefinedSemantics)    
  | APPEND (e1,e2) ->
    (match eval e1 env, eval e2 env with
    | List l1, List l2 -> List (l1@l2)
    | _ -> raise UndefinedSemantics)    
  | HEAD e ->
    (match eval e env with
    | List l ->
      (match l with
      | hd::tl -> hd
      | _ -> raise UndefinedSemantics)
    | _ -> raise UndefinedSemantics)
  | TAIL e ->
    (match eval e env with
    | List l ->
      (match l with
      | hd::tl -> List tl
      | _ -> raise UndefinedSemantics)
    | _ -> raise UndefinedSemantics)
  | ISNIL e ->
    (match eval e env with
    | List [] -> Bool true
    | List (hd::tl) -> Bool false
    | _ -> raise UndefinedSemantics)
  | IF (e1,e2,e3) ->
    (match eval e1 env with
    | Bool true -> eval e2 env
    | Bool false -> eval e3 env
    | _ -> raise UndefinedSemantics)
  | LET (x,e1,e2) ->
    let v1 = eval e1 env in
    let v = eval e2 (extend_env (x,v1) env) in v
  | LETREC (f,x,e1,e2) ->
    let rp = RecProcedure (f,x,e1,env) in
    let v = eval e2 (extend_env (f,rp) env) in v
  | LETMREC ((f,x,e1),(g,y,e2),e3) ->
    let mrp1 = MRecProcedure ((f,x,e1,env),(g,y,e2,env)) in
    let mrp2 = MRecProcedure ((g,y,e2,env),(f,x,e1,env)) in
    let v = eval e3 (extend_env (g,mrp2) (extend_env (f,mrp1) env)) in v
  | PROC (x,e) -> Procedure (x,e,env)
  | CALL (e1,e2) ->
    let v = eval e2 env in
    let ev = eval e1 env in
    (match ev with
    | Procedure (x,e,env1) -> eval e (extend_env (x,v) env1)
    | RecProcedure (f,x,e,env1) -> eval e (extend_env (x,v) (extend_env (f,ev) env1))
    | MRecProcedure ((f,x,ee1,env1),(g,y,ee2,env2)) ->
      let mrp1 = MRecProcedure ((f,x,ee1,env1),(g,y,ee2,env2)) in
      let mrp2 = MRecProcedure ((g,y,ee2,env2),(f,x,ee1,env1)) in
      eval ee1 (extend_env (x,v) (extend_env (g,mrp2) (extend_env (f,mrp1) env1)))
    | _ -> raise UndefinedSemantics)
  | SEQ (e1,e2) ->
  let v1 = eval e1 env in
  let v2 = eval e2 env in v2

let runml : program -> value
=fun pgm -> eval pgm empty_env;;

(* 1 *)
runml (LET ("x", CONST 1,
LET ("f", PROC ("y", ADD (VAR "x", VAR "y")),
LET ("x", CONST 2,
LET ("g", PROC ("y", ADD (VAR "x", VAR "y")),
ADD (CALL (VAR "f", CONST 1), CALL (VAR "g", CONST 1)))))));;

(* 2 *)
runml (LETREC ("double", "x",
IF (EQUAL (VAR "x", CONST 0), CONST 0,
ADD (CALL (VAR "double", SUB (VAR "x", CONST 1)), CONST 2)),
CALL (VAR "double", CONST 6)));;

(* 3 *)
runml (LETMREC
(("even", "x",
IF (EQUAL (VAR "x", CONST 0), TRUE,
CALL (VAR "odd", SUB (VAR "x", CONST 1)))),
("odd", "x",
IF (EQUAL (VAR "x", CONST 0), FALSE,
CALL (VAR "even", SUB (VAR "x", CONST 1)))),
CALL (VAR "odd", CONST 13))
);;

(* 4 *)
runml (LETREC ("factorial", "x",
IF (EQUAL (VAR "x", CONST 0), CONST 1,
MUL (CALL (VAR "factorial", SUB (VAR "x", CONST 1)), VAR "x")),
LETREC ("loop", "n",
IF (EQUAL (VAR "n", CONST 0), UNIT,
SEQ (PRINT (CALL (VAR "factorial", VAR "n")),
CALL (VAR "loop", SUB (VAR "n", CONST 1)))),
CALL (VAR "loop", CONST 10)))
);;

(* 5 *)
runml (
LETREC ("range", "n",
IF (EQUAL (VAR "n", CONST 1), CONS (CONST 1, NIL),
CONS (VAR "n", CALL (VAR "range", SUB (VAR "n", CONST 1)))),
CALL (VAR "range", CONST 10))
);;

(* 6 *)
runml (LETREC ("reverse", "l",
IF (ISNIL (VAR "l"), NIL,
APPEND (CALL (VAR "reverse", TAIL (VAR "l")), CONS (HEAD (VAR "l"), NIL))),
CALL (VAR "reverse", CONS (CONST 1, CONS (CONST 2, CONS (CONST 3, NIL)))))
);;

(* 7 *)
runml(
LET ("fix",
PROC ("f",
CALL
(PROC ("x",
CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))),
PROC ("x",
CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))))),
LET ("f",
CALL (VAR "fix",
PROC ("f",
PROC ("x",
IF (EQUAL (VAR "x", CONST 0), CONST 1,
MUL (CALL (VAR "f", SUB (VAR "x", CONST 1)), VAR "x"))))),
CALL (VAR "f", CONST 10)))
);;

runml(
LET ("fix",
PROC ("f",
CALL
(PROC ("x",
CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))),
PROC ("x",
CALL (VAR "f", PROC ("y", CALL (CALL (VAR "x", VAR "x"), VAR "y")))))),
LET ("f",
CALL (VAR "fix",
PROC ("range",
PROC ("n",
IF (EQUAL (VAR "n", CONST 1), CONS (CONST 1, NIL),
CONS (VAR "n", CALL (VAR "range", SUB (VAR "n", CONST 1))))))),
CALL (VAR "f", CONST 10)))
);;

runml(LETMREC(("sub","x",IF(EQUAL(VAR "x",CONST 0),CONST 0,ADD(VAR "x",CALL(VAR "sub",SUB(VAR "x",CONST 1))))),("f","x",LET("x",DIV(VAR "x",CONST 2),CALL(VAR "sub",VAR "x"))),CALL(VAR "f", CONST 10))
);;

runml(
  LETMREC(("f","n",IF(LESS(CONST 0,VAR "n"),ADD(CALL(VAR "f",SUB(VAR "n",CONST 1)),MUL(VAR "n",CALL(VAR "g",VAR "n"))),CONST 0)),("g","n",IF(LESS(CONST 0,VAR "n"),ADD(CONST 1,CALL(VAR "f",SUB(VAR "n",CONST 1))),CONST 1)),CALL(VAR "f",CONST 5))
);;

runml(
  LETREC("iter","n",PROC("f",IF(EQUAL(VAR "n",CONST 0),PROC("x",VAR "x"),PROC("x",CALL(CALL(CALL(VAR "iter",SUB(VAR "n",CONST 1)),VAR "f"),CALL (VAR "f",VAR "x"))))),CALL(CALL(CALL(VAR "iter",CONST 3),PROC ("x",ADD(VAR "x",CONST 2))),CONST 3))
);;

runml(
  LET("x",CONST 2,LETREC("f","y",IF(EQUAL(VAR "y",CONST 0),CONST 0,ADD(VAR "x",CALL (VAR "f", SUB(VAR "y",CONST 1)))),LET("x",CONST 5,CALL (VAR "f",VAR "x"))))
);;

runml(
  LETMREC(("f","lst",IF(ISNIL(VAR "lst"),NIL,APPEND(CALL(VAR "f",TAIL(VAR "lst")),CALL(VAR "g",VAR "lst")))),("g","lst",IF(ISNIL(VAR "lst"),NIL,CONS(HEAD(VAR "lst"),CALL(VAR "f",TAIL(VAR "lst"))))),CALL(VAR "f",CONS(CONST 1,CONS(CONST 3,CONS(CONST 5,NIL)))))
);;

runml(
  LETREC("concat","lst",IF(ISNIL(VAR "lst"),NIL,APPEND(HEAD(VAR "lst"),CALL(VAR "concat",TAIL(VAR "lst")))),CALL(VAR "concat",CONS(CONS(CONST 1,CONS(CONST 2,NIL)),CONS(CONS(CONST 3,CONS (CONST 4,CONS (CONST 5,NIL))),NIL))))
);;

runml(LETREC("drop","f",PROC("lst",IF(ISNIL(VAR "lst"),NIL,IF(CALL(VAR "f",HEAD(VAR "lst")),CALL(CALL(VAR "drop",VAR "f"),TAIL(VAR "lst")),VAR "lst"))),CALL(CALL(VAR "drop",PROC("x",LESS(CONST 5,VAR "x"))),CONS(CONST 1,CONS(CONST 3,CONS (CONST 7,NIL)))))
);;

runml(
LET("x",CONST 2,LET ("f",PROC("y",ADD(VAR "y",VAR "x")),LET("x",CONST 5,CALL (VAR "f",CONST 3))))
);;

runml(
  LETREC("factorial","x",IF(LESS(VAR "x",CONST 1),CONST 1,MUL(VAR "x",CALL (VAR "factorial",SUB(VAR "x",CONST 1)))),CALL (VAR "factorial",CONST 5))
);;

runml(
  IF(NOT FALSE,CONST 1,CONST 2)
);;

runml(
 TAIL(APPEND(CONS(CONST 1,NIL),CONS (CONST 2, CONS(CONST 3,NIL))))
);;

runml(
  CALL(PROC ("x",CONS (VAR "x",NIL)),CONST 1) 
);;