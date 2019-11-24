type exp =
  | NUM of int | TRUE | FALSE | UNIT
  | VAR of id
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | EQUAL of exp * exp
  | LESS of exp * exp
  | NOT of exp
  | SEQ of exp * exp                 (* sequence *)
  | IF of exp * exp * exp            (* if-then-else *)
  | WHILE of exp * exp               (* while loop *)
  | LETV of id * exp * exp           (* variable binding *)
  | LETF of id * id list * exp * exp (* procedure binding *)
  | CALLV of id * exp list           (* call by value *)
  | CALLR of id * id list            (* call by referenece *)
  | RECORD of (id * exp) list        (* record construction *)
  | FIELD of exp * id                (* access record field *)
  | ASSIGN of id * exp               (* assgin to variable *)
  | ASSIGNF of exp * id * exp        (* assign to record field *)
  | WRITE of exp
and id = string

type loc = int
type value =
| Num of int
| Bool of bool
| Unit
| Record of record 
and record = (id * loc) list
type memory = (loc * value) list
type env = binding list
and binding = LocBind of id * loc | ProcBind of id * proc
and proc = id list * exp * env

(************************************)
(*      List utility functions      *)
(************************************)
let rec list_length : 'a list -> int
= fun lst ->
  match lst with
  | [] -> 0
  | hd::tl -> 1 + list_length tl

let rec list_exists : ('a -> bool) -> 'a list -> bool
= fun pred lst ->
  match lst with 
  | [] -> false 
  | hd::tl -> if (pred hd) then true else list_exists pred tl

let rec list_fold2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
= fun func acc lst1 lst2 ->
  match (lst1, lst2) with
  | ([], []) -> acc
  | (hd1::tl1, hd2::tl2) -> list_fold2 func (func acc hd1 hd2) tl1 tl2
  | _ -> raise (Failure "list_fold2 : two lists have different length")

let rec list_fold : ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a
= fun func acc lst ->
  match lst with
  | [] -> acc
  | hd::tl -> list_fold func (func acc hd) tl 

(********************************)
(*     Handling environment     *)
(********************************)
let rec lookup_loc_env : id -> env -> loc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind (id, l) -> if (x = id) then l else lookup_loc_env x tl
    | ProcBind _ -> lookup_loc_env x tl
    end

let rec lookup_proc_env : id -> env -> proc
= fun x env ->
  match env with
  | [] -> raise(Failure ("Variable "^x^" is not included in environment"))
  | hd::tl ->
    begin match hd with
    | LocBind _ -> lookup_proc_env x tl
    | ProcBind (id, binding) -> if (x = id) then binding else lookup_proc_env x tl
    end

let extend_env : binding -> env -> env
= fun e env -> e::env

let empty_env = []

(***************************)
(*     Handling memory     *)
(***************************)
let rec lookup_mem : loc -> memory -> value
= fun l mem ->
  match mem with
  | [] -> raise (Failure ("location "^(string_of_int l)^" is not included in memory"))
  | (loc, v)::tl -> if (l = loc) then v else lookup_mem l tl

let extend_mem : (loc * value) -> memory -> memory
= fun (l, v) mem -> (l, v)::mem

let empty_mem = []

let size_of_mem mem = 
  let add_if_new x l = if list_exists (fun y -> x = y) l then l else x::l in
  let dom = list_fold (fun dom loc -> add_if_new loc dom) [] mem  in
    list_length dom

(***************************)
(*     Handling record     *)
(***************************)
let rec lookup_record : id -> record -> loc
= fun id record -> 
  match record with
  | [] -> raise(Failure ("field "^ id ^" is not included in record"))
  | (x, l)::tl -> if (id = x) then l else lookup_record id tl


let extend_record : (id * loc) -> record -> record
= fun (x, l) record -> (x, l)::record

let empty_record = []

(******************)
(* Pretty printer *)
(******************)
let rec value2str : value -> string
= fun v ->
  match v with
  | Num n -> string_of_int n
  | Bool b -> string_of_bool b
  | Unit -> "unit"
  | Record r -> "{" ^ record2str r ^ "}" 

and record2str : record -> string
= fun record ->
  match record with
  | [] -> ""
  | [(x, l)] -> x ^ "->" ^ string_of_int l
  | (x, l)::tl-> x ^ "->" ^ string_of_int l ^ ", " ^ record2str tl

let mem2str : memory -> string
= fun mem -> 
  let rec aux mem =
    match mem with
    | [] -> ""
    | [(l, v)] -> string_of_int l ^ "->" ^ value2str v
    | (l, v)::tl -> string_of_int l ^ "->" ^ value2str v ^ ", " ^ aux tl
  in
  "[" ^ aux mem ^ "]"

let rec env2str : env -> string
= fun env -> 
  let rec aux env =
    match env with
    | [] -> ""
    | [binding] -> binding2str binding
    | binding::tl -> binding2str binding ^ ", " ^ aux tl
  in
  "[" ^ aux env ^ "]"

and binding2str : binding -> string
= fun binding ->
  match binding with
  | LocBind (x, l) -> x ^ "->" ^ string_of_int l
  | ProcBind (x, proc) -> x ^ "->" ^ "(" ^ proc2str proc ^ ")"

and proc2str : proc -> string
= fun (xs, e, env) ->  
  let rec args2str xs =
    match xs with
    | [] -> ""
    | [x] -> x
    | x::tl -> x ^ ", " ^ args2str tl
  in
  "(" ^ args2str xs ^ ")" ^ ", E" ^ ", " ^ env2str env

(***************************)
let counter = ref 0
let new_location () = counter:=!counter+1;!counter

exception NotImplemented
exception UndefinedSemantics

let rec eval_aop : env -> memory -> exp -> exp -> (int -> int -> int) -> (value * memory)
= fun env mem e1 e2 op ->
  let (v1, mem1) = eval env mem e1 in
  let (v2, mem2) = eval env mem1 e2 in
  match (v1, v2) with
  | (Num n1, Num n2) -> (Num (op n1 n2), mem2)
  | _ -> raise (Failure "arithmetic operation type error")

and eval : env -> memory -> exp -> (value * memory) 
=fun env mem e -> 
  let mem = gc env mem in
  match e with
  | WRITE e -> 
    let (v1, mem1) = eval env mem e in
    let _ = print_endline (value2str v1) in
    (v1, mem1)
  | NUM n -> (Num n, mem)
  | TRUE -> (Bool true, mem)
  | FALSE -> (Bool false, mem)
  | UNIT -> (Unit, mem)
  | VAR x ->
    let l = lookup_loc_env x env in
    let v1 = lookup_mem l mem in
    (v1, mem)
  | ADD (e1,e2) ->
    eval_aop env mem e1 e2 (+)
  | SUB (e1,e2) ->
    eval_aop env mem e1 e2 (-)
  | MUL (e1,e2) ->
    eval_aop env mem e1 e2 ( * )
  | DIV (e1,e2) ->
    eval_aop env mem e1 e2 (/)
  | EQUAL (e1,e2) ->
    let (v1, mem1) = eval env mem e1 in
    let (v2, mem2) = eval env mem1 e2 in
    if v1 = v2 then (Bool true, mem2) else (Bool false, mem2)
  | LESS (e1,e2) ->
    let (v1, mem1) = eval env mem e1 in
    let (v2, mem2) = eval env mem1 e2 in
    begin match v1, v2 with
    | Num n1, Num n2 ->
      if n1 < n2 then (Bool true, mem2) else (Bool false, mem2)
    | _ -> raise UndefinedSemantics
    end
  | NOT e ->
    let (b, mem1) = eval env mem e in
    begin match b with
    | Bool true -> (Bool false, mem1)
    | Bool false -> (Bool true, mem1)
    | _ -> raise UndefinedSemantics
    end
  | SEQ (e1,e2) ->
    let (v1, mem1) = eval env mem e1 in
    let (v2, mem2) = eval env mem1 e2 in
    (v2, mem2)
  | IF (e1, e2, e3) ->
    let (b, mem1) = eval env mem e1 in
    begin match b with
    | Bool true -> eval env mem1 e2
    | Bool false -> eval env mem1 e3
    | _ -> raise UndefinedSemantics
    end
  | WHILE (e1, e2) ->
    let (b, mem1) = eval env mem e1 in
    begin match b with
    | Bool true ->
      let (v1, mem2) = eval env mem1 e2 in
      eval env mem2 (WHILE (e1,e2))
    | Bool false -> (Unit, mem1)
    | _ -> raise UndefinedSemantics
    end
  | LETV (x, e1, e2) ->
    let (v1, mem1) = eval env mem e1 in
    let l = new_location () in
    let env1 = extend_env (LocBind (x,l)) env in
    let mem2 = extend_mem (l,v1) mem1 in
    let (v2, mem3) = eval env1 mem2 e2 in
    (v2, mem3)
  | LETF (x, lst, e1, e2) ->
    let env1 = extend_env (ProcBind (x,(lst, e1, env))) env in
    let (v1, mem1) = eval env1 mem e2 in
    (v1, mem1)
  | CALLV (x, lst) ->
    let (idlst, ee, en) = lookup_proc_env x env in
    let (r, m, ex_mem) = 
    list_fold2 (fun (re, me, ex_m) x es ->
      let (v, mem1) = eval env me es in
      let l = new_location () in
      let reco = extend_env (LocBind (x,l)) re in
      let ex_me = extend_mem (l,v) ex_m in
      (reco, mem1, ex_me)) (empty_env, mem, empty_mem) idlst lst in
    let env_eval = [ProcBind (x, (idlst, ee, en))] @ r @ en in
    let mem_eval = m @ ex_mem in
    let (v_, mem_) = eval env_eval mem_eval ee in
    (v_, (mem_ @ mem))
  | CALLR (f, lst) ->
    let pro = lookup_proc_env f env in
      begin match pro with
      | (idlst, e_, env_) ->
        let env_eval =
        list_fold2 (fun env_up x y ->
          let l = lookup_loc_env y env in
          extend_env (LocBind (x,l)) env_up) env_ idlst lst in
        eval (env_eval @ [ProcBind (f, pro)]) mem e_
      end
  | RECORD lst ->
    if lst = empty_record then (Unit, mem)
    else
    let (ret_reco, rt_mem, ex_mem) =
    list_fold (fun (re, cu_me, me) (x, e) -> 
      let l = new_location () in
      let (v, mem1) = eval env cu_me e in
      let reco = extend_record (x,l) re in
      let ex_me = extend_mem (l,v) me in
      (reco, mem1, ex_me)) (empty_record, mem, empty_mem) lst in
    let ret_mem  = rt_mem @ ex_mem in
    (Record ret_reco, ret_mem)
  | FIELD (e, x) ->
    begin match eval env mem e with
    | (Record r, mem1) ->
      let l = lookup_record x r in
      let v = lookup_mem l mem1 in
      (v, mem1)
    | _ -> raise UndefinedSemantics
    end
  | ASSIGN (x, e) ->
    let (v1, mem1) = eval env mem e in
    let l = lookup_loc_env x env in
    let mem2 = extend_mem (l, v1) mem1 in
    (v1, mem2)
  | ASSIGNF (e1, x, e2) ->
    begin match eval env mem e1 with
    | (Record r, mem1) ->
      let (v, mem2) = eval env mem1 e2 in
      let l = lookup_record x r in
      let ret_mem = extend_mem (l,v) mem2 in
      (v, ret_mem)
    | _ -> raise UndefinedSemantics
    end

and gc : env -> memory -> memory
= fun env mem ->
  (* let _ = print_endline (env2str env) in
  let _ = print_endline (mem2str mem) in  *)
  let reach = list_fold  (fun reach_ hd ->
    begin match hd with
    | LocBind (x,l) -> extend_reach l reach_ mem
    | _ -> reach_
    end) empty_mem env
  in fix reach mem

and fix : memory -> memory -> memory
= fun reach mem ->
  let update = list_fold (fun reach_ (l,v) -> 
    begin match v with 
    | Record r -> record_reach reach_ r mem
    | _ -> reach_
    end) reach reach
  in
  if update = reach then reach
  else fix update mem

and record_reach : memory -> record -> memory -> memory
= fun reach r mem ->
  list_fold (fun reach_ hd ->
    begin match hd with
    | (x,l) -> extend_reach l reach_ mem
    end) reach r

and extend_reach : loc -> memory -> memory -> memory
= fun l reach mem ->
  if list_exists (fun (l1,v1) -> l1 = l || false) reach then reach
  else let v = lookup_mem l mem in extend_mem (l,v) reach

let runb : exp -> value 
= fun exp ->
  let (v, m) = eval empty_env empty_mem exp in
  let _ = print_endline ("memory size: " ^ string_of_int (size_of_mem m)) in
    v;;

runb(IF(EQUAL(ADD(NUM 1,NUM 3),DIV(NUM 12,SUB(NUM 4,NUM 1))),TRUE,FALSE));;
(* gc debug *)
runb(LETF("f",["x1";"x2"],SEQ(ASSIGN("x1",NUM 3),ASSIGN("x2",NUM 3)),LETV("x1",NUM 1,LETV("x2",NUM 1,SEQ(CALLV("f",[VAR "x1";VAR "x2"]),ADD(VAR "x1",VAR "x2"))))));;
runb(LETV("ret",NUM 1,LETV("n",NUM 5,SEQ(WHILE(LESS(NUM 0,VAR "n"),SEQ(ASSIGN("ret",MUL(VAR "ret",VAR "n")),ASSIGN("n",SUB(VAR "n",NUM 1)))),VAR "ret"))));;
runb(LETV("x",NUM 2,SEQ(ASSIGN("x",NUM 1),VAR "x")));;
runb(LETF("f",["x1";"x2"],SEQ(ASSIGN("x1",NUM 3),ASSIGN("x2",NUM 3)),LETV("x1",NUM 1,LETV("x2",NUM 1,SEQ(CALLR("f",["x1";"x2"]),ADD(VAR "x1",VAR "x2"))))));;
runb(LETV("x",NUM 1,LETV("y",NUM 2,LETF("f",["x1";"x2"],SEQ(SEQ(ASSIGN("x1",MUL(VAR "x1",NUM 2)),ASSIGN("x2",ADD(VAR "x2",NUM 2))),ADD(VAR "x1",VAR "x2")),SEQ(CALLR("f",["x";"y"]),LETV("r",ADD(VAR "x",VAR "y"),ADD(VAR "r",CALLV("f",[VAR "x";VAR "y"]))))))));;
runb(LETV("n",NUM 5,LETV("sum",NUM 0,LETF("calc",[],WHILE(NOT(EQUAL(VAR "n",NUM 0)),SEQ(ASSIGN("sum",ADD(VAR "sum",VAR "n")),ASSIGN("n",SUB(VAR "n",NUM 1)))),SEQ(CALLR("calc",[]),VAR "sum")))));;
runb(LETF("f",["n"],IF(LESS(VAR "n",NUM 2),NUM 1,ADD(CALLV("f",[SUB(VAR "n",NUM 1)]),CALLV("f",[SUB(VAR "n",NUM 2)]))),CALLV("f",[NUM 5])));;
runb(LETV("n",NUM 10,LETF("f",["x"],IF(EQUAL(VAR "n",NUM 0),UNIT,SEQ(SEQ(ASSIGN("x",ADD(VAR "x",NUM 1)),ASSIGN("n",SUB(VAR "n",NUM 1))),CALLR("f",["x"]))),LETV("x",NUM 10,SEQ(CALLR("f",["x"]),VAR "x")))));;
runb(LETV("x",NUM 5,LETV("y",NUM 5,LETF("f",["n"],SEQ(ASSIGN("n",ADD(VAR "n",NUM 1)),UNIT),ADD(SEQ(CALLR("f",["x"]),VAR "x"),SEQ(CALLV("f",[VAR "y"]),VAR "y"))))));;
runb(LETF("swap",["a";"b"], LETV("temp",VAR "a",SEQ(ASSIGN("a",VAR "b"),ASSIGN("b",VAR "temp"))),LETV("x",NUM 1,LETV("y",NUM 2,SEQ(CALLR("swap",["x";"y"]),VAR "x")))));;
runb(FIELD(RECORD([("id",NUM 123);("pw",NUM 123)]),"id"));;
runb(LETV("f",RECORD([("x",TRUE);("y",FALSE)]),SEQ(ASSIGNF(VAR "f","y",NOT (NOT TRUE)),FIELD(VAR "f","y"))));;
runb(LETV("f",RECORD([("x",NUM 5);("y",NUM 7)]),LETV("x",VAR "f",SEQ(ASSIGNF(VAR "f","x",NUM 6),FIELD(VAR "x","x")))));;
runb(LETV("x",NUM 1,LETV("f",RECORD([("x",NUM 1);("y",VAR "x")]),FIELD(VAR "f","y"))));;
runb(LETV("x",RECORD([("x",NUM 5);("y",NUM 7)]),SEQ(ASSIGNF(VAR "x","x",ADD(FIELD(VAR "x","x"),FIELD(VAR "x","y"))),FIELD(VAR "x","x"))));;
runb(LETV("f",RECORD([("x",NUM 10);("y",NUM 13)]),LETF("swap",["a";"b"],LETV("temp",VAR "a",SEQ(ASSIGN("a",VAR "b"),ASSIGN("b",VAR "temp"))),SEQ(CALLV("swap",[FIELD(VAR "f","x");FIELD(VAR "f","y")]),FIELD(VAR "f","x")))));;
runb(LETV("num",RECORD([("n",NUM 5);("is_even",FALSE)]),LETF("f",["n"],WHILE(EQUAL(NUM 0,FIELD(VAR "n","n")),SEQ(ASSIGNF(VAR "n","is_even",NOT(FIELD(VAR "n","is_even"))),ASSIGNF(VAR "n","n",SUB(FIELD(VAR "n","n"),NUM 1)))),SEQ(CALLR("f",["num"]),FIELD(VAR "num","is_even")))));;
