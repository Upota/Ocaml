(* 1. smllest_divisor *)
let rec smallest_divisor : int -> int =
  fun n -> if n mod 2 = 0 then 2 else divide n 3
and divide : int -> int -> int =
  fun n x ->
    if x * x > n then n else if n mod x = 0 then x else divide n (x + 2)
  
let _ = smallest_divisor 15
let _ = smallest_divisor 121
let _ = smallest_divisor 141
let _ = smallest_divisor 199;;

(* 2. sigma *)
let rec sigma : (int -> int) -> int -> int -> int =
  fun f a b -> if a = b then f a else f a + sigma f (a + 1) b

  
let _ = sigma (fun x -> x) 1 10
let _ = sigma (fun x -> x * x) 1 7;;

(* forall *)
let rec forall : ('a -> bool) -> 'a list -> bool =
  fun f lst ->
    match lst with
      [] -> true
    | hd :: tl -> if f hd then forall f tl else false
  
let _ = forall (fun x -> x mod 2 = 0) [1; 2; 3]
let _ = forall (fun x -> x > 5) [7; 8; 9]
;;

(* app *)
let rec is_mem : 'a -> 'a list -> bool =
  fun e lst ->
    match lst with
      [] -> false
    | hd :: tl -> hd = e || is_mem e tl

let rec app_uniq : 'a list -> 'a list -> 'a list =
  fun l1 l2 ->
    match l1 with
      [] -> l2
    | hd :: tl ->
        if is_mem hd l2 then app_uniq tl l2 else app_uniq tl (l2 @ [hd])
    
let rec app : 'a list -> 'a list -> 'a list =
  fun l1 l2 -> app_uniq l1 (app_uniq l2 [])
;;

(* uniq *)
let rec uniq : 'a list -> 'a list =
  fun lst ->
    match lst with
      [] -> []
    | hd :: tl -> hd :: uniq (search hd (uniq tl))
and search : 'a -> 'a list -> 'a list =
  fun s l ->
    match l with
      [] -> []
    | hd :: tl -> if s = hd then tl else hd :: search s tl
  
let _ = uniq [5; 6; 5; 4];;

(* reduce *)
let rec reduce : ('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c =
  fun f xs ys c ->
    match xs with
      [] -> c
    | hd :: tl ->
        match ys with
          [] -> c
        | h :: t -> reduce f tl t (f hd h c)

let _ = reduce (fun x y z -> x * y + z) [1; 2; 3] [0; 1; 2] 0
let _ = reduce (fun x y z -> x * y + z) [1; 2; 3; 4] [0; 1; 2; 3] 0
;;

(* reach *)
type graph = (vertex * vertex) list
and vertex = int

(* Input validity checking *)
let rec is_valid : graph * vertex -> bool =
  fun (g, v) ->
    match g with
      [] -> false
    | (s, t) :: tl -> if v = s || v = t then true else is_valid (tl, v)

(* Utility function *)
let rec mem : 'a -> 'a list -> bool =
  fun e lst ->
    match lst with
      [] -> false
    | hd :: tl -> if e = hd then true else mem e tl

(* Main procedure *)
let rec add_vertex : vertex -> vertex list -> vertex list =
  fun v vs -> if mem v vs then vs else v :: vs

let rec next : vertex list -> graph -> vertex -> vertex list =
  fun vs g v ->
    match g with
      [] -> vs
    | (s, t) :: tl ->
        if s = v then next (add_vertex t vs) tl v else next vs tl v

let rec reach_helper : vertex list -> graph -> vertex list =
  fun vs g ->
    let vs' = List.fold_left (fun vs v -> next vs g v) vs vs in
    if vs = vs' then vs' else reach_helper vs' g

let rec reach : graph * vertex -> vertex list =
  fun (g, v) ->
    if is_valid (g, v) then reach_helper [v] g
    else raise (Failure "Invalid Input")
;;

(* diff *)
type aexp =
    Const of int
  | Var of string
  | Power of string * int
  | Times of aexp list
  | Sum of aexp list

let rec diff : aexp * string -> aexp =
  fun (exp, x) ->
    match exp with
      Const a -> Const 0
    | Var v ->
        if v = x then Sum [Times [Const 1]; Times [Var x; Const 0]]
        else Const 0
    | Power (v, a) ->
        if v = x then Times [Const a; Power (x, a - 1)] else Const 0
    | Times lst ->
        begin match lst with
          [hd] -> diff (hd, x)
        | hd :: tl ->
            Sum [Times ([diff (hd, x)] @ tl); Times [hd; diff (Times tl, x)]]
        | [] -> raise (Failure "Empty List")
        end
    | Sum lst ->
        match lst with
          [hd] -> diff (hd, x)
        | hd :: tl -> Sum ([diff (hd, x)] @ diff_sumlist (tl, x))
        | [] -> raise (Failure "Empty List")
and diff_sumlist (aexplist, x) =
  match aexplist with
    hd :: tl -> [diff (hd, x)] @ diff_sumlist (tl, x)
  | [] -> []
    
let _ = diff (Sum [Power ("x", 2); Times [Const 2; Var "x"]; Const 1], "x")
;;

(* balanced *)
type mobile = branch * branch
and branch =
    SimpleBranch of length * weight
  | CompoundBranch of length * mobile
and length = int
and weight = int

let rec balanced : mobile -> bool =
  fun m ->
    match m with b1, b2 -> if torque b1 = torque b2 then true else false
and torque : branch -> int =
  fun b ->
    match b with
      SimpleBranch (l, w) -> l * w
    | CompoundBranch (l, m) -> if balanced m then exactw b * l else 0
and exactw : branch -> int =
  fun b ->
    match b with
      SimpleBranch (l, w) -> w
    | CompoundBranch (l, m) -> match m with b1, b2 -> exactw b1 + exactw b2
                              
let _ =
  balanced
    (CompoundBranch
       (3,
        (CompoundBranch (2, (SimpleBranch (1, 1), SimpleBranch (1, 1))),
         SimpleBranch (1, 4))),
     SimpleBranch (6, 3))

let _ =
  balanced
    (CompoundBranch (2, (SimpleBranch (1, 1), SimpleBranch (1, 1))),
     SimpleBranch (1, 3))
;;

(* calculator *)
type exp =
    X
  | INT of int
  | ADD of exp * exp
  | SUB of exp * exp
  | MUL of exp * exp
  | DIV of exp * exp
  | SIGMA of exp * exp * exp

let rec apply : exp -> int -> int =
  fun e x ->
    match e with
      X -> x
    | INT n -> n
    | ADD (e1, e2) -> apply e1 x + apply e2 x
    | SUB (e1, e2) -> apply e1 x - apply e2 x
    | MUL (e1, e2) -> apply e1 x * apply e2 x
    | DIV (e1, e2) -> apply e1 x / apply e2 x
    | SIGMA (e1, e2, e3) ->
        let i = apply e1 x in
        let j = apply e2 x in
        if i > j then raise (Failure "Invalid Input")
        else if i = j then apply e3 i
        else apply e3 i + apply (SIGMA (ADD (e1, INT 1), e2, e3)) x
    
let rec calculator : exp -> int =
  fun exp ->
    match exp with
      X -> raise (Failure "Invalid Input")
    | INT n -> n
    | ADD (e1, e2) -> calculator e1 + calculator e2
    | SUB (e1, e2) -> calculator e1 - calculator e2
    | MUL (e1, e2) -> calculator e1 * calculator e2
    | DIV (e1, e2) -> calculator e1 / calculator e2
    | SIGMA (e1, e2, e3) ->
        let i = calculator e1 in
        let j = calculator e2 in
        if i > j then raise (Failure "Invalid Input")
        else if i = j then apply e3 i
        else apply e3 i + calculator (SIGMA (ADD (e1, INT 1), e2, e3))
;;
