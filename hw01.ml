(* pascal *)
exception Problem

let rec pascal : int * int -> int =
  fun (n, m) ->
    if n < 0 || m > n then raise Problem
    else if m = 0 || m = n then 1
    else if m > 0 && m < n then pascal (n - 1, m - 1) + pascal (n - 1, m)
    else 0
  
let _ = pascal (0, 0)
let _ = pascal (1, 0)
let _ = pascal (1, 1)
let _ = pascal (2, 1)
let _ = pascal (4, 2)

let _ = try pascal (4, 6) with Problem -> 0;;

(* prime *)
let rec p : int -> int -> bool =
  fun n x ->
    if x * x > n then true else if n mod x = 0 then false else p n (x + 1)

let prime : int -> bool = fun n -> if n = 1 then false else let x = 2 in p n x
    
let _ = prime 2
let _ = prime 3
let _ = prime 4
let _ = prime 17;;

(* dfact *)
let rec dfact : int -> int =
  fun n -> if n = 0 || n = 1 then 1 else n * dfact (n - 2)
  
let _ = dfact 7
let _ = dfact 6;;

(* fastexpt *)
let rec fastexpt : int -> int -> int =
  fun b n ->
    if n = 0 then 1
    else if n mod 2 = 1 then b * fastexpt b (n - 1)
    else fastexpt b (n / 2) * fastexpt b (n / 2)
  
let _ = fastexpt 3 3
let _ = fastexpt 3 6;;

(* iter *)
let rec iter : int * (int -> int) -> int -> int =
  fun (n, f) ->
    match n with
      0 -> (fun x -> x)
    | _ -> fun x -> f (iter (n - 1, f) x)

let _ = iter (0, (fun x -> 2 + x)) 1
let _ = iter (5, (fun x -> 2 + x)) 0
;;

(* nat *)
type nat =
    ZERO
  | SUCC of nat

let rec natadd : nat -> nat -> nat =
  fun n1 n2 ->
    match n1 with
      ZERO -> n2
    | SUCC n1' -> natadd n1' (SUCC n2)
  
let rec natmul : nat -> nat -> nat =
  fun n1 n2 ->
    match n1 with
      ZERO -> ZERO
    | SUCC ZERO -> n2
    | SUCC n1' -> natadd n2 (natmul n1' n2)

let two = SUCC (SUCC ZERO)
let three = SUCC (SUCC (SUCC ZERO))
let _ = natmul two three
let _ = natadd two three
;;

(* mem *)
type btree =
    Empty
  | Node of (int * btree * btree)

let rec mem : int -> btree -> bool =
  fun n t ->
    match t with
      Empty -> false
    | Node (a, bt1, bt2) -> if n = a then true else mem n bt1 || mem n bt2


let t1 = Node (1, Empty, Empty)
let t2 = Node (1, Node (2, Empty, Empty), Node (3, Empty, Empty))

let _ = mem 1 t1
let _ = mem 3 t2
let _ = mem 4 t2
;;

(* eval *)
type formula =
    True
  | False
  | Not of formula
  | AndAlso of formula * formula
  | OrElse of formula * formula
  | Imply of formula * formula
  | Equal of exp * exp
and exp =
    Num of int
  | Plus of exp * exp
  | Minus of exp * exp

let rec evalexp : exp -> int =
  fun e ->
    match e with
      Num a -> a
    | Plus (a, b) -> evalexp a + evalexp b
    | Minus (a, b) -> evalexp a - evalexp b

let rec eval : formula -> bool =
  fun f ->
    match f with
      True -> true
    | False -> false
    | Not f1 -> if eval f1 then false else true
    | AndAlso (f1, f2) -> eval f1 && eval f2
    | OrElse (f1, f2) -> eval f1 || eval f2
    | Imply (f1, f2) ->
        if eval f1 = true && eval f2 = false then false else true
    | Equal (e1, e2) -> evalexp e1 = evalexp e2

let _ = eval (Imply (Imply (True, False), True))
let _ = eval (Not (OrElse (True, False)))
let _ = eval (Equal (Num 1, Plus (Num 1, Num 2)));;

(* max_min *)
exception EmptyList

let rec max : int list -> int =
  fun lst ->
    match lst with
      [hd] -> hd
    | hd :: tl -> let x = hd in if x > max tl then x else max tl
    | [] -> raise EmptyList

let rec min : int list -> int =
  fun lst ->
    match lst with
      [hd] -> hd
    | hd :: tl -> let x = hd in if x < min tl then x else min tl
    | [] -> raise EmptyList
  
let _ = max [1; 3; 5; 2]
let _ = min [1; 3; 2]

let _ = max [1; 5; 8; 9]
let _ = min [4; 6; 9; 1]

let _ = try max [] with EmptyList -> 0;;

(* drop *)
let rec drop : ('a -> bool) -> 'a list -> 'a list =
  fun f lst ->
    match lst with
      hd :: tl -> if f hd then drop f tl else hd :: tl
    | [] -> []

let _ = drop (fun x -> x > 5) [1; 3; 7]
let _ = drop (fun x -> x mod 2 = 1) [1; 3; 5; 6; 7]
let _ = drop (fun x -> x < 5) [1; 3; 5; 7];;
