let rec length l = 
  match l with 
  | [] -> 0
  | hd::tl -> 1 + length tl;;

let rec append l1 l2 =
  match l1 with
  | [] -> l2
  | hd::tl -> hd::(append tl l2);;

let rec reverse l =
  match l with
  | [] -> []
  | hd::tl -> (reverse tl)@[hd];;

let rec nth l n =
  match l with
  | [] -> raise (Failure "list is too short")
  | hd::tl -> match n with
              | 0 -> hd
              | _ -> nth tl (n-1);;

let rec remove_first a l =
  match l with
  | [] -> []
  | hd::tl -> match a with
              | 1 -> tl
              | _ -> hd::(remove_first (a-1) tl);;

let rec insert a l =
  match l with
  | [] -> [a];
  | hd::tl -> if a > hd then hd::(insert a tl)
              else a::l;;

let rec insertion_sort l =
  match l with
  | [] -> []
  | hd::tl -> insert hd (insertion_sort tl);;
  