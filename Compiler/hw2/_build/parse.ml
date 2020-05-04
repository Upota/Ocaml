type symbol = T of string | N of string | Epsilon | End
type production = (symbol * symbol list) list
type cfg = symbol list * symbol list * symbol * production

type t = (symbol, symbol BatSet.t) BatMap.t  (* (symbol X, FIRST(X)) (symbol X, FOLLOW(X) ) *)
type m = (symbol * symbol, production) BatMap.t (* parsing table *)

let rec check_LL1 : cfg -> bool
=fun cfg -> 
    match cfg with
    (n,t,s,p) ->
        let terminal_updated = compute_first t p BatMap.empty in
        let first = fix (compute_first n p) terminal_updated in
        let follow = fix (compute_follow p first) (update_t s (BatSet.singleton End) BatMap.empty) in
        let table = build_table first follow p BatMap.empty in
        BatMap.for_all (fun x y -> if ((List.length y) > 1) then false else true) table

and fix
=fun f a ->
  if BatMap.equal (BatSet.equal) (f a) a then a else fix f (f a)

and compute_first : symbol list -> production -> t -> t     (* update FIRST SET about each symbols *)
=fun lst p first ->         (* lst = list of symbols *)
    match lst with
    | [] -> first
    | hd::tl -> 
        let up_fst = compute_first tl p first in
        begin
            match hd with
            | T _ -> update_t hd (BatSet.singleton hd) up_fst
            | N a -> 
                let rules = List.filter (fun (x,_) -> if x = hd then true else false) p in
                eval_fst (up_fst) hd rules
            | _ -> first
        end

and compute_follow : production -> t -> t -> t  
=fun p first follow ->
    match p with
    | [] -> follow
    | hd::tl -> 
        let up_flw = eval_flw first hd follow in
        compute_follow tl first up_flw

and eval_flw : t -> (symbol * symbol list) -> t -> t
=fun first (x,lst) follow ->
    match lst with
    | [] -> follow
    | [y] -> 
        begin match y with
        | T _ -> follow
        | N s -> 
            let follow_x = try BatMap.find x follow with _ -> BatSet.empty in
            update_t y follow_x follow
        | _ -> follow
        end
    | hd::tl ->
        let up_flw = eval_flw first (x,tl) follow in
        begin match hd with
        | T _ -> up_flw
        | N s -> 
            let first_str = eval_string_fstset first tl BatSet.empty in
            begin match BatSet.mem Epsilon first_str with
            | true -> 
                let follow_x = try BatMap.find x follow with _ -> BatSet.empty in
                update_t hd follow_x (update_t hd (BatSet.remove Epsilon first_str) up_flw)
            | false -> update_t hd (BatSet.remove Epsilon first_str) up_flw
            end
        | _ -> follow
        end

and eval_fst : t -> symbol -> production -> t  (* FIRST(X) *)
=fun first x p ->
    match p with
    | [] -> first
    | hd::tl ->
        let up_fst = eval_fst first x tl in
        begin match hd with                     (* looking production rules  X -> Y1 Y2 Y3 ... *)
        | (_,[]) -> update_t x (BatSet.singleton Epsilon) up_fst
        | (_,[y]) -> 
            begin match y with  (* Terminal or Non-terminal symbol *)
            | T _ -> update_t x (BatSet.singleton y) up_fst
            | N _ -> 
                let first_y = try BatMap.find y up_fst with _ -> BatSet.empty in
                update_t x first_y up_fst
            | _ -> first
            end
        | (_,y1::y2) ->
            let set = eval_string_fstset up_fst (y1::y2) BatSet.empty in
            update_t x set up_fst
        end

and eval_string_fstset : t -> symbol list -> symbol BatSet.t -> symbol BatSet.t
=fun first str fstset -> (* str = string alpha *)
    match str with 
    | [y] ->
        let first_y = try BatMap.find y first with _ -> BatSet.empty in
        BatSet.union first_y fstset
    | y1::y2 ->
        let first_y1 = try BatMap.find y1 first with _ -> BatSet.empty in
        if BatSet.mem Epsilon first_y1 then eval_string_fstset first y2 (BatSet.union (BatSet.remove Epsilon first_y1) fstset)
        else BatSet.union first_y1 fstset
    | _ -> fstset

and build_table : t -> t -> production -> m -> m
=fun first follow p table ->
    match p with
    | [] -> table
    | (x,lst)::tl ->  
        begin match lst with
        | [] ->     (* X -> e *)
            let follow_x = BatMap.find x follow in (* symbol BatSet.t *)
            build_table first follow tl (insert_table (x,lst) follow_x table)
        | _ ->
            let first_str = eval_string_fstset first lst BatSet.empty in
            if BatSet.mem Epsilon first_str then 
                let table1 = insert_table (x,lst) (BatSet. remove Epsilon first_str) table in
                let follow_x = BatMap.find x follow in
                let table2 = insert_table (x,lst) follow_x table1 in
                build_table first follow tl table2
            else
                let table1 = insert_table (x,lst) (BatSet. remove Epsilon first_str) table in
                build_table first follow tl table1
        end

and insert_table : (symbol * symbol list) -> symbol BatSet.t -> m -> m
=fun (x,lst) set table ->   (* set = FIRST(X) or FOLLOW(X) *)
    if BatSet.is_empty set then table
    else 
        let (a, set1) = BatSet.pop set in
        insert_table (x,lst) set1 (update_m (x,a) (x,lst) table)
    
and update_t s s' d = 
  let old = try BatMap.find s d with _ -> BatSet.empty in
    BatMap.add s (BatSet.union s' old) d

and update_m : (symbol * symbol) -> (symbol * symbol list) -> m -> m
=fun (s,a) s' d ->
  let old = try BatMap.find (s,a) d with _ -> [] in
  if List.mem s' old then d
  else
    BatMap.add (s,a) (s'::old) d

let rec parse : cfg -> symbol list -> bool
=fun cfg sentence ->
    match cfg with
    (n,t,s,p) ->
        let terminal_updated = compute_first t p BatMap.empty in
        let first = fix (compute_first n p) terminal_updated in
        let follow = fix (compute_follow p first) (update_t s (BatSet.singleton End) BatMap.empty) in
        let table = build_table first follow p BatMap.empty in
        let stack = s::[End] in
        parsing stack sentence table

and parsing : symbol list -> symbol list -> m -> bool
=fun stack input table ->
    match (stack,input) with
    | ([End],[End]) -> true
    | ((T x)::tl, a::t) -> if T x = a then parsing tl t table else false
    | ((N x)::tl, a::t) ->
        let lookAtable = try BatMap.find (N x,a) table with _ -> [] in
        begin match lookAtable with
        | [] -> false
        | [(x,ylst)] -> parsing (ylst@tl) input table
        | _ -> false
        end
    | _ -> false
