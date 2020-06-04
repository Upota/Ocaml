let sidx = ref 0
let new_state() = sidx := !sidx + 1; !sidx

type symbol = T of string | N of string | Epsilon | End | DOT
type production = (symbol * symbol list) list
type cfg = symbol list * symbol list * symbol * production

type state = int
type item_set = (symbol * symbol list) BatSet.t
type states = (state, item_set) BatMap.t
type edges = (state * symbol, state) BatMap.t
type srg = S of int | R of (symbol * symbol list) | G of int | ACC

type t = (symbol, symbol BatSet.t) BatMap.t  (* (symbol X, FIRST(X)) (symbol X, FOLLOW(X) ) *)
type m = (state * symbol, srg list) BatMap.t

let string_of_symbol a = match a with T s -> "T " ^ s | N s -> "N " ^ s | Epsilon -> "Epsilon " | End -> "End " | DOT -> "DOT "
let string_of_symbol2 a = match a with T s -> s | N s -> s | Epsilon -> "Epsilon " | End -> "End " | DOT -> "."
let string_of_set set =
  "{ " ^ (BatSet.fold (fun s str -> str ^ string_of_symbol s ^ ", ") set "") ^ " }"
let rec string_of_symbol_list lst = 
    match lst with
    | hd::tl -> string_of_symbol2 hd ^ " " ^ string_of_symbol_list tl
    | [] -> " "
    
let string_of_srg a = match a with S a -> string_of_int a | G a -> string_of_int a | ACC -> "ACC" | R (s,lst) -> string_of_symbol2 s ^ " -> " ^ string_of_symbol_list lst
let rec string_of_srg_list lst = 
    match lst with
    | hd::tl -> string_of_srg hd ^ " " ^ string_of_srg_list tl
    | [] -> " "

let print
=fun first ->
    BatMap.iter (fun s states ->
        prerr_endline (string_of_symbol s ^ " -> " ^ string_of_set states)) first;
    prerr_endline ""

let print_m
=fun table ->
    BatMap.iter (fun (s,a) srglst ->
        prerr_endline ("M [ " ^string_of_int s ^ ", " ^ string_of_symbol a ^ " ] = " ^ string_of_srg_list srglst);
        
        ) table;
    prerr_endline ""

let print_item_set
=fun i ->
    BatSet.iter (fun (s,lst) -> 
        prerr_endline (string_of_symbol2 s ^ " -> " ^ string_of_symbol_list lst)) i;
    prerr_endline ""

let print_states
=fun states-> BatMap.iter (fun s i -> 
        prerr_endline ("I" ^ string_of_int s ^ " -> ") ; print_item_set i) states;
    prerr_endline ""

let print_edges
=fun edge -> BatMap.iter (fun (s,a) i -> 
        prerr_endline ("I" ^ string_of_int s ^" "^ string_of_symbol2 a ^ " -> " ^ string_of_int i)) edge;
    prerr_endline ""

let rec check_SLR : cfg -> bool
=fun cfg -> 
    match cfg with
    (n,t,s,p) ->
        let terminal_updated = compute_first t p BatMap.empty in
        let first = fix (compute_first n p) terminal_updated in
        let follow = fix (compute_follow p first) (update_t s (BatSet.singleton End) BatMap.empty) in
        (* let _ = print follow in *)
        let arg_p = add_rule p s in                         (* argumented_production E' -> .E *)
        let (state_set, edge_set) = construct_automaton arg_p in
        let acc_rule = make_acc s in
        let table = construct_table (BatMap.empty) state_set edge_set follow acc_rule in
        (* print_m table;print_edges edge_set; print_states state_set; *)
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
    
and update_t s s' d = 
  let old = try BatMap.find s d with _ -> BatSet.empty in
    BatMap.add s (BatSet.union s' old) d

and add_rule : production -> symbol -> production       (* add [E' -> .E] *)
=fun p s ->
    match s with
    | N a -> [(N (a ^ "'"), [DOT;s])]@p
    | _ -> p

and closure : production -> item_set -> item_set       (* CLOSURE(I) I : (state, item_set) BatMap.t *)
=fun p i ->
    if BatSet.equal (run_clo p i i) i then i else closure p (run_clo p i i)

and run_clo : production -> item_set -> item_set -> item_set
=fun p set i ->
    if BatSet.is_empty i then set
    else
    let (item,i') = BatSet.pop i in
    let up_set = run_clo p set i' in
    BatSet.union up_set (eval_clo set item p)

and eval_clo : item_set -> (symbol * symbol list) -> production -> item_set     (* iteration for item *)
=fun set (n,r) p ->
    match r with
    | [] -> set
    | DOT::(N a)::tl ->
        let rules = List.filter (fun (x,_) -> if x = (N a) then true else false) p in
        let updated_set = rule2item set rules in updated_set
    | hd::tl -> eval_clo set (n,tl) p

and rule2item : item_set -> production -> item_set    (* any production *)
=fun i rules ->
    match rules with        (* (symbol * symbol list) list *)
    | [] -> i
    | (n,lst)::tl ->      (* B -> r *)     
        let up_i = rule2item i tl in
        let dot_rule = DOT::lst in       (* B -> .r *)
        BatSet.union (BatSet.singleton (n,dot_rule)) up_i

and eval_goto : item_set -> symbol -> item_set
=fun i x ->
    if BatSet.is_empty i then BatSet.empty
    else
    let ((n,r),i') = BatSet.pop i in
    let j = eval_goto i' x in
    if is_dotX x r then BatSet.add (n, move_dot r) j
    else j

and is_dotX : symbol -> symbol list -> bool             (* check item contains A -> a.Xb *)
=fun x r ->
    match r with
    | [] -> false
    | DOT::hd::tl -> if hd = x then true else false
    | hd::tl -> is_dotX x tl

and move_dot : symbol list -> symbol list
=fun r ->
    match r with
    | DOT::hd::tl -> hd::DOT::tl
    | hd::tl -> hd::(move_dot tl)
        
and construct_automaton : production -> states * edges
=fun p ->
    let s = new_state() in
    (* let _ = prerr_endline "check1" in *)
    let i_set = BatSet.singleton (List.hd p) in
    (* let _ = print_item_set i_set in *)
    let s_itemset = closure p i_set in
    let ini_t = BatMap.singleton s s_itemset in
    (* let _ = BatMap.iter (fun s i -> 
        prerr_endline ("I" ^ string_of_int s ^ " -> ") ; print_item_set i) ini_t in *)
    (* let _ = print_states ini_t in *)
    let ini_e = BatMap.empty in
    (* let _ = prerr_endline "check2" in *)
    (* let (t,e) = eval_automaton p ini_t ini_e in
    let _ = print_states t in
    let (t1,e1) = eval_automaton p t e in
    let _ = print_edges e1 in
    let _ = print_states t1 in *)
    let (t,e) = fix_automaton (eval_automaton p) ini_t ini_e in
    (* let _ = print_edges e; print_states t in *)
    (t,e)

and fix_automaton
=fun f t e ->
    let (new_t,new_e) = f t e in
    (* let _ = prerr_endline "fix check"; print_edges new_e; print_states new_t in *)
    if BatMap.equal (BatSet.equal) new_t t then (new_t,new_e) else fix_automaton f new_t new_e

and eval_automaton : production -> states -> edges -> states * edges        (* update T, S *)
=fun p t e ->
    if BatMap.is_empty t then (t,e)
    else
    let ((s,set_item),t') = BatMap.pop t in
    (* let _ = print_item_set set_item in *)
    (* let _ = prerr_int s; prerr_endline "" in *)
    let new_t, new_e = eval_automaton p t' e in
    (* let _ = prerr_int s; prerr_endline ""; print_edges new_e ;print_states new_t in *)
    (* let _ = print_item_set set_item; prerr_endline "current_edges\n"; print_edges e; prerr_endline "new_edges";print_edges new_e in *)
    let ret_t, ret_e = eval_each_item p s set_item new_t new_e set_item in
    (BatMap.union t ret_t, ret_e)

(* and eval_each_item : production -> state -> item_set -> states -> edges -> item_set -> states * edges       (* iterate for i *)
=fun p s i t e mem_i ->                       (* s: current state *)
    if BatSet.is_empty i then (t,e)
    else
    (* let _ = print_item_set i in *)
    let ((n,lst),i') = BatSet.pop i in                           (* (n,lst) : A -> a.Xb *)
    let new_t, new_e = eval_each_item p s i' t e mem_i in          
    let x = find_x lst in   (* find .X *)
    if x = DOT then (new_t,new_e)   (* A -> a. *)
    else
    let goto = closure p (eval_goto mem_i x) in                 (* goto : item_set *)
    let find_j = BatMap.filter (fun key value -> if BatSet.equal value goto then true else false) new_t in
    let s' = if (BatMap.mem (s,x) new_e) then BatMap.find (s,x) new_e
    else if BatMap.is_empty find_j then new_state()
    else 
        let ((k,v),j') = BatMap.pop find_j in k in
    let old_itemset = try BatMap.find s' new_t with _ -> BatSet.empty in
    let ret_i = BatSet.union old_itemset goto in
    let ret_t = BatMap.add s' ret_i new_t in
    let ret_e = BatMap.add (s,x) s' new_e in
    (* let _ = prerr_endline "check9" in *)
    (BatMap.union t ret_t, ret_e) *)

and eval_each_item : production -> state -> item_set -> states -> edges -> item_set -> states * edges       (* iterate for i *)
=fun p s i t e mem_i ->                       (* s: current state *)
    if BatSet.is_empty i then (t,e)
    else
    (* let _ = print_item_set i in *)
    let ((n,lst),i') = BatSet.pop i in                           (* (n,lst) : A -> a.Xb *)
    (* let new_t, new_e = eval_each_item p s i' t e mem_i in           *)
    let x = find_x lst in   (* find .X *)
    if x = DOT then eval_each_item p s i' t e mem_i   (* A -> a. *)
    else
    let goto = closure p (eval_goto mem_i x) in                 (* goto : item_set *)
    let find_j = BatMap.filter (fun key value -> if BatSet.equal value goto then true else false) t in
    let s' = if (BatMap.mem (s,x) e) then BatMap.find (s,x) e
    else if BatMap.is_empty find_j then new_state()
    else 
        let ((k,v),j') = BatMap.pop find_j in k in
    let old_itemset = try BatMap.find s' t with _ -> BatSet.empty in
    let ret_i = BatSet.union old_itemset goto in
    let ret_t = BatMap.add s' ret_i t in
    let ret_e = BatMap.add (s,x) s' e in
    (* let _ = prerr_endline "check9" in *)
    eval_each_item p s i' (BatMap.union t ret_t) ret_e mem_i

and find_x : symbol list -> symbol
=fun lst ->
    match lst with
    | DOT::hd::tl -> hd
    | hd::tl -> find_x tl
    | [] -> DOT

and make_acc : symbol -> (symbol * symbol list)
=fun s -> 
    match s with
    | N a -> (N (a ^ "'"), s::[DOT])

and construct_table : m -> states -> edges -> t -> (symbol * symbol list) -> m
=fun m1 s e f acc -> 
    let m2 = eval_table_shift m1 e in
    let m3 = eval_table_reduce m2 s f acc in
    m3

and eval_table_shift : m -> edges -> m
=fun m1 e ->
    if BatMap.is_empty e then m1
    else 
    let (((s,x),s'),e') = BatMap.pop e in
    match x with
    | T a -> eval_table_shift (update_m (s,x) (S s') m1) e'
    | N a -> eval_table_shift (update_m (s,x) (G s') m1) e'

and update_m
=fun (s,x) s' d ->
  let old = try BatMap.find (s,x) d with _ -> [] in
  if List.mem s' old then d
  else
    BatMap.add (s,x) (s'::old) d

and eval_table_reduce : m -> states -> t -> (symbol * symbol list) -> m
=fun m1 s f acc ->
    if BatMap.is_empty s then m1
    else 
    let ((n,i),s') = BatMap.pop s in
    let m2 = insert_reduce m1 n i f acc in
    eval_table_reduce m2 s' f acc 

and insert_reduce : m -> state -> item_set -> t -> (symbol * symbol list) -> m
=fun m1 n i f acc ->
    if BatSet.is_empty i then m1
    else
    let ((a,lst),i') = BatSet.pop i in
    (* let _ = prerr_endline (string_of_int n);prerr_endline "here" in *)
    (* let _ = prerr_endline (string_of_symbol2 a) in *)
    if (a,lst) = acc then insert_reduce (update_m (n,End) ACC m1) n i' f acc
    else if is_Xdot lst then
        (* let _ = prerr_endline "yes" in *)
        let rule = (a,getrule lst) in
        let set_f = BatMap.find a f in
        add_reduce m1 a n set_f rule
    else insert_reduce m1 n i' f acc

and is_Xdot : symbol list -> bool
=fun lst ->
    match lst with
    | [] -> false
    | hd::DOT::[] -> true
    | hd::tl -> is_Xdot tl

and getrule
=fun lst ->
    match lst with
    | hd::DOT::[] -> hd::[]
    | hd::tl -> hd::(getrule tl)

and add_reduce
=fun m1 a n set_f rule ->
    if BatSet.is_empty set_f then m1
    else 
    let (y,f') = BatSet.pop set_f in
    add_reduce (update_m (n,y) (R rule) m1) a n f' rule

let rec parse : cfg -> symbol list -> bool
=fun cfg sentence ->
    match cfg with
    (n,t,s,p) ->
        let terminal_updated = compute_first t p BatMap.empty in
        let first = fix (compute_first n p) terminal_updated in
        let follow = fix (compute_follow p first) (update_t s (BatSet.singleton End) BatMap.empty) in
        (* let _ = print follow in *)
        let arg_p = add_rule p s in                         (* argumented_production E' -> .E *)
        let (state_set, edge_set) = construct_automaton arg_p in
        let acc_rule = make_acc s in
        let table = construct_table (BatMap.empty) state_set edge_set follow acc_rule in
        let (start_state,i) = BatMap.min_binding state_set in
        let stack = [start_state] in
        parsing stack sentence table

and parsing : int list -> symbol list -> m -> bool
=fun stack input table ->
    match (stack,input) with
    | (hd::tl, h::t) -> 
        let look = try BatMap.find (hd,h) table with _ -> [] in
        begin match look with
        | [] -> false
        | [S a] -> parsing (a::hd::tl) t table
        | [G a] -> parsing (a::hd::tl) input table
        | [ACC] -> true
        | [R a] ->
            let (r, rule) = a in
            let leng = List.length rule in
            let new_stack = stack_poped stack leng in
            begin match new_stack with
            | d::l -> 
                let look1 = try BatMap.find (d,r) table with _ -> [] in
                begin match look1 with
                | [G n] -> parsing (n::d::l) input table
                | _ -> false
                end
            | [] -> false
            end
        end
    | _ -> false
 
and stack_poped : int list -> int -> int list
=fun stack i ->
    if i = 0 then stack
    else
    match stack with
    | hd::tl -> stack_poped tl (i-1)