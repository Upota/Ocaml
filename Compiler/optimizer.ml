type cfg = blocks * edges
and blocks = block list
and block = blabel * T.linstr
and blabel = int
and edges = edge list
and edge = blabel * blabel

let b_label = ref 0
let new_b_label() = b_label := !b_label + 1; !b_label

(*************************************)
(*        Print func.                *)
(*************************************)

let pp : cfg -> unit
=fun (b,e) -> 
  let ps = print_string in
  let pn = print_endline in
  let s_bop o = match o with T.ADD -> "+" | T.SUB -> "-" | T.MUL -> "*" | T.DIV -> "/"
  | T.LT -> "<" | T.LE -> "<=" | T.GT -> ">" | T.GE -> ">=" | T.EQ -> "==" | T.AND -> "&&" |
  T.OR -> "||" in
  let s_uop o = match o with T.MINUS -> "-" | T.NOT -> "!" in
  let s_arr (x,y) = x ^ "[" ^ y ^ "]" in
	pn ("----print cfg ----");
  List.iter (fun (bl,(label, instr)) ->
    ps ("B" ^ string_of_int bl ^ "  ");
    ps (string_of_int label ^ " : ");
    match instr with
    | T.HALT -> pn "HALT"
    | T.SKIP -> pn "SKIP"
    | T.ALLOC (x,n) -> pn (x ^ " = alloc (" ^ string_of_int n ^ ")")
    | T.ASSIGNV (x,o,y,z) -> pn (x ^ " = " ^ y ^ " " ^ s_bop o ^ " " ^ z)
    | T.ASSIGNC (x,o,y,n) -> pn (x ^ " = " ^ y ^ " " ^ s_bop o ^ " " ^ string_of_int n)
    | T.ASSIGNU (x,o,y) -> pn (x ^ " = " ^ s_uop o ^ y)
    | T.COPY (x,y) -> pn (x ^ " = " ^ y)
    | T.COPYC (x,n) -> pn (x ^ " = " ^ string_of_int n)
    | T.UJUMP label -> pn ("goto " ^ string_of_int label)
    | T.CJUMP (x,l) -> pn ("if " ^ x ^ " goto " ^ string_of_int l)
    | T.CJUMPF (x,l) -> pn ("iffalse " ^ x ^ " goto " ^ string_of_int l)
    | T.LOAD (x,a) -> pn (x ^ " = " ^ s_arr a)
    | T.STORE (a,x) -> pn (s_arr a ^  " = " ^ x)
    | T.READ x -> pn ("read " ^ x)
    | T.WRITE x -> pn ("write " ^ x)
  ) b;
	List.iter (fun (b1,b2) -> 
	pn (string_of_int b1 ^ " -> " ^ string_of_int b2)
	) e

let pp_rda_inout : (blabel * blabel list) list -> unit
=fun lst ->
	let ps = print_string in
 		let pn = print_endline in
	List.iter (fun (bl,b) ->
		ps ("B" ^ string_of_int bl ^ " : {");
		List.iter (fun bl1 ->
			ps (string_of_int bl1 ^ ", ")
		) b;
		pn ("}")
	) lst

let print_lv_inout : (blabel * T.var list) list -> unit
=fun lst ->
	let ps = print_string in
  	let pn = print_endline in
	List.iter (fun (bl,b) ->
		ps ("B" ^ string_of_int bl ^ " : {");
		List.iter (fun v ->
		ps (v ^ ", ")
		) b;
		pn ("}")
	) lst

(*************************************)
(*           OPTIMIZATION            *)
(*************************************)

let rec get_edges : blocks -> blocks -> edges -> edges
=fun iter mem ret ->
	match iter with
	| (bl,(l,inst))::tl -> 
		let next_bl = get_next bl mem in
		begin match inst with
		| UJUMP l' -> 						(* goto handler *)
			let (bl',(l2,_)) = List.find (fun (bl1,(l1,_)) -> if l1 = l' then true else false) mem in
			get_edges tl mem (ret@[(bl,bl')])
		| CJUMP (_,l') | CJUMPF (_,l') ->
			let (bl',(l2,_)) = List.find (fun (bl1,(l1,_)) -> if l1 = l' then true else false) mem in
			if next_bl = bl' then get_edges tl mem (ret@[(bl,bl')]) 
			else get_edges tl mem (ret@[(bl,next_bl);(bl,bl')])
		| HALT -> ret
		| _->  get_edges tl mem (ret@[(bl,next_bl)])
		end
	| [] -> raise (Failure "exception")

and get_next : blabel -> blocks -> blabel
=fun bl bs ->
	let lst = List.rev_map (fun (l,linst) -> l) bs in 
	let l1 = List.filter (fun bl' -> if bl' > bl then true else false) lst in
	let l2 = List.sort compare l1 in
	if l2 = [] then -1 else List.hd l2

let defB : block -> T.var list
=fun (bl,(l,instr)) ->
	match instr with
	| ASSIGNV (x,o,y,z) -> [x] 
	| ASSIGNC (x,o,y,n) -> [x]
	| ASSIGNU (x,o,y) -> [x]
	| COPY (x,y) -> [x]     				
	| COPYC (x,n) -> [x]  				
	| LOAD (x,arr) -> [x]	        			
	| ALLOC (x,n) -> [x]							
	| STORE ((x,y),x') -> [x]
	| READ x -> [x]
	| _ -> []

let useB : block -> T.var list
=fun (bl,(l,instr)) ->
	match instr with
	| ASSIGNV (x,o,y,z) -> if y = z then [y] else [y;z] 
	| ASSIGNC (x,o,y,n) -> [y]
	| ASSIGNU (x,o,y) -> [y]
	| COPY (x,y) -> [y]     				
	| CJUMP (x,l) -> [x]
  	| CJUMPF (x,l) -> [x]
	| LOAD (x,(x',y)) -> [x';y]	        			
	| STORE ((x,y),x') -> if y = x' then [y] else [y;x']
  	| WRITE x -> [x]
	| _ -> []

let rec least_fix
=fun f equal (a,b) ->
	if equal (f a b) (a,b) then (a,b) else least_fix f equal (f a b)

module Rda = struct
	type t = (blabel,blabel list) PMap.t
	let lookup s t = try PMap.find s t with _ -> []
	let find_b
	= fun labellst mem -> 
		List.filter (fun (bl1,_) -> 
			if List.mem bl1 labellst then true else false 
		) mem
	let rec ef
	=fun (a,b) (a',b') ->
		let abool = try
		List.for_all2 (fun (bl1,lst1) (bl2,lst2) ->
			try List.for_all2 (fun bl3 bl4 ->
				if bl3 = bl4 then true else false
			) lst1 lst2
			with _ -> false
		) a a'
		with _ -> false
		in let bbool = try
		List.for_all2 (fun (bl1,lst1) (bl2,lst2) ->
			try List.for_all2 (fun bl3 bl4 ->
				if bl3 = bl4 then true else false
			) lst1 lst2
			with _ -> false
		) b b'
		with _ -> false in
		abool&&bbool
	let rec bigunion : edges -> t -> blabel list -> blabel list
	=fun prev outB lst ->
		match prev with
		| (p,bi)::tl -> 
			let outp = lookup p outB in
			let up_lst = List.sort_uniq compare (lst@outp) in
			bigunion tl outB up_lst
		| [] -> lst
	let new_set b = List.rev_map (fun (bl,linst) -> (bl,[])) b
	let rec compute_rda : cfg -> t * t			(*  in(B) * out(B) *)
	=fun (b,e) ->
		let inB = PMap.empty in
		let outB = PMap.empty in
		least_fix (update_set (b,e) b) ef (inB,outB)

	and update_set : cfg -> blocks -> t -> t -> t * t
	=fun (b,e) iter inB outB ->
		match iter with
		| (bl,linstr)::tl ->
			let up_inB = update_inB e bl inB outB in
			let up_outB = update_outB b (bl,linstr) up_inB outB  in
			update_set (b,e) tl up_inB up_outB
		| [] -> (inB,outB)
	and update_inB : edges -> blabel -> t -> t -> t
	=fun e bl inB outB ->
		let prev = List.filter (fun (bl1,bl2) -> if bl2 = bl then true else false) e in
		let inBi = bigunion prev outB [] in
		let inB' = PMap.remove bl inB
		PMap.add bl inBi inB'
	and update_outB : blocks -> block -> t -> t -> t
	=fun mem (bl,linstr) inB outB ->
		let inBi_labellst = lookup bl inB in
		let inBi = find_b inBi_labellst mem in
		let x = defB (bl,linstr) in
		let up_inBi = inBSUBkillB x inBi [] in
		let outBi = List.sort_uniq compare ([bl]@up_inBi) in
		let outB' = PMap.remove bl outB
		PMap.add bl outBi outB'
		(* (bl,outBi)::(List.remove_assoc bl outB) *)
	and inBSUBkillB : T.var list -> blocks -> blabel list -> blabel list
	=fun lst inBi ret ->
		match lst with
		| [a] -> begin
			match inBi with
			| (bl,linst)::tl ->
				let x = defB (bl,linst) in
				begin match x with
				| [y] -> if y = a then inBSUBkillB lst tl ret else inBSUBkillB lst tl (bl::ret)
				| [] -> inBSUBkillB lst tl (bl::ret)
				| _ -> raise (Failure "exception")
				end
			| [] -> ret
			end
		| [] -> List.rev_map (fun (lab,_) -> lab) inBi 
		| _ -> raise (Failure "exception")
end


module Lv = struct
	type t = (blabel, T.var list) PMap.t
	let lookup s t = try PMap.find s t with _ -> []
	let new_set b = List.rev_map (fun (bl,linst) -> (bl,[])) b
	let rec ef
	=fun (a,b) (a',b') ->
		let abool = try
		List.for_all2 (fun (bl1,lst1) (bl2,lst2) ->
			try List.for_all2 (fun v1 v2 ->
				if v1 = v2 then true else false
			) lst1 lst2
			with _ -> false
		) a a'
		with _ -> false
		in let bbool = try
		List.for_all2 (fun (bl1,lst1) (bl2,lst2) ->
			try List.for_all2 (fun v3 v4 ->
				if v3 = v4 then true else false
			) lst1 lst2
			with _ -> false
		) b b'
		with _ -> false in
		abool&&bbool
	let rec bigunion : edges -> t -> T.var list -> T.var list
	=fun succ inB lst ->
		match succ with
		| (bi,s)::tl -> 
			let ins = lookup s inB in
			let up_lst = List.sort_uniq compare (lst@ins) in
			bigunion tl inB up_lst
		| [] -> lst
	let rec compute_lv : cfg -> t * t
	=fun (b,e) ->
		let inB = PMap.empty in
		let outB = PMap.empty in
		least_fix (update_set b e) ef (inB,outB)
	and update_set : blocks -> edges -> t -> t -> t * t
	=fun b e inB outB ->
		match b with
		| (bl,linstr)::tl ->
			let up_inB = update_inB (bl,linstr) inB outB  in
			let up_outB = update_outB e bl up_inB outB in
			update_set tl e up_inB up_outB
		| [] -> (inB,outB)
	and update_inB : block -> t -> t -> t
	=fun (bl,linstr) inB outB ->
		let outBi = lookup bl outB in
		let x = defB (bl,linstr) in
		let up_outBi = 
			match x with
			| [d] -> List.filter (fun v -> if v = d then false else true) outBi
			| _ -> outBi in
		let inBi = List.sort_uniq compare (useB (bl,linstr))@up_outBi in
		let inB' = PMap.remove bl inB
		PMap.add bl inBi inB'
	and update_outB : edges -> blabel -> t -> t -> t
	=fun e bl inB outB ->
		let succ = List.filter (fun (bl1,bl2) -> if bl1 = bl then true else false) e in
		let outBi = bigunion succ inB [] in
		let outB' = PMap.remove bl outB
		PMap.add bl outBi outB'
end
 
let rec constant_prop : cfg -> cfg
=fun (bs,e) ->
	let (inB,_) = Rda.compute_rda (bs,e) in
	iter_for_blocks bs (bs,e) inB

and iter_for_blocks : blocks -> cfg -> Rda.t -> cfg
=fun iter g inB ->
	match iter with
	| (bl,linstr)::tl ->
		let uselst = useB (bl,linstr) in
		let g' = iter_for_uselst uselst bl g inB in
		let (b,e) = g' in
		let updated_iter = List.filter (fun (bl',linst) -> if bl' > bl then true else false) b in
		iter_for_blocks updated_iter g' inB 
	| [] -> g

(* and iter_for_uselst : T.var list -> blabel -> cfg -> Rda.t  -> cfg
=fun uselst bl g inB  ->
	let inBi_label = Rda.lookup bl inB in
	let inBi = Rda.find_b inBi_label inB in
	match uselst with
	| v::tl ->
		let doORnot = List.for_all (fun (_,(_,instr)) ->
			match instr with
			| T.ALLOC (x,n) -> if x = v then false else true
			| ASSIGNV (x,o,y,z) -> if x = v then false else true
			| ASSIGNC (x,o,y,n) -> if x = v then false else true
			| ASSIGNU (x,o,y) -> if x = v then false else true
			| COPY (x,y) -> if x = v then false else true   				
			| LOAD (x,(x',y)) -> if x = v then false else true         			
			| STORE ((x,y),x') -> if x = v then false else true
			| READ x -> if x = v then false else true
			| _ -> true
		) inBi in
		if not doORnot then iter_for_uselst tl bl g inB
		else
		let nlst = List.filter_map (fun (_,(_,instr)) ->
			match instr with
			| T.COPYC (x,n) -> if x = v then Some n else None
			| _ -> None
		) inBi in
 
		(* let _ = print_endline ("----iter for uselst----") in
		let _ = print_endline (string_of_int bl ^ " " ^ v ) in
		let _ = List.iter (fun a -> print_endline (string_of_int a ^ " ; ")) nlst in *)

		begin match nlst with
		| [n] ->
			let g' = do_const_prop g bl v n in
			iter_for_uselst tl bl g' inB 
		| n::tail -> if List.for_all (fun a -> if a = n then true else false) tail
			then let g' = do_const_prop g bl v n in
			iter_for_uselst tl bl g' inB 
			else iter_for_uselst tl bl g inB 
		| [] -> iter_for_uselst tl bl g inB
		end
	| [] -> g *)
	
and iter_for_uselst : T.var list -> blabel -> cfg -> Rda.t  -> cfg
=fun uselst bl g inB  ->
	let (mem,e) = g in
	let inBi_label = Rda.lookup bl inB in
	let inBi = Rda.find_b inBi_label mem in
	match uselst with
	| v::tl ->
		let defv = List.filter_map (fun (_,(_,inst)) ->	(* find v = exp *)
			match inst with
			| T.ALLOC (x,n) -> if x = v then Some inst else None
			| ASSIGNV (x,o,y,z) -> if x = v then Some inst else None
			| ASSIGNC (x,o,y,n) -> if x = v then Some inst else None
			| ASSIGNU (x,o,y) -> if x = v then Some inst else None
			| COPY (x,y) -> if x = v then Some inst else None 				
			| COPYC (x,n) -> if x = v then Some inst else None 				
			| LOAD (x,(x',y)) -> if x = v then Some inst else None       			
			| STORE ((x,y),x') -> if x = v then Some inst else None
			| READ x -> if x = v then Some inst else None
			| _ -> None
		) inBi in
		if List.for_all (fun inst -> match inst with | T.COPYC _ -> true | _ -> false) defv then 
		let n =
			begin match List.hd defv with 
			| COPYC (v,a) -> a
			| _ -> raise (Failure "exception")
			end in
		let g' = do_const_prop g bl v n in
		iter_for_uselst tl bl g' inB
		else iter_for_uselst tl bl g inB
	| [] -> g
 
and do_const_prop : cfg -> blabel -> T.var -> int -> cfg
=fun (bs,e) bl v c ->
	let (l,old) = try List.assoc bl bs with _ -> raise (Failure "exception") in
	let new_instr = 
		match old with
		| ASSIGNV (x,o,y,z) -> 
			if y = z then 
			let (NUM a) = T.eval_binary (NUM c) o (NUM c) in
			T.COPYC (x,a)
			else if z = v then ASSIGNC (x,o,y,c)
			else if y = v then
			begin match o with
			| ADD | MUL | EQ | AND | OR -> ASSIGNC (x,o,z,c)
			| LT -> ASSIGNC (x,GT,z,c)
			| LE -> ASSIGNC (x,GE,z,c)
			| GT -> ASSIGNC (x,LT,z,c)
			| GE  -> ASSIGNC (x,LE,z,c)
			| SUB | DIV -> old
			end
			else raise (Failure "exception")
		| ASSIGNC (x,o,y,n) ->
			let (NUM a) = T.eval_binary (NUM c) o (NUM n) in
			T.COPYC (x,a)
		| ASSIGNU (x,o,y) ->
			let (NUM a) = T.eval_unary o (NUM c) in
			T.COPYC (x,a)
		| COPY (x,y) -> COPYC (x,c)    				
		| _ -> old in
	let up_bs = List.rev (List.rev_map (fun (bl',(l,instr)) ->
		if bl' = bl then (bl,(l,new_instr)) else (bl',(l,instr))
		) bs) in
	(up_bs,e)

let rec copy_prop : cfg -> cfg
=fun (bs,e) ->
	let (inB,_) = Rda.compute_rda (bs,e) in
	cp_iter_for_blocks bs (bs,e) inB

and cp_iter_for_blocks : blocks -> cfg -> Rda.t -> cfg
=fun iter g inB ->
	match iter with
	| (bl,linstr)::tl ->
		let uselst = useB (bl,linstr) in
		let g' = cp_iter_for_uselst uselst bl g inB in
		let (b,e) = g' in
		let updated_iter = List.filter (fun (bl',linst) -> if bl' > bl then true else false) b in
		cp_iter_for_blocks updated_iter g' inB
		(* cp_iter_for_blocks tl g' inB *)
	| [] -> g

(* and cp_iter_for_uselst : T.var list -> blabel -> cfg -> Rda.t -> cfg
=fun uselst bl g inB ->
	match uselst with
	| v::tl -> 
		let doORnot = List.for_all (fun (_,(_,instr)) ->
			match instr with
			| T.ALLOC (x,n) -> if x = v then false else true
			| ASSIGNV (x,o,y,z) -> if x = v then false else true
			| ASSIGNC (x,o,y,n) -> if x = v then false else true
			| ASSIGNU (x,o,y) -> if x = v then false else true
			| COPYC (x,n) -> if x = v then false else true   				
			| LOAD (x,(x',y)) -> if x = v then false else true         			
			| STORE ((x,y),x') -> if x = v then false else true
			| READ x -> if x = v then false else true
			| _ -> true
		) inBi in
		if not doORnot then cp_iter_for_uselst tl bl g inBi
		else
		let dlst = List.filter_map (fun (_,(_,instr)) ->	(* v = d *)
			match instr with
			| T.COPY (x,d) -> if x = v then Some d else None
			| _ -> None
		) inBi in
 
		(* let _ = print_endline ("----iter for uselst----") in
		let _ = print_endline (string_of_int bl ^ " " ^ v ) in
		let _ = List.iter (fun a -> print_endline (string_of_int a ^ " ; ")) nlst in *)

		begin match dlst with
		| [d] ->
			let g' = do_copy_prop g bl v d in
			iter_for_uselst tl bl g' inBi
		| d::tail -> if List.for_all (fun a -> if a = d then true else false) tail
			then let g' = do_copy_prop g bl v d in
			iter_for_uselst tl bl g' inBi
			else iter_for_uselst tl bl g inBi
		| [] -> iter_for_uselst tl bl g inBi
		end
	| [] -> g *)

and cp_iter_for_uselst : T.var list -> blabel -> cfg -> Rda.t -> cfg
=fun uselst bl g inB ->
	let (mem,e) = g in
	let inBi_label = Rda.lookup bl inB in
	let inBi = Rda.find_b inBi_label mem in
	match uselst with
	| v::tl -> 
		let defv = List.filter_map (fun (_,(_,instr)) ->	(* find v = exp *)
			match instr with
			| T.ALLOC (x,n) -> if x = v then Some instr else None
			| ASSIGNV (x,o,y,z) -> if x = v then Some instr else None
			| ASSIGNC (x,o,y,n) -> if x = v then Some instr else None
			| ASSIGNU (x,o,y) -> if x = v then Some instr else None
			| COPY (x,y) -> if x = v then Some instr else None 				
			| COPYC (x,n) -> if x = v then Some instr else None 				
			| LOAD (x,(x',y)) -> if x = v then Some instr else None       			
			| STORE ((x,y),x') -> if x = v then Some instr else None
			| READ x -> if x = v then Some instr else None
			| _ -> None
		) inBi in
		let head = List.hd defv in
		if List.for_all (fun instr -> 
			if instr = head then
			begin match instr with
			| ASSIGNV (x,o,y,z) -> (if x = y || x = z then false else true)
			| ASSIGNC (x,o,y,n) -> (if x = y then false else true)
			| ASSIGNU (x,o,y) -> (if x = y then false else true)
			| _ -> true end
			else false) defv then 
			let g' = do_copy_prop g bl v head in
			cp_iter_for_uselst tl bl g' inB
		else
			cp_iter_for_uselst tl bl g inB
	| [] -> g
 
and do_copy_prop : cfg -> blabel -> T.var -> T.instr -> cfg	
=fun (bs,e) bl v exp ->
	let (l,old) = try List.assoc bl bs with _ -> raise (Failure "exception") in
	match exp with
	| COPY (v,d) ->					(* v = d *)
		let new_instr = 
			begin match old with
			| ASSIGNV (x,o,y,z) -> 
				if y = z && y = v then T.ASSIGNV (x,o,d,d)
				else if y = v then ASSIGNV (x,o,d,z)
				else if z = v then ASSIGNV (x,o,y,d)
				else raise (Failure "exception")
			| ASSIGNC (x,o,y,n) -> ASSIGNC (x,o,d,n)
			| ASSIGNU (x,o,y) -> ASSIGNU (x,o,d)
			| COPY (x,y) -> COPY (x,d)  
			| CJUMP (x,label) -> CJUMP (d,label)
			| CJUMPF (x,label) -> CJUMPF (d,label)
			| LOAD (x,(a,i)) -> if i = v then LOAD (x,(a,d)) else old
			| STORE ((a,i),x) ->
				if i = v && x = v then STORE ((a,d),d)
				else if x = v then STORE ((a,i),d)
				else if i = v then STORE ((a,d),x)
				else old	
			| WRITE x -> WRITE d
			| _ -> old
			end in
		let up_bs = List.rev (List.rev_map (fun (bl',(l,instr)) ->
			if bl' = bl then (bl,(l,new_instr)) else (bl',(l,instr))
			) bs ) in
		(up_bs,e)
	| _ -> do_copy_exp (bs,e) bl v exp old

and do_copy_exp : cfg -> blabel -> T.var -> T.instr -> T.instr -> cfg	
=fun (bs,e) bl v exp old ->
	let new_instr = 
		match old with
		| COPY (x,v') ->				(* x = v *)			(* exp : v = ~~~~ *)
			begin match exp with
			| T.ASSIGNV (ev,o,y,z) -> if ev != y && ev != z then T.ASSIGNV (x,o,y,z) else old
			| ASSIGNC (ev,o,y,n) -> if ev != y then ASSIGNC (x,o,y,n) else old
			| ASSIGNU (ev,o,y) -> if ev != y then ASSIGNU (x,o,y) else old		
			| LOAD (ev,arr) -> LOAD (x,arr)										
			| _ -> old
			end
		| _ -> old in
	let up_bs = List.rev (List.rev_map (fun (bl',(l,instr)) ->
		if bl' = bl then (bl,(l,new_instr)) else (bl',(l,instr))
		)bs) in
	(up_bs,e)

let rec deadcode_elimination : cfg -> cfg
=fun (bs,e) ->
	dc_iter_for_blocks bs (bs,e)

and dc_iter_for_blocks : blocks -> cfg -> cfg
=fun iter (bs,e) ->
	match iter with
	| (bl,b)::tl ->
		let defbi = defB (bl,b) in
		if defbi = [] then dc_iter_for_blocks tl (bs,e)
		else
		let (inB,outB) = Lv.compute_lv (bs,e) in
		let outbi = Lv.lookup bl outB in
		if List.mem (List.hd defbi) outbi then dc_iter_for_blocks tl (bs,e)
		else
		let up_bs = List.filter (fun (bl',_) -> if bl' = bl then false else true) bs in
		let up_e = get_edges up_bs up_bs [] in
		dc_iter_for_blocks tl (up_bs,up_e)
	| [] -> (bs,e)

let optimize : T.program -> T.program
=fun t -> 
	let t2b = List.map (fun linstr -> (new_b_label(),linstr)) t in 
	let e = get_edges t2b t2b [] in
	(* let cfg = (([(0,(-1,T.SKIP))]@t2b),([(0,1)]@e)) in *)
	let cfg = (t2b,e) in
	(* let (inB,outB) = Rda.compute_rda cfg in *)
	(* let (inB,outB) = Lv.compute_lv cfg in *)
	(* let const_cfg = constant_prop cfg in *)
	(* let const_cfg2 = constant_prop const_cfg in *)
	(* let cfg3 = deadcode_elimination const_cfg2 in *)
	(* let res = copy_prop cfg in *)
	(* let cfg2 = constant_prop cfg in *)
	let cfg3 = constant_prop cfg in
	let cfg4 = deadcode_elimination cfg3 in
	let cfg5 = copy_prop cfg4 in
	let cfg6 = deadcode_elimination cfg5 in

	let (resultb,_) = cfg6 in

	let b2t = List.map (fun (bl,linstr) -> linstr) resultb in

	(* print_endline ("Before optimization");
	pp cfg; *)
	(* print_endline ("++++++++++++++++optimization");
	pp cfg4;
	print_endline ("++++++++++++++++optimization");
	pp cfg5; *)
	
	(* print_endline ("----print in set----");
	pp_rda_inout inB;
	print_endline ("----print out set----");
	pp_rda_inout outB; *) 
	(* print_endline ("After constant propagation 1st");
	pp cfg2; *)
	(* print_endline ("After constant propagation 2nd");
	pp cfg3; *)
	(* print_endline ("After constant propagation 2nd -> deadcode");
	pp cfg4;
	print_endline ("After const prop 2nd -> deadcode -> copy prop");
	pp cfg5; *)
	b2t

(* let optimize : T.program -> T.program
=fun t -> t *)