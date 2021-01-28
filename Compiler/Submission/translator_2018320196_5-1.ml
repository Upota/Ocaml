let tidx = ref 0
let new_tmp() = tidx := !tidx + 1; ".t" ^ (string_of_int (!tidx))
let label = ref 1
let new_label() = label := !label + 1; !label

let rec trans_e : S.exp -> T.var * T.program
=fun e -> 
	match e with
	| NUM n ->
		let t = new_tmp() in
		let code = [(T.dummy_label, T.COPYC (t,n))] in
		(t,code)
	| LV v ->
		begin match v with
		| ID id ->
			let t = new_tmp() in
			let code = [(T.dummy_label, T.COPY (t,id))] in
			(t,code)
		| ARR (id,e1) ->
			let (t1,code) = trans_e e1 in
			let t2 = new_tmp() in
			let arr = (id,t1) in
			(t2,code@[(T.dummy_label, T.LOAD (t2,arr))])
		end
  | ADD (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.ADD,t1,t2))] in
		(t3,code)
  | SUB (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.SUB,t1,t2))] in
		(t3,code)
  | MUL (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.MUL,t1,t2))] in
		(t3,code)
  | DIV (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.DIV,t1,t2))] in
		(t3,code)
  | MINUS e1 ->
		let (t1,code1) = trans_e e1 in
		let t2 = new_tmp() in
		let code = code1@[(T.dummy_label, T.ASSIGNU (t2,T.MINUS,t1))] in
		(t2,code)
  | NOT e1 ->
		let (t1,code1) = trans_e e1 in
		let t2 = new_tmp() in
		let code = code1@[(T.dummy_label, T.ASSIGNU (t2,T.NOT,t1))] in
		(t2,code)
  | LT (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.LT,t1,t2))] in
		(t3,code)
  | LE (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.LE,t1,t2))] in
		(t3,code)
  | GT (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.GT,t1,t2))] in
		(t3,code)
  | GE (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.GE,t1,t2))] in
		(t3,code)
  | EQ (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.EQ,t1,t2))] in
		(t3,code)
  | AND (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.AND,t1,t2))] in
		(t3,code)
  | OR (e1,e2) ->
		let (t1,code1) = trans_e e1 in
		let (t2,code2) = trans_e e2 in
		let t3 = new_tmp() in
		let code = code1@code2@[(T.dummy_label, T.ASSIGNV (t3,T.OR,t1,t2))] in
		(t3,code)

let rec trans_s : S.stmt -> T.program
=fun s ->
	match s with
	| ASSIGN (v,e2) ->
		begin match v with
		| ID id ->
			let (t1,code1) = trans_e e2 in
			code1@[(T.dummy_label, T.COPY (id,t1))]
		| ARR (id,e1) ->
			let (t1,code1) = trans_e e1 in
			let (t2,code2) = trans_e e2 in
			let arr = (id,t1) in
			code1@code2@[(T.dummy_label, T.STORE (arr,t2))]
		end
  | IF (e,s1,s2) ->
		let (t1,code1) = trans_e e in 
		let code_t = trans_s s1 in 
		let code_f = trans_s s2 in 
		let lt = new_label() in
		let lf = new_label() in
		let lx = new_label() in
		code1@[(T.dummy_label, T.CJUMP (t1,lt))]@[(T.dummy_label, T.UJUMP lf)]@[(lt,T.SKIP)]@code_t@[(T.dummy_label, T.UJUMP lx)]@[(lf,T.SKIP)]@code_f@[(T.dummy_label, T.UJUMP lx)]@[(lx,T.SKIP)]
  | WHILE (e,s1) ->
		let (t1,code1) = trans_e e in 
		let code_b = trans_s s1 in
		let le = new_label() in 
		let lx = new_label() in 
		[(le,T.SKIP)]@code1@[(T.dummy_label,T.CJUMPF (t1,lx))]@code_b@[(T.dummy_label, T.UJUMP le)]@[(lx,T.SKIP)]
  | DOWHILE (s1,e) ->
		(trans_s s1)@(trans_s (S.WHILE (e,s1)))
  | READ id -> [(T.dummy_label,T.READ id)]
  | PRINT e ->
		let (t1,code1) = trans_e e in
		code1@[(T.dummy_label, T.WRITE t1)]
  | BLOCK b -> trans_b b

and trans_d : S.decl -> T.program
=fun decl ->
	match decl with
	| (S.TINT,id) -> [(T.dummy_label, T.COPYC (id,0))]
	| (S.TARR n,id) -> [(T.dummy_label, T.ALLOC (id,n))]

and trans_b : S.block -> T.program
=fun (decls,stmts) ->
	match decls with
	| hd::tl -> 
		let d1 = trans_d hd in 
		d1@(trans_b (tl,stmts))
	| [] ->	begin
		match stmts with
		| hd::tl -> 
		let s1 = trans_s hd in
		s1@(trans_b ([],tl))
		| [] -> []
		end

let translate : S.program -> T.program
=fun s -> (trans_b s)@[(T.dummy_label,T.HALT)]