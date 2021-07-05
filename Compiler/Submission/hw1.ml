open Regex

exception Not_implemented

let rec regex2nfa : Regex.t -> Nfa.t 
=fun regex -> 
  let nfa1 = Nfa.create_new_nfa () in
  let (fs,nfa2) = eval_reg2n regex (Nfa.get_initial_state nfa1, nfa1) in
  let nfa = Nfa.add_final_state nfa2 fs in
  nfa

and eval_reg2n : Regex.t -> (Nfa.state * Nfa.t) -> (Nfa.state * Nfa.t)
=fun regex (s,nfa) -> 
  match regex with
  | Empty -> Nfa.create_state nfa
  | Epsilon -> 
    let (s1,nfa1) = Nfa.create_state nfa in  
    let nfa2 = (s1, Nfa.add_epsilon_edge nfa1 (s,s1)) in
    nfa2
  | Alpha a ->
    let (s1,nfa1) = Nfa.create_state nfa in
    let nfa2 = (s1, Nfa.add_edge nfa1 (s,a,s1)) in
    nfa2
  | OR (r1,r2) ->
    let nfa1 = eval_reg2n Epsilon (s,nfa) in
    let nfa2 = eval_reg2n Epsilon (s,nfa) in

    (* eval r1, r2 *)
    let nfa_r1 = eval_reg2n r1 nfa1 in
    let (s1,nfa_r2) = eval_reg2n r2 nfa2 in

    let (pos,nfa1_r1) = eval_reg2n Epsilon nfa_r1 in

    (* for union states and edges *)
    let states_r2 = Nfa.get_states nfa_r2 in
    let edges_r2 = Nfa.get_edges nfa_r2 in

    let nfa3 = Nfa.add_edges (Nfa.add_states nfa1_r1 states_r2) edges_r2 in
    let nfa4 = Nfa.add_epsilon_edge nfa3 (s1,pos) in
    (pos,nfa4)
  | CONCAT (r1,r2) ->
    let nfa_r1 = eval_reg2n r1 (s,nfa) in
    let nfa1 = eval_reg2n Epsilon nfa_r1 in
    let nfa2 = eval_reg2n r2 nfa1 in
    nfa2
  | STAR r ->
    let (s1,nfa1) = Nfa.create_state nfa in
    let nfa2 = Nfa.add_epsilon_edge nfa1 (s,s1) in
    let (s2,nfa3) = eval_reg2n r (s1,nfa2) in
    let nfa4 = Nfa.add_epsilon_edge nfa3 (s2,s1) in
    let (s3,nfa5) = Nfa.create_state nfa4 in
    let nfa6 = Nfa.add_epsilon_edge (Nfa.add_epsilon_edge nfa5 (s,s3)) (s2,s3) in
    (s3,nfa6)

let rec nfa2dfa : Nfa.t -> Dfa.t
=fun nfa -> 
  let d0 = fix (e_closure nfa) (BatSet.singleton (Nfa.get_initial_state nfa)) in
  let dfa1 = Dfa.create_new_dfa d0 in
  let dfa2 = fs_check nfa dfa1 d0 in
  let dfa = eval_n2d nfa (BatSet.singleton d0) (BatSet.singleton d0) dfa2 in
  dfa

and eval_n2d : Nfa.t -> Dfa.states -> Dfa.states -> Dfa.t -> Dfa.t
=fun nfa d w dfa ->
  if BatSet.is_empty w then dfa
  else
  let (ds,w') = BatSet.pop w in
  let a_clo = fix (e_closure nfa) (closure nfa A ds) in
  let dfa1 = fs_check nfa (Dfa.add_edge (Dfa.add_state dfa a_clo) (ds, A, a_clo)) a_clo in
  
  let b_clo = fix (e_closure nfa) (closure nfa B ds) in
  let dfa2 = fs_check nfa (Dfa.add_edge (Dfa.add_state dfa1 b_clo) (ds, B, b_clo)) b_clo in
  
  let (up_d,up_w) = update_dw (update_dw (d,w') a_clo) b_clo in
  eval_n2d nfa up_d up_w dfa2

and fix : (Dfa.state -> Dfa.state) -> Dfa.state -> Dfa.state
=fun f a ->
  if BatSet.equal (f a) a then a else fix f (f a)

and update_dw : (Dfa.states * Dfa.states) -> Dfa.state -> (Dfa.states * Dfa.states)
=fun (d,w) q ->
  if BatSet.is_empty q then (d,w)
  else (if BatSet.mem q d then (d,w) else (BatSet.add q d, BatSet.add q w))

and e_closure : Nfa.t -> Dfa.state -> Dfa.state
=fun nfa ds ->
  if BatSet.is_empty ds then ds
  else
  let (s,a) = BatSet.pop ds in
  let tmp = BatSet.add s (Nfa.get_next_state_epsilon nfa s) in
  BatSet.union tmp (e_closure nfa a)

and closure : Nfa.t -> Regex.alphabet -> Dfa.state -> Dfa.state
=fun nfa x ds ->
  if BatSet.is_empty ds then ds
  else
  let (s,a) = BatSet.pop ds in
  let tmp = Nfa.get_next_state nfa s x in
  BatSet.union tmp (closure nfa x a)

and fs_check : Nfa.t -> Dfa.t -> Dfa.state -> Dfa.t
=fun nfa dfa s ->
  let fs = Nfa.get_final_states nfa in
  if BatSet.is_empty (BatSet.intersect s fs) then dfa
  else Dfa.add_final_state dfa s

(* Do not modify this function *)
let regex2dfa : Regex.t -> Dfa.t
=fun regex -> 
  let nfa = regex2nfa regex in
  let dfa = nfa2dfa nfa in
    dfa

let rec run_dfa : Dfa.t -> alphabet list -> bool
=fun dfa str -> Dfa.is_final_state dfa (List.fold_left (fun s x -> 
if BatSet.is_empty s then BatSet.empty else Dfa.get_next_state dfa s x) (Dfa.get_initial_state dfa) str)
