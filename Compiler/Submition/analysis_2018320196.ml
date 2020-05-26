type var = string
type aexp = 
  | Int of int
  | Var of var
  | Plus of aexp * aexp
  | Mult of aexp * aexp 
  | Minus of aexp * aexp 
 
type bexp = 
  | True 
  | False
  | Eq of aexp * aexp 
  | Le of aexp * aexp 
  | Neg of bexp 
  | Conj of bexp * bexp 

type cmd = 
  | Assign of var * aexp 
  | Skip
  | Seq of cmd * cmd
  | If of bexp * cmd * cmd
  | While of bexp * cmd 

exception Invalid_State

(* x:=1; y:=2; a:=x+y; b:=x-y *) 
let test1 = 
  Seq (Assign ("x", Int 1), 
    Seq (Assign ("y", Int 2), 
      Seq (Assign ("a", Plus  (Var "x", Var "y")), 
           Assign ("b", Minus (Var "x", Var "a")))))


(* x:=10; y:=2; while (x!=1) do (y:=y*x; x:=x-1) *)
let test2 = 
  Seq (Assign ("x", Int 10), 
    Seq (Assign("y", Int 2), 
         While (Neg (Eq (Var "x", Int 1)),
                Seq(Assign("y", Mult(Var "y", Var "x")), 
                    Assign("x", Minus(Var "x", Int 1))))))

(* a:=10; b:=2; q:=0; r:=a; while (b<=r) { r:=r-b; q:=q+1 } *)
let test3 = 
  Seq (Assign ("a", Int 10), 
    Seq (Assign ("b", Int 2), 
      Seq (Assign ("q", Int 0), 
        Seq (Assign ("r", Var "a"), 
           While (Le (Var "b", Var "r"),
                Seq(Assign("r", Minus(Var "r", Var "b")), 
                    Assign("q", Plus(Var "q", Int 1))))))))

module ABool = struct
  type t = Bot | Top | TT | FF
  let alpha b = if b then TT else FF

  (* partial order *)
  let order : t -> t -> bool 
  =fun b1 b2 -> 
    match b1,b2 with
    | Bot,_| TT,TT | TT,Top | FF,FF | FF,Top | Top,Top -> true
    | _,_ -> false

  (* least upper bound *)
  let lub : t -> t -> t 
  =fun b1 b2 -> 
    match b1,b2 with
    | Bot,_ -> b2
    | _,Bot -> b1
    | Top,_ -> Top
    | _,Top -> Top
    | TT,TT -> TT
    | TT,FF -> Top
    | FF,TT -> Top
    | FF,FF -> FF

  (* abstract negation *)
  let neg : t -> t 
  =fun b -> 
    match b with
    | TT -> FF
    | FF -> TT
    | _ -> b

  (* abstract conjunction *)
  let conj : t -> t -> t
  =fun b1 b2 -> 
    if b1 = Bot || b2 = Bot then Bot
    else if b1 = FF || b2 = FF then FF
    else if b1 = TT && b2 = TT then TT
    else Top

end

module AValue = struct
  type t = Bot | Top | Neg | Zero | Pos | NonPos | NonZero | NonNeg
  let alpha : int -> t 
  =fun n -> if n = 0 then Zero else if n > 0 then Pos else Neg
  let to_string s = 
    match s with 
    | Bot -> "Bot" 
    | Top -> "Top" 
    | Pos -> "Pos" 
    | Neg -> "Neg" 
    | Zero -> "Zero"
    | NonNeg -> "NonNeg"
    | NonZero -> "NonZero"
    | NonPos -> "NonPos"

  (* partial order *)
  let order : t -> t -> bool
  =fun s1 s2 -> 
    if s1 = s2 then true else
    match s1,s2 with
    | Bot,_
    | Neg,NonPos | Neg,Top | Neg,NonZero 
    | Zero,NonPos | Zero,NonNeg | Zero,Top
    | Pos,NonZero | Pos,NonNeg | Pos,Top
    | NonPos,Top | NonZero,Top | NonNeg,Top -> true
    | _,_ -> false

  (* least upper bound *)
  let lub : t -> t -> t 
  =fun s1 s2 -> 
    if s1 = s2 then s1 else
    match s1,s2 with
    | Bot,_ -> s2
    | _,Bot -> s1
    | Neg,Zero | Zero,Neg -> NonPos
    | Neg,Pos | Pos,Neg -> NonZero
    | Neg,NonPos | NonPos,Neg -> NonPos
    | Neg,NonZero | NonZero,Neg -> NonZero
    | Neg,NonNeg | NonNeg,Neg -> Top
    | Zero,Pos | Pos,Zero -> NonNeg
    | Zero,NonPos | NonPos,Zero -> NonPos
    | Zero,NonZero | NonZero,Zero -> Top
    | Zero,NonNeg | NonNeg,Zero -> NonNeg
    | Pos,NonPos | NonPos,Pos -> Top
    | Pos,NonZero | NonZero,Pos -> NonZero
    | Pos,NonNeg | NonNeg,Pos -> NonNeg
    | _,_ -> Top

  (* abstract addition *)
  let plus : t -> t -> t 
  =fun a1 a2 -> 
    if a1 = Bot || a2 = Bot then Bot
    else if a1 = Top || a2 = Top then Top
    else
    match a1,a2 with
    | Neg,Neg -> Neg
    | Neg,Zero | Zero,Neg -> Neg
    | Neg,Pos | Pos,Neg -> Top
    | Neg,NonPos | NonPos,Neg -> Neg
    | Neg,NonZero | NonZero,Neg -> Top
    | Neg,NonNeg | NonNeg,Neg -> Top
    | Zero,Zero -> Zero
    | Zero,Pos | Pos,Zero -> Pos
    | Zero,NonPos | NonPos,Zero -> NonPos
    | Zero,NonZero | NonZero,Zero -> NonZero
    | Zero,NonNeg | NonNeg,Zero -> NonNeg
    | Pos,Pos -> Pos
    | Pos,NonPos | NonPos,Pos -> Top
    | Pos,NonZero | NonZero,Pos -> Top
    | Pos,NonNeg | NonNeg,Pos -> Pos
    | NonPos,NonPos -> NonPos
    | NonNeg,NonNeg -> NonNeg
    | _,_ -> Top
     
  (* abstract multiplication *)
  let mult : t -> t -> t 
  =fun a1 a2 ->
    if a1 = Bot || a2 = Bot then Bot
    else if a1 = Top || a2 = Top then Top
    else if a1 = Zero || a2 = Zero then Zero
    else
    match a1,a2 with
    | Neg,Neg -> Pos
    | Neg,Pos | Pos,Neg -> Neg 
    | Neg,NonPos | NonPos,Neg -> NonNeg 
    | Neg,NonZero | NonZero,Neg -> NonZero 
    | Neg,NonNeg | NonNeg,Neg -> NonPos
    | Pos,Pos -> Pos 
    | Pos,NonPos | NonPos,Pos -> NonPos 
    | Pos,NonZero | NonZero,Pos -> NonZero 
    | Pos,NonNeg | NonNeg,Pos -> NonNeg
    | NonPos,NonPos -> NonNeg 
    | NonPos,NonZero | NonZero,NonPos -> Top
    | NonPos,NonNeg | NonNeg,NonPos -> NonPos
    | NonZero,NonZero -> NonZero
    | NonZero,NonNeg | NonNeg,NonZero -> Top
    | NonNeg,NonNeg -> NonNeg
    | _,_ -> raise Invalid_State 

  (* abstract subtraction *)
  let minus : t -> t -> t
  =fun a1 a2 -> 
    if a1 = Bot || a2 = Bot then Bot
    else if a1 = Top || a2 = Top then Top
    else if a2 = Zero then a1
    else
    match a1,a2 with
    | Neg,Pos -> Neg
    | Neg,NonNeg -> Neg
    | Zero,Neg -> Pos
    | Zero,Pos -> Neg
    | Zero,NonPos -> NonNeg
    | Zero,NonZero -> NonZero
    | Zero,NonNeg -> NonPos
    | Pos,Neg -> Pos
    | Pos,NonPos -> Pos
    | NonPos,Pos -> Neg
    | NonPos,NonNeg -> NonPos
    | NonNeg,Neg -> Pos
    | NonNeg,NonPos -> NonNeg
    | _,_ -> Top
    
  let eq : t -> t -> ABool.t 
  =fun a1 a2 -> 
    if a1 = Bot || a2 = Bot then ABool.Bot
    else if a1 = Top || a2 = Top then ABool.Top
    else
    match a1,a2 with
    | Zero,Zero -> ABool.TT
    | Neg,Zero | Zero,Neg
    | Neg,Pos | Pos,Neg
    | Neg,NonNeg | NonNeg,Neg
    | Zero,Pos | Pos,Zero
    | Zero,NonZero | NonZero,Zero
    | Pos,NonPos | NonPos,Pos -> ABool.FF
    | _,_ -> ABool.Top

  let le : t -> t -> ABool.t 
  =fun a1 a2 -> 
    if a1 = Bot || a2 = Bot then ABool.Bot
    else if a1 = Top || a2 = Top then ABool.Top
    else if a1 = NonZero || a2 = NonZero then ABool.Top
    else
    match a1,a2 with
    | Neg,Zero | Neg,Pos | Neg,NonNeg
    | Zero,Zero | Zero,Pos | Zero,NonNeg
    | NonPos,Zero | NonPos,Pos | NonPos,NonNeg -> ABool.TT
    | Zero,Neg | Pos,Neg | Pos,Zero | Pos,NonPos | NonNeg,Neg -> ABool.FF
    | _,_ -> ABool.Top

end

module AState = struct
  module Map = Map.Make(struct type t = var let compare = compare end)
  type t = AValue.t Map.t (* var -> AValue.t map *)
  let bot = Map.empty
  let find x m = try Map.find x m with Not_found -> AValue.Bot
  let update x v m = Map.add x v m
  let update_join x v m = Map.add x (AValue.lub v (find x m)) m
  let order m1 m2 = Map.for_all (fun k v -> AValue.order v (find k m2)) m1
  let lub m1 m2 = Map.fold (fun k v m -> update_join k v m) m1 m2
  let print m = 
    Map.iter (fun k v -> 
   print_endline (k ^ " |-> " ^ AValue.to_string v)) m 
end

let rec aeval : aexp -> AState.t -> AValue.t
=fun a s ->
  match a with
  | Int n -> AValue.alpha n 
  | Var x -> AState.find x s 
  | Plus (a1, a2) -> AValue.plus (aeval a1 s) (aeval a2 s)
  | Mult (a1, a2) -> AValue.mult (aeval a1 s) (aeval a2 s)
  | Minus (a1, a2) -> AValue.minus (aeval a1 s) (aeval a2 s)

let rec beval : bexp -> AState.t -> ABool.t
=fun b s -> 
  match b with
  | True -> ABool.alpha true
  | False -> ABool.alpha false
  | Eq (a1, a2) -> AValue.eq (aeval a1 s) (aeval a2 s)
  | Le (a1, a2) -> AValue.le (aeval a1 s) (aeval a2 s)
  | Neg b -> ABool.neg (beval b s)
  | Conj (b1, b2) -> ABool.conj (beval b1 s) (beval b2 s)

let rec ceval : cmd -> AState.t -> AState.t
=fun c s -> 
  match c with
  | Assign (x, a) -> AState.update x (aeval a s) s
  | Skip -> s
  | Seq (c1,c2) -> ceval c2 (ceval c1 s)
  | If (b, c1, c2) -> 
      if beval b s = ABool.TT then (ceval c1 s)
      else if beval b s = ABool.FF then (ceval c2 s)
      else if beval b s = ABool.Bot then AState.bot
      else AState.lub (ceval c1 s) (ceval c2 s)

  | While (_, c) -> fix (ceval c) s

and fix f s0 = if AState.order (f s0) s0 then s0 else fix f (f s0)

let run : cmd -> AState.t
=fun c -> ceval c AState.bot

let _ = AState.print (run test1); prerr_endline "";
AState.print (run test2); prerr_endline "";
AState.print (run test3)
