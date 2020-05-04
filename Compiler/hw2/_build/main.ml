open Parse

let cfg1 = (
  [N "E"; N "E'"; N "T"; N "T'"; N "F"], 
  [T "+"; T "*"; T "("; T ")"; T "id"], 
  N "E",
  [
    (N "E", [N "T"; N "E'"]);
    (N "E'", [T "+"; N "T"; N "E'"]);
    (N "E'", []);
    (N "T", [N "F"; N "T'"]);
    (N "T'", [T "*"; N "F"; N "T'"]);
    (N "T'", []);
    (N "F", [T "("; N "E"; T ")"]);
    (N "F", [T "id"])
  ])

let cfg2 = (
  [N "S"; N "E"; N "E'"; N "T"; N "T'"; N "F"],
  [T "+"; T "-"; T "*"; T "/"; T "id"; T "num"; T "("; T ")"],
  N "S",
  [
      (N "S", [N "E"]);
      (N "E", [N "T"; N "E'"]);
      (N "E'", [T "+"; N "T"; N "E'"]);
      (N "E'", [T "-"; N "T"; N "E'"]);
      (N "E'", []);
      (N "T", [N "F"; N "T'"]);
      (N "T'", [T "*"; N "F"; N "T'"]);
      (N "T'", [T "/"; N "F"; N "T'"]);
      (N "T'", []);
      (N "F", [T "id"]);
      (N "F", [T "num"]);
      (N "F", [T "("; N "E" ;T ")"]);
  ]
)

let cfg3 = (
  [N "X"; N "Y"; N "Z"],
  [T "a"; T"c"; T"d"], 
  N "X", 
  [
    (N "X", [N "Y"]);
    (N "X", [T "a"]);
    (N "Y", [T "c"]);
    (N "Y", []);
    (N "Z", [T "d"]);
    (N "Z", [N "X"; N "Y"; N "Z"])
  ]
)

let cfg4 = (
  [N "S"; N "S'"; N "E"],
  [T "a"; T "b"; T "e"; T "i"; T "t"],
  N "S",
  [
   (N "S", [T "i"; N "E"; T "t"; N "S"; N "S'"]);
   (N "S", [T "a"]);
   (N "S'", [T "e"; N "S"]);
   (N "S'", []);
   (N "E", [T "b"])
  ] 
)

let cfg5 = (
  [N "E"; N "T"; N "F"], 
  [T "+"; T "*"; T "("; T ")"; T "id"], 
  N "E",
  [
    (N "E", [N "E"; T "+"; N "T"]);
    (N "E", [N "T"]);
    (N "T", [N "T"; T "*"; N "F"]);
    (N "T", [N "F"]);
    (N "F", [T "id"]);
    (N "F", [T "("; N "E"; T ")"]) (* False *)
  ])

let s1 = [T "id"; T "+"; T "id"; T "*"; T "id"; End]
let s2 = [T "id"; T "/"; T "("; T "num"; T "+"; T "id"; T ")"; End]
let s3 = [T "id"; T "*"; T "("; T ")"; T "id"; End] (* id * () id  cfg1 False *)
let s4 = [T "id"; T "-"; T "("; T "num";T ")"; T "id"; End] (* id - (num) id cfg2 False *)
let s5 = [T "id"; T "-"; T "("; T "num";T ")"; T "+"; T "id"; End] (* id - (num) + id  cfg2 True *)

let cfgs = [cfg1; cfg2; cfg3; cfg4; cfg5]
let main () =
  List.iter (fun cfg ->
    print_endline (string_of_bool (check_LL1 cfg))
  ) cfgs;
  print_endline "";
  print_endline (string_of_bool (parse cfg1 s1));
  print_endline (string_of_bool (parse cfg1 s2));
  print_endline (string_of_bool (parse cfg2 s1));
  print_endline (string_of_bool (parse cfg2 s2));
  print_endline (string_of_bool (parse cfg1 s3));
  print_endline (string_of_bool (parse cfg2 s4));
  print_endline (string_of_bool (parse cfg2 s5))

let _ = main ()
