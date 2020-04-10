open Regex
open Hw1

let testcases : (Regex.t * alphabet list) list = 
  [ 
    (Empty, []);
    (Epsilon, []);
    (Alpha A, [A]);
    (Alpha A, [B]);
    (OR (Alpha A, Alpha B), [B]);  (*   (A + B)    *)
    (CONCAT (STAR (Alpha A), Alpha B), [B]);   (*  A*B   *)
    (CONCAT (STAR (Alpha A), Alpha B), [A;B]);  
    (CONCAT (STAR (Alpha A), Alpha B), [A;A;B]);
    (CONCAT (STAR (Alpha A), Alpha B), [A;B;B]);
    (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B), [B]);    (* (AA)*(BB)*B  *)
    (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B), [A;A;B]);
    (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B), [B;B;B]);
    (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B), [A;A;A;A;B;B;B]);
    (CONCAT (CONCAT (STAR (CONCAT (Alpha A, Alpha A)), STAR (CONCAT (Alpha B, Alpha B))), Alpha B), [A;A;A;B;B;B]);

    (CONCAT (Alpha A, CONCAT (Alpha B, STAR (Alpha A))), [A;B;A]) ;
    (CONCAT (Alpha A, CONCAT (Alpha B, STAR (Alpha A))), [A;A]) ;

    (CONCAT (Alpha B, CONCAT(OR (Alpha A, Alpha B), Alpha A)), [B;A;A]);
    (CONCAT (Alpha B, CONCAT(OR (Alpha A, Alpha B), Alpha A)) ,[B;B;A;B]);

    (CONCAT ( CONCAT (CONCAT (STAR (Alpha A),Alpha B),STAR (Alpha B)), OR (CONCAT (Alpha A, Alpha B),CONCAT (Alpha B, Alpha A))), [A;A;B;B;B;A;B]);
    (CONCAT ( CONCAT (CONCAT (STAR (Alpha A),Alpha B),STAR (Alpha B)), OR (CONCAT (Alpha A, Alpha B),CONCAT (Alpha B, Alpha A))) ,[A;A;B;A]);

    (CONCAT (STAR (OR (Alpha A, Alpha B)),Alpha A), [A;B;B;B;A;A]);           
    (CONCAT (STAR (OR (Alpha A, Alpha B)),Alpha A), [B;B;B;B;A;A;B]);          
    (CONCAT (Alpha A,STAR (OR(Alpha A,Alpha B))), [A;B;A;B;A;A;A;A;A;A;B;A]);            
    (CONCAT (Alpha A,STAR (OR(Alpha A,Alpha B))), [B;B;A;A]);                 
    (CONCAT (Alpha A, CONCAT (Alpha B, CONCAT (STAR (CONCAT (Alpha A, CONCAT (Alpha A, Alpha B))), CONCAT (Alpha B, Alpha A)))), [A;B;B;A]);  
    (CONCAT (Alpha A, CONCAT (Alpha B, CONCAT (STAR (CONCAT (Alpha A, CONCAT (Alpha A, Alpha B))), CONCAT (Alpha B, Alpha A)))), [A;B;A;A;B;A;B;B;A]);

    (CONCAT (STAR (OR (Alpha A, Alpha B)), Alpha A), [A;B;B;B;A;A]);
    (CONCAT (STAR (OR (Alpha A, Alpha B)), Alpha A), [A;B;B;B;A;B]);
    (STAR (CONCAT (Alpha A, STAR (Alpha B))), [A;B;B;B;A;A;B]);
    (STAR (CONCAT (Alpha A, STAR (Alpha B))), [B;A;B;B;B;A;A;B]);
    (STAR (CONCAT (OR (Alpha A, CONCAT (Alpha B, Alpha A)), Alpha B)), []);
    (STAR (CONCAT (OR (Alpha A, CONCAT (Alpha B, Alpha A)), Alpha B)), [B;A;B;A;B]);
    (STAR (CONCAT (OR (Alpha A, CONCAT (Alpha B, Alpha A)), Alpha B)), [A;B;B;A;A]);
    (OR (CONCAT (OR (Alpha A, Epsilon), Alpha B), STAR(CONCAT (Alpha B, Alpha B))), [A;B]);
    (OR (CONCAT (OR (Alpha A, Epsilon), Alpha B), STAR(CONCAT (Alpha B, Alpha B))), [A;A;B;A]);
    (CONCAT (STAR (CONCAT (Alpha B, OR (STAR (Alpha A), Alpha B))), OR (CONCAT (Alpha B, STAR (Alpha A)), STAR (Alpha B))), [B;A;A;B;A;B;B;B;A]);
    (CONCAT (STAR (CONCAT (Alpha B, OR (STAR (Alpha A), Alpha B))), OR (CONCAT (Alpha B, STAR (Alpha A)), STAR (Alpha B))), [A;B;B;A;B;A;A])
  ]

let match_regex : Regex.t -> alphabet list -> bool
=fun regex input -> Hw1.run_dfa (Hw1.regex2dfa regex) input

(* run testcases *)
let _ = 
  List.iter (fun (regex, str) -> 
    prerr_endline (string_of_bool (match_regex regex str)) 
  ) testcases
