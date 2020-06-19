type token =
  | NEWLINE
  | LPAREN
  | RPAREN
  | PLUS
  | MINUS
  | MULTIPLY
  | DIVIDE
  | NUM of (int)

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.expr
