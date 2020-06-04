type token =
  | NUM of (int)
  | ID of (string)
  | INT
  | PLUS
  | MINUS
  | STAR
  | SLASH
  | EQUAL
  | EQUALEQUAL
  | LE
  | LT
  | GE
  | GT
  | NOT
  | AND
  | OR
  | IF
  | ELSE
  | WHILE
  | DO
  | READ
  | PRINT
  | SEMICOLON
  | LBRACE
  | RBRACE
  | LBLOCK
  | RBLOCK
  | LPAREN
  | RPAREN
  | EOF

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> S.program
