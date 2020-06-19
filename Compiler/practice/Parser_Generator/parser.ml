type token =
  | NEWLINE
  | LPAREN
  | RPAREN
  | PLUS
  | MINUS
  | MULTIPLY
  | DIVIDE
  | NUM of (int)

open Parsing;;
let _ = parse_error;;
# 2 "parser.mly"
# 15 "parser.ml"
let yytransl_const = [|
  257 (* NEWLINE *);
  258 (* LPAREN *);
  259 (* RPAREN *);
  260 (* PLUS *);
  261 (* MINUS *);
  262 (* MULTIPLY *);
  263 (* DIVIDE *);
    0|]

let yytransl_block = [|
  264 (* NUM *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\002\000\002\000\002\000\002\000\002\000\000\000"

let yylen = "\002\000\
\002\000\001\000\003\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\002\000\008\000\000\000\000\000\001\000\
\000\000\000\000\000\000\000\000\007\000\000\000\000\000\000\000\
\000\000"

let yydgoto = "\002\000\
\005\000\006\000"

let yysindex = "\011\000\
\003\255\000\000\003\255\000\000\000\000\009\255\020\255\000\000\
\003\255\003\255\003\255\003\255\000\000\033\255\038\255\011\255\
\253\254"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\032\255\027\255\016\255\
\040\255"

let yygindex = "\000\000\
\000\000\253\255"

let yytablesize = 45
let yytable = "\007\000\
\009\000\010\000\011\000\012\000\003\000\014\000\015\000\016\000\
\017\000\008\000\004\000\001\000\009\000\010\000\011\000\012\000\
\005\000\012\000\005\000\005\000\005\000\005\000\013\000\009\000\
\010\000\011\000\012\000\004\000\000\000\004\000\004\000\004\000\
\003\000\000\000\003\000\003\000\000\000\010\000\011\000\012\000\
\006\000\000\000\006\000\011\000\012\000"

let yycheck = "\003\000\
\004\001\005\001\006\001\007\001\002\001\009\000\010\000\011\000\
\012\000\001\001\008\001\001\000\004\001\005\001\006\001\007\001\
\001\001\007\001\003\001\004\001\005\001\006\001\003\001\004\001\
\005\001\006\001\007\001\001\001\255\255\003\001\004\001\005\001\
\001\001\255\255\003\001\004\001\255\255\005\001\006\001\007\001\
\001\001\255\255\003\001\006\001\007\001"

let yynames_const = "\
  NEWLINE\000\
  LPAREN\000\
  RPAREN\000\
  PLUS\000\
  MINUS\000\
  MULTIPLY\000\
  DIVIDE\000\
  "

let yynames_block = "\
  NUM\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 16 "parser.mly"
                      ( _1 )
# 95 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 18 "parser.mly"
         ( Ast.Num (_1) )
# 102 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 19 "parser.mly"
               ( Ast.Add (_1,_3) )
# 110 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 20 "parser.mly"
                ( Ast.Minus (_1,_3) )
# 118 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 21 "parser.mly"
                   ( Ast.Mul (_1,_3) )
# 126 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exp) in
    Obj.repr(
# 22 "parser.mly"
                 ( Ast.Div (_1,_3) )
# 134 "parser.ml"
               : 'exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'exp) in
    Obj.repr(
# 23 "parser.mly"
                    ( _2 )
# 141 "parser.ml"
               : 'exp))
(* Entry program *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let program (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.expr)
