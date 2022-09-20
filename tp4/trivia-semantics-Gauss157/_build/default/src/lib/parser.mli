
(* The type of tokens. *)

type token = 
  | THEN
  | RPAREN
  | PLUS
  | LT
  | LPAREN
  | LITINT of (int)
  | LET
  | INT
  | IN
  | IF
  | ID of (Symbol.symbol)
  | EQ
  | EOF
  | ELSE
  | COMMA
  | BOOL

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val program: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Absyn.lprogram)
