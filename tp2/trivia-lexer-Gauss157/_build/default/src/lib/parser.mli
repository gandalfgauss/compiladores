
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
  | ID of (string)
  | EQ
  | EOF
  | ELSE
  | COMMA
  | BOOL
