{
  module L = Lexing

  type token = [%import: Parser.token] [@@deriving show]

  let illegal_character loc char =
    Error.error loc "illegal character '%c'" char
}

let spaces = [' ' '\t']+
let digit = ['0'-'9']
let integer = digit+
let id = ['A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

rule token = parse
  | spaces            { token lexbuf }
  | '\n'              { L.new_line lexbuf; token lexbuf }
  | integer as lxm    { LITINT (int_of_string lxm) }
  | '+'               { PLUS }
  | "int"             { INT }
  | "bool"            { BOOL}
  | "let"             { LET }
  | "in"              { IN }
  | "if"              { IF }
  | "then"            { THEN }
  | "else"            { ELSE }
  | id as name        { ID name }
  | '<'               { LT }
  | '('               { LPAREN }
  | ')'               { RPAREN }
  | ','               { COMMA }
  | '='               { EQ }
  | eof               { EOF }
  | _                 { illegal_character (Location.curr_loc lexbuf) (L.lexeme_char lexbuf 0) }
