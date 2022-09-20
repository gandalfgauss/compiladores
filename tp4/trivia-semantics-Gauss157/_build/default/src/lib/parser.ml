
module MenhirBasics = struct
  
  exception Error
  
  let _eRR =
    fun _s ->
      raise Error
  
  type token = 
    | THEN
    | RPAREN
    | PLUS
    | LT
    | LPAREN
    | LITINT of (
# 4 "src/lib/parser.mly"
       (int)
# 20 "src/lib/parser.ml"
  )
    | LET
    | INT
    | IN
    | IF
    | ID of (
# 5 "src/lib/parser.mly"
       (Symbol.symbol)
# 29 "src/lib/parser.ml"
  )
    | EQ
    | EOF
    | ELSE
    | COMMA
    | BOOL
  
end

include MenhirBasics

type ('s, 'r) _menhir_state = 
  | MenhirState00 : ('s, _menhir_box_program) _menhir_state
    (** State 00.
        Stack shape : .
        Start symbol: program. *)

  | MenhirState01 : (('s, _menhir_box_program) _menhir_cell1_INT, _menhir_box_program) _menhir_state
    (** State 01.
        Stack shape : INT.
        Start symbol: program. *)

  | MenhirState04 : (('s, _menhir_box_program) _menhir_cell1_BOOL, _menhir_box_program) _menhir_state
    (** State 04.
        Stack shape : BOOL.
        Start symbol: program. *)

  | MenhirState07 : (('s, _menhir_box_program) _menhir_cell1_typeid, _menhir_box_program) _menhir_state
    (** State 07.
        Stack shape : typeid.
        Start symbol: program. *)

  | MenhirState10 : ((('s, _menhir_box_program) _menhir_cell1_typeid, _menhir_box_program) _menhir_cell1_typeids _menhir_cell0_RPAREN, _menhir_box_program) _menhir_state
    (** State 10.
        Stack shape : typeid typeids RPAREN.
        Start symbol: program. *)

  | MenhirState14 : (('s, _menhir_box_program) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_program) _menhir_state
    (** State 14.
        Stack shape : LET ID.
        Start symbol: program. *)

  | MenhirState15 : (('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_state
    (** State 15.
        Stack shape : IF.
        Start symbol: program. *)

  | MenhirState17 : (('s, _menhir_box_program) _menhir_cell1_ID, _menhir_box_program) _menhir_state
    (** State 17.
        Stack shape : ID.
        Start symbol: program. *)

  | MenhirState22 : (('s, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 22.
        Stack shape : exp.
        Start symbol: program. *)

  | MenhirState24 : (('s, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 24.
        Stack shape : exp.
        Start symbol: program. *)

  | MenhirState26 : (('s, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 26.
        Stack shape : exp.
        Start symbol: program. *)

  | MenhirState29 : ((('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 29.
        Stack shape : IF exp.
        Start symbol: program. *)

  | MenhirState31 : (((('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 31.
        Stack shape : IF exp exp.
        Start symbol: program. *)

  | MenhirState34 : ((('s, _menhir_box_program) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 34.
        Stack shape : LET ID exp.
        Start symbol: program. *)

  | MenhirState38 : (('s, _menhir_box_program) _menhir_cell1_typeid, _menhir_box_program) _menhir_state
    (** State 38.
        Stack shape : typeid.
        Start symbol: program. *)

  | MenhirState45 : (('s, _menhir_box_program) _menhir_cell1_fundec, _menhir_box_program) _menhir_state
    (** State 45.
        Stack shape : fundec.
        Start symbol: program. *)


and ('s, 'r) _menhir_cell1_exp = 
  | MenhirCell1_exp of 's * ('s, 'r) _menhir_state * (Absyn.lexp) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_fundec = 
  | MenhirCell1_fundec of 's * ('s, 'r) _menhir_state * (Absyn.lfundec) * Lexing.position

and ('s, 'r) _menhir_cell1_typeid = 
  | MenhirCell1_typeid of 's * ('s, 'r) _menhir_state * (Absyn.typeid) * Lexing.position

and ('s, 'r) _menhir_cell1_typeids = 
  | MenhirCell1_typeids of 's * ('s, 'r) _menhir_state * (Absyn.typeid list)

and ('s, 'r) _menhir_cell1_BOOL = 
  | MenhirCell1_BOOL of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_ID = 
  | MenhirCell1_ID of 's * ('s, 'r) _menhir_state * (
# 5 "src/lib/parser.mly"
       (Symbol.symbol)
# 142 "src/lib/parser.ml"
) * Lexing.position * Lexing.position

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 5 "src/lib/parser.mly"
       (Symbol.symbol)
# 149 "src/lib/parser.ml"
) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_INT = 
  | MenhirCell1_INT of 's * ('s, 'r) _menhir_state * Lexing.position

and ('s, 'r) _menhir_cell1_LET = 
  | MenhirCell1_LET of 's * ('s, 'r) _menhir_state * Lexing.position

and 's _menhir_cell0_RPAREN = 
  | MenhirCell0_RPAREN of 's * Lexing.position

and _menhir_box_program = 
  | MenhirBox_program of (Absyn.lprogram) [@@unboxed]

let _menhir_action_01 =
  fun _endpos_x_ _startpos_x_ x ->
    let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 32 "src/lib/parser.mly"
           ( _loc, Absyn.IntExp x )
# 175 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_02 =
  fun _endpos_x_ _startpos_x_ x ->
    let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 33 "src/lib/parser.mly"
       ( _loc, Absyn.VarExp x )
# 186 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_03 =
  fun _endpos_y_ _startpos_x_ x y ->
    let op = 
# 40 "src/lib/parser.mly"
       ( Absyn.Plus )
# 194 "src/lib/parser.ml"
     in
    let _endpos = _endpos_y_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 34 "src/lib/parser.mly"
                          ( _loc, Absyn.OpExp (op, x, y) )
# 202 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_04 =
  fun _endpos_y_ _startpos_x_ x y ->
    let op = 
# 41 "src/lib/parser.mly"
     ( Absyn.LT )
# 210 "src/lib/parser.ml"
     in
    let _endpos = _endpos_y_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 34 "src/lib/parser.mly"
                          ( _loc, Absyn.OpExp (op, x, y) )
# 218 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_05 =
  fun _endpos_y_ _startpos__1_ t x y ->
    let _endpos = _endpos_y_ in
    let _startpos = _startpos__1_ in
    let _loc = (_startpos, _endpos) in
    (
# 35 "src/lib/parser.mly"
                                 ( _loc, Absyn.IfExp (t, x, y) )
# 229 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_06 =
  fun _endpos__4_ _startpos_f_ a f ->
    let _endpos = _endpos__4_ in
    let _startpos = _startpos_f_ in
    let _loc = (_startpos, _endpos) in
    (
# 36 "src/lib/parser.mly"
                            ( _loc, Absyn.CallExp (f, a) )
# 240 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_07 =
  fun _endpos_b_ _startpos__1_ b i x ->
    let _endpos = _endpos_b_ in
    let _startpos = _startpos__1_ in
    let _loc = (_startpos, _endpos) in
    (
# 37 "src/lib/parser.mly"
                             ( _loc, Absyn.LetExp (x, i, b) )
# 251 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_08 =
  fun x ->
    (
# 60 "src/lib/parser.mly"
                                        ( x )
# 259 "src/lib/parser.ml"
     : (Absyn.lexp list))

let _menhir_action_09 =
  fun _endpos_b_ _startpos_x_ b p x ->
    let _endpos = _endpos_b_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 47 "src/lib/parser.mly"
                                            ( _loc, (x, p, b) )
# 270 "src/lib/parser.ml"
     : (Absyn.lfundec))

let _menhir_action_10 =
  fun l ->
    (
# 44 "src/lib/parser.mly"
                          ( l )
# 278 "src/lib/parser.ml"
     : (Absyn.lfundec list))

let _menhir_action_11 =
  fun x ->
    (
# 218 "<standard.mly>"
    ( [ x ] )
# 286 "src/lib/parser.ml"
     : (Absyn.lfundec list))

let _menhir_action_12 =
  fun x xs ->
    (
# 220 "<standard.mly>"
    ( x :: xs )
# 294 "src/lib/parser.ml"
     : (Absyn.lfundec list))

let _menhir_action_13 =
  fun _endpos__2_ _startpos_l_ l ->
    let _endpos = _endpos__2_ in
    let _startpos = _startpos_l_ in
    let _loc = (_startpos, _endpos) in
    (
# 29 "src/lib/parser.mly"
                ( _loc, Absyn.Program l )
# 305 "src/lib/parser.ml"
     : (Absyn.lprogram))

let _menhir_action_14 =
  fun x ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 313 "src/lib/parser.ml"
     : (Absyn.lexp list))

let _menhir_action_15 =
  fun x xs ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 321 "src/lib/parser.ml"
     : (Absyn.lexp list))

let _menhir_action_16 =
  fun x ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 329 "src/lib/parser.ml"
     : (Absyn.typeid list))

let _menhir_action_17 =
  fun x xs ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 337 "src/lib/parser.ml"
     : (Absyn.typeid list))

let _menhir_action_18 =
  fun _endpos_x_ _startpos_x_ x ->
    let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 50 "src/lib/parser.mly"
       ( _loc, x )
# 348 "src/lib/parser.ml"
     : (Absyn.lsymbol))

let _menhir_action_19 =
  fun x ->
    (
# 53 "src/lib/parser.mly"
               ( (Absyn.Int, x) )
# 356 "src/lib/parser.ml"
     : (Absyn.typeid))

let _menhir_action_20 =
  fun x ->
    (
# 54 "src/lib/parser.mly"
                ( (Absyn.Bool, x) )
# 364 "src/lib/parser.ml"
     : (Absyn.typeid))

let _menhir_action_21 =
  fun x ->
    (
# 57 "src/lib/parser.mly"
                                           ( x )
# 372 "src/lib/parser.ml"
     : (Absyn.typeid list))

let _menhir_print_token : token -> string =
  fun _tok ->
    match _tok with
    | BOOL ->
        "BOOL"
    | COMMA ->
        "COMMA"
    | ELSE ->
        "ELSE"
    | EOF ->
        "EOF"
    | EQ ->
        "EQ"
    | ID _ ->
        "ID"
    | IF ->
        "IF"
    | IN ->
        "IN"
    | INT ->
        "INT"
    | LET ->
        "LET"
    | LITINT _ ->
        "LITINT"
    | LPAREN ->
        "LPAREN"
    | LT ->
        "LT"
    | PLUS ->
        "PLUS"
    | RPAREN ->
        "RPAREN"
    | THEN ->
        "THEN"

let _menhir_fail : unit -> 'a =
  fun () ->
    Printf.eprintf "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

include struct
  
  [@@@ocaml.warning "-4-37-39"]
  
  let rec _menhir_run_42_spec_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _startpos _v ->
      let _v =
        let l = _v in
        _menhir_action_10 l
      in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let (_startpos_l_, l, _endpos__2_) = (_startpos, _v, _endpos) in
      let _v = _menhir_action_13 _endpos__2_ _startpos_l_ l in
      MenhirBox_program _v
  
  let rec _menhir_goto_nonempty_list_fundec_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _startpos _v _menhir_s ->
      match _menhir_s with
      | MenhirState45 ->
          _menhir_run_46 _menhir_stack _menhir_lexbuf _v
      | MenhirState00 ->
          _menhir_run_42_spec_00 _menhir_stack _menhir_lexbuf _startpos _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_46 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_fundec -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _v ->
      let MenhirCell1_fundec (_menhir_stack, _menhir_s, x, _startpos_x_) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_12 x xs in
      _menhir_goto_nonempty_list_fundec_ _menhir_stack _menhir_lexbuf _startpos_x_ _v _menhir_s
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v =
            let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos_0, _v) in
            _menhir_action_18 _endpos_x_ _startpos_x_ x
          in
          let (x, _startpos__1_) = (_v, _startpos) in
          let _v = _menhir_action_19 x in
          _menhir_goto_typeid _menhir_stack _menhir_lexbuf _menhir_lexer _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_typeid : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState38 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState07 ->
          _menhir_run_37 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState45 ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState00 ->
          _menhir_run_06 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_37 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_typeid (_menhir_stack, _menhir_s, _v, _startpos) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
          | BOOL ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState38
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_16 x in
          _menhir_goto_separated_nonempty_list_COMMA_typeid_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_04 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let _v =
            let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos_0, _v) in
            _menhir_action_18 _endpos_x_ _startpos_x_ x
          in
          let (x, _startpos__1_) = (_v, _startpos) in
          let _v = _menhir_action_20 x in
          _menhir_goto_typeid _menhir_stack _menhir_lexbuf _menhir_lexer _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_typeid_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState07 ->
          _menhir_run_40_spec_07 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState38 ->
          _menhir_run_39 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_40_spec_07 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_typeid -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _v =
        let x = _v in
        _menhir_action_21 x
      in
      let _menhir_stack = MenhirCell1_typeids (_menhir_stack, MenhirState07, _v) in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _menhir_stack = MenhirCell0_RPAREN (_menhir_stack, _endpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | EQ ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LITINT _v_0 ->
              let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
              let _endpos_1 = _menhir_lexbuf.Lexing.lex_curr_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_endpos_x_, _startpos_x_, x) = (_endpos_1, _startpos, _v_0) in
              let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
              _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState10 _tok
          | LET ->
              _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
          | IF ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState10
          | ID _v_3 ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState10
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_36 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_typeid, _menhir_box_program) _menhir_cell1_typeids _menhir_cell0_RPAREN as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BOOL | EOF | INT ->
          let MenhirCell0_RPAREN (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_typeids (_menhir_stack, _, p) = _menhir_stack in
          let MenhirCell1_typeid (_menhir_stack, _menhir_s, x, _startpos_x_) = _menhir_stack in
          let (_endpos_b_, b) = (_endpos, _v) in
          let _v = _menhir_action_09 _endpos_b_ _startpos_x_ b p x in
          let _startpos = _startpos_x_ in
          (match (_tok : MenhirBasics.token) with
          | INT ->
              let _menhir_stack = MenhirCell1_fundec (_menhir_stack, _menhir_s, _v, _startpos) in
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState45
          | BOOL ->
              let _menhir_stack = MenhirCell1_fundec (_menhir_stack, _menhir_s, _v, _startpos) in
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState45
          | EOF ->
              let (_startpos_x_, x) = (_startpos, _v) in
              let _v = _menhir_action_11 x in
              _menhir_goto_nonempty_list_fundec_ _menhir_stack _menhir_lexbuf _startpos_x_ _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_run_22 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_exp -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LITINT _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _v _tok
      | LET ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState22
      | IF ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState22
      | ID _v ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState22
      | _ ->
          _eRR ()
  
  and _menhir_run_23 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_exp -> _ -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_exp (_menhir_stack, _menhir_s, x, _startpos_x_, _) = _menhir_stack in
      let (_endpos_y_, y) = (_endpos, _v) in
      let _v = _menhir_action_03 _endpos_y_ _startpos_x_ x y in
      _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_y_ _startpos_x_ _v _menhir_s _tok
  
  and _menhir_goto_exp : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState10 ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState34 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState14 ->
          _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState31 ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState29 ->
          _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState15 ->
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState24 ->
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState22 ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState26 ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState17 ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_35 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_program) _menhir_cell1_exp as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BOOL | COMMA | ELSE | EOF | IN | INT | RPAREN | THEN ->
          let MenhirCell1_exp (_menhir_stack, _, i, _, _) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, x, _, _) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_b_, b) = (_endpos, _v) in
          let _v = _menhir_action_07 _endpos_b_ _startpos__1_ b i x in
          _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_b_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_24 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_exp -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LITINT _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
          _menhir_run_25 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState24 _tok
      | LET ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
      | IF ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState24
      | ID _v ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState24
      | _ ->
          _eRR ()
  
  and _menhir_run_25 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_exp as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BOOL | COMMA | ELSE | EOF | IN | INT | RPAREN | THEN ->
          let MenhirCell1_exp (_menhir_stack, _menhir_s, x, _startpos_x_, _) = _menhir_stack in
          let (_endpos_y_, y) = (_endpos, _v) in
          let _v = _menhir_action_04 _endpos_y_ _startpos_x_ x y in
          _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_y_ _startpos_x_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_12 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_LET (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _menhir_stack = MenhirCell0_ID (_menhir_stack, _v, _startpos_0, _endpos) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | EQ ->
              let _tok = _menhir_lexer _menhir_lexbuf in
              (match (_tok : MenhirBasics.token) with
              | LITINT _v_1 ->
                  let _startpos_2 = _menhir_lexbuf.Lexing.lex_start_p in
                  let _endpos_3 = _menhir_lexbuf.Lexing.lex_curr_p in
                  let _tok = _menhir_lexer _menhir_lexbuf in
                  let (_endpos_x_, _startpos_x_, x) = (_endpos_3, _startpos_2, _v_1) in
                  let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
                  _menhir_run_33 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState14 _tok
              | LET ->
                  _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
              | IF ->
                  _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
              | ID _v_5 ->
                  _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState14
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_33 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_LET _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LITINT _v_0 ->
              let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
              let _endpos_2 = _menhir_lexbuf.Lexing.lex_curr_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_endpos_x_, _startpos_x_, x) = (_endpos_2, _startpos_1, _v_0) in
              let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
              _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState34 _tok
          | LET ->
              _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState34
          | IF ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState34
          | ID _v_4 ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState34
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_15 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _menhir_stack = MenhirCell1_IF (_menhir_stack, _menhir_s, _startpos) in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LITINT _v ->
          let _startpos_0 = _menhir_lexbuf.Lexing.lex_start_p in
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos_0, _v) in
          let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
          _menhir_run_28 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState15 _tok
      | LET ->
          _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | IF ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState15
      | ID _v ->
          _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState15
      | _ ->
          _eRR ()
  
  and _menhir_run_28 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | THEN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LITINT _v_0 ->
              let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
              let _endpos_2 = _menhir_lexbuf.Lexing.lex_curr_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_endpos_x_, _startpos_x_, x) = (_endpos_2, _startpos_1, _v_0) in
              let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
              _menhir_run_30 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState29 _tok
          | LET ->
              _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState29
          | IF ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState29
          | ID _v_4 ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState29
          | _ ->
              _eRR ())
      | PLUS ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_30 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_exp as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LITINT _v_0 ->
              let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
              let _endpos_2 = _menhir_lexbuf.Lexing.lex_curr_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_endpos_x_, _startpos_x_, x) = (_endpos_2, _startpos_1, _v_0) in
              let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
              _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState31 _tok
          | LET ->
              _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState31
          | IF ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState31
          | ID _v_4 ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState31
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_32 : type  ttv_stack. ((((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_cell1_exp as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BOOL | COMMA | ELSE | EOF | IN | INT | RPAREN | THEN ->
          let MenhirCell1_exp (_menhir_stack, _, x, _, _) = _menhir_stack in
          let MenhirCell1_exp (_menhir_stack, _, t, _, _) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_y_, y) = (_endpos, _v) in
          let _v = _menhir_action_05 _endpos_y_ _startpos__1_ t x y in
          _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_y_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_16 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _menhir_stack = MenhirCell1_ID (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LITINT _v_0 ->
              let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
              let _endpos_2 = _menhir_lexbuf.Lexing.lex_curr_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_endpos_x_, _startpos_x_, x) = (_endpos_2, _startpos_1, _v_0) in
              let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState17 _tok
          | LET ->
              _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
          | IF ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState17
          | ID _v_4 ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState17
          | _ ->
              _eRR ())
      | BOOL | COMMA | ELSE | EOF | IN | INT | LT | PLUS | RPAREN | THEN ->
          let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_02 _endpos_x_ _startpos_x_ x in
          _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_21 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer
      | COMMA ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LITINT _v_0 ->
              let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
              let _endpos_2 = _menhir_lexbuf.Lexing.lex_curr_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_endpos_x_, _startpos_x_, x) = (_endpos_2, _startpos_1, _v_0) in
              let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
              _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState26 _tok
          | LET ->
              _menhir_run_12 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState26
          | IF ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState26
          | ID _v_4 ->
              _menhir_run_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState26
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_14 x in
          _menhir_goto_separated_nonempty_list_COMMA_exp_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_exp_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState26 ->
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState17 ->
          _menhir_run_18_spec_17 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_27 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_exp -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_exp (_menhir_stack, _menhir_s, x, _, _) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_15 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_exp_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_18_spec_17 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_ID -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _v =
        let x = _v in
        _menhir_action_08 x
      in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_ID (_menhir_stack, _menhir_s, f, _startpos_f_, _) = _menhir_stack in
      let (_endpos__4_, a) = (_endpos, _v) in
      let _v = _menhir_action_06 _endpos__4_ _startpos_f_ a f in
      _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__4_ _startpos_f_ _v _menhir_s _tok
  
  and _menhir_run_39 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_typeid -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_typeid (_menhir_stack, _menhir_s, x, _) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_17 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_typeid_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_06 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typeid (_menhir_stack, _menhir_s, _v, _startpos) in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
          | BOOL ->
              _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState07
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  let rec _menhir_run_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | INT ->
          _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | BOOL ->
          _menhir_run_04 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | _ ->
          _eRR ()
  
end

let program =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_program v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
