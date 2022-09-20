
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

  | MenhirState06 : (('s, _menhir_box_program) _menhir_cell1_typeid, _menhir_box_program) _menhir_state
    (** State 06.
        Stack shape : typeid.
        Start symbol: program. *)

  | MenhirState09 : ((('s, _menhir_box_program) _menhir_cell1_typeid, _menhir_box_program) _menhir_cell1_typeids _menhir_cell0_RPAREN, _menhir_box_program) _menhir_state
    (** State 09.
        Stack shape : typeid typeids RPAREN.
        Start symbol: program. *)

  | MenhirState13 : (('s, _menhir_box_program) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_program) _menhir_state
    (** State 13.
        Stack shape : LET ID.
        Start symbol: program. *)

  | MenhirState14 : (('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_state
    (** State 14.
        Stack shape : IF.
        Start symbol: program. *)

  | MenhirState16 : (('s, _menhir_box_program) _menhir_cell1_ID, _menhir_box_program) _menhir_state
    (** State 16.
        Stack shape : ID.
        Start symbol: program. *)

  | MenhirState21 : (('s, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 21.
        Stack shape : exp.
        Start symbol: program. *)

  | MenhirState23 : (('s, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 23.
        Stack shape : exp.
        Start symbol: program. *)

  | MenhirState25 : (('s, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 25.
        Stack shape : exp.
        Start symbol: program. *)

  | MenhirState28 : ((('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 28.
        Stack shape : IF exp.
        Start symbol: program. *)

  | MenhirState30 : (((('s, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 30.
        Stack shape : IF exp exp.
        Start symbol: program. *)

  | MenhirState33 : ((('s, _menhir_box_program) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_state
    (** State 33.
        Stack shape : LET ID exp.
        Start symbol: program. *)

  | MenhirState37 : (('s, _menhir_box_program) _menhir_cell1_typeid, _menhir_box_program) _menhir_state
    (** State 37.
        Stack shape : typeid.
        Start symbol: program. *)

  | MenhirState45 : (('s, _menhir_box_program) _menhir_cell1_fundec, _menhir_box_program) _menhir_state
    (** State 45.
        Stack shape : fundec.
        Start symbol: program. *)


and ('s, 'r) _menhir_cell1_exp = 
  | MenhirCell1_exp of 's * ('s, 'r) _menhir_state * (Absyn.lexp) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_fundec = 
  | MenhirCell1_fundec of 's * ('s, 'r) _menhir_state * (Absyn.lfundec) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_typeid = 
  | MenhirCell1_typeid of 's * ('s, 'r) _menhir_state * (Absyn.typeid) * Lexing.position

and ('s, 'r) _menhir_cell1_typeids = 
  | MenhirCell1_typeids of 's * ('s, 'r) _menhir_state * (Absyn.typeid list)

and ('s, 'r) _menhir_cell1_ID = 
  | MenhirCell1_ID of 's * ('s, 'r) _menhir_state * (
# 5 "src/lib/parser.mly"
       (Symbol.symbol)
# 129 "src/lib/parser.ml"
) * Lexing.position * Lexing.position

and 's _menhir_cell0_ID = 
  | MenhirCell0_ID of 's * (
# 5 "src/lib/parser.mly"
       (Symbol.symbol)
# 136 "src/lib/parser.ml"
) * Lexing.position * Lexing.position

and ('s, 'r) _menhir_cell1_IF = 
  | MenhirCell1_IF of 's * ('s, 'r) _menhir_state * Lexing.position

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
                                 ( _loc , Absyn.IntExp x           )
# 159 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_02 =
  fun _endpos_y_ _startpos_x_ x y ->
    let op = 
# 43 "src/lib/parser.mly"
       ( Absyn.Plus )
# 167 "src/lib/parser.ml"
     in
    let _endpos = _endpos_y_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 33 "src/lib/parser.mly"
                                 ( _loc , Absyn.OpExp (op, x, y)   )
# 175 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_03 =
  fun _endpos_y_ _startpos_x_ x y ->
    let op = 
# 44 "src/lib/parser.mly"
       ( Absyn.LT )
# 183 "src/lib/parser.ml"
     in
    let _endpos = _endpos_y_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 33 "src/lib/parser.mly"
                                 ( _loc , Absyn.OpExp (op, x, y)   )
# 191 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_04 =
  fun _endpos_x_ _startpos_x_ x ->
    let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 34 "src/lib/parser.mly"
                                 ( _loc , Absyn.VarExp x            )
# 202 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_05 =
  fun _endpos_z_ _startpos__1_ x y z ->
    let _endpos = _endpos_z_ in
    let _startpos = _startpos__1_ in
    let _loc = (_startpos, _endpos) in
    (
# 35 "src/lib/parser.mly"
                                 ( _loc , Absyn.IfExp (x, y, z)    )
# 213 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_06 =
  fun _endpos__4_ _startpos_x_ f x ->
    let _endpos = _endpos__4_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 36 "src/lib/parser.mly"
                                 ( _loc , Absyn.CallExp (x, f)     )
# 224 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_07 =
  fun _endpos_ff_ _startpos__1_ f ff i ->
    let _endpos = _endpos_ff_ in
    let _startpos = _startpos__1_ in
    let _loc = (_startpos, _endpos) in
    (
# 37 "src/lib/parser.mly"
                                 ( _loc , Absyn.LetExp (i, f, ff) )
# 235 "src/lib/parser.ml"
     : (Absyn.lexp))

let _menhir_action_08 =
  fun x ->
    (
# 40 "src/lib/parser.mly"
                                        ( x )
# 243 "src/lib/parser.ml"
     : (Absyn.lexp list))

let _menhir_action_09 =
  fun _endpos_b_ _startpos_x_ b p x ->
    let _endpos = _endpos_b_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 47 "src/lib/parser.mly"
                                            ( _loc , (x, p, b) )
# 254 "src/lib/parser.ml"
     : (Absyn.lfundec))

let _menhir_action_10 =
  fun x ->
    (
# 53 "src/lib/parser.mly"
                            ( x )
# 262 "src/lib/parser.ml"
     : (Absyn.lfundec list))

let _menhir_action_11 =
  fun _endpos_x_ _startpos_x_ x ->
    let _endpos = _endpos_x_ in
    let _startpos = _startpos_x_ in
    let _loc = (_startpos, _endpos) in
    (
# 50 "src/lib/parser.mly"
                                ( _loc, Absyn.Program x )
# 273 "src/lib/parser.ml"
     : (Absyn.lprogram))

let _menhir_action_12 =
  fun x ->
    (
# 218 "<standard.mly>"
    ( [ x ] )
# 281 "src/lib/parser.ml"
     : (Absyn.lfundec list))

let _menhir_action_13 =
  fun x xs ->
    (
# 220 "<standard.mly>"
    ( x :: xs )
# 289 "src/lib/parser.ml"
     : (Absyn.lfundec list))

let _menhir_action_14 =
  fun x ->
    (
# 29 "src/lib/parser.mly"
             ( x )
# 297 "src/lib/parser.ml"
     : (Absyn.lprogram))

let _menhir_action_15 =
  fun x ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 305 "src/lib/parser.ml"
     : (Absyn.lexp list))

let _menhir_action_16 =
  fun x xs ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 313 "src/lib/parser.ml"
     : (Absyn.lexp list))

let _menhir_action_17 =
  fun x ->
    (
# 238 "<standard.mly>"
    ( [ x ] )
# 321 "src/lib/parser.ml"
     : (Absyn.typeid list))

let _menhir_action_18 =
  fun x xs ->
    (
# 240 "<standard.mly>"
    ( x :: xs )
# 329 "src/lib/parser.ml"
     : (Absyn.typeid list))

let _menhir_action_19 =
  fun _endpos_x_ _startpos__1_ x ->
    let _endpos = _endpos_x_ in
    let _startpos = _startpos__1_ in
    let _loc = (_startpos, _endpos) in
    (
# 56 "src/lib/parser.mly"
             ( (Absyn.Int, (_loc,  x)) )
# 340 "src/lib/parser.ml"
     : (Absyn.typeid))

let _menhir_action_20 =
  fun _endpos_x_ _startpos__1_ x ->
    let _endpos = _endpos_x_ in
    let _startpos = _startpos__1_ in
    let _loc = (_startpos, _endpos) in
    (
# 57 "src/lib/parser.mly"
             ( (Absyn.Bool, (_loc,  x)) )
# 351 "src/lib/parser.ml"
     : (Absyn.typeid))

let _menhir_action_21 =
  fun x ->
    (
# 60 "src/lib/parser.mly"
                                           ( x )
# 359 "src/lib/parser.ml"
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
  
  let rec _menhir_run_41_spec_00 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _endpos _startpos _v ->
      let _v =
        let x = _v in
        _menhir_action_10 x
      in
      let _v =
        let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
        _menhir_action_11 _endpos_x_ _startpos_x_ x
      in
      let x = _v in
      let _v = _menhir_action_14 x in
      MenhirBox_program _v
  
  let rec _menhir_goto_nonempty_list_fundec_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _endpos _startpos _v _menhir_s ->
      match _menhir_s with
      | MenhirState45 ->
          _menhir_run_46 _menhir_stack _endpos _v
      | MenhirState00 ->
          _menhir_run_41_spec_00 _menhir_stack _endpos _startpos _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_46 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_fundec -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _endpos _v ->
      let MenhirCell1_fundec (_menhir_stack, _menhir_s, x, _startpos_x_, _) = _menhir_stack in
      let (_endpos_xs_, xs) = (_endpos, _v) in
      let _v = _menhir_action_13 x xs in
      _menhir_goto_nonempty_list_fundec_ _menhir_stack _endpos_xs_ _startpos_x_ _v _menhir_s
  
  let rec _menhir_run_01 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos_x_, x, _startpos__1_) = (_endpos, _v, _startpos) in
          let _v = _menhir_action_19 _endpos_x_ _startpos__1_ x in
          _menhir_goto_typeid _menhir_stack _menhir_lexbuf _menhir_lexer _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_typeid : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState37 ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState06 ->
          _menhir_run_36 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState45 ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | MenhirState00 ->
          _menhir_run_05 _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_36 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | COMMA ->
          let _menhir_stack = MenhirCell1_typeid (_menhir_stack, _menhir_s, _v, _startpos) in
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState37
          | BOOL ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState37
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_17 x in
          _menhir_goto_separated_nonempty_list_COMMA_typeid_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_run_03 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _menhir_s ->
      let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | ID _v ->
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos_x_, x, _startpos__1_) = (_endpos, _v, _startpos) in
          let _v = _menhir_action_20 _endpos_x_ _startpos__1_ x in
          _menhir_goto_typeid _menhir_stack _menhir_lexbuf _menhir_lexer _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_typeid_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState06 ->
          _menhir_run_39_spec_06 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState37 ->
          _menhir_run_38 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_39_spec_06 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_typeid -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _v =
        let x = _v in
        _menhir_action_21 x
      in
      let _menhir_stack = MenhirCell1_typeids (_menhir_stack, MenhirState06, _v) in
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
              _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState09 _tok
          | LET ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
          | IF ->
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState09
          | ID _v_3 ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v_3 MenhirState09
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_35 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_typeid, _menhir_box_program) _menhir_cell1_typeids _menhir_cell0_RPAREN as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BOOL | EOF | INT ->
          let MenhirCell0_RPAREN (_menhir_stack, _) = _menhir_stack in
          let MenhirCell1_typeids (_menhir_stack, _, p) = _menhir_stack in
          let MenhirCell1_typeid (_menhir_stack, _menhir_s, x, _startpos_x_) = _menhir_stack in
          let (_endpos_b_, b) = (_endpos, _v) in
          let _v = _menhir_action_09 _endpos_b_ _startpos_x_ b p x in
          let (_endpos, _startpos) = (_endpos_b_, _startpos_x_) in
          (match (_tok : MenhirBasics.token) with
          | INT ->
              let _menhir_stack = MenhirCell1_fundec (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState45
          | BOOL ->
              let _menhir_stack = MenhirCell1_fundec (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState45
          | EOF ->
              let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
              let _v = _menhir_action_12 x in
              _menhir_goto_nonempty_list_fundec_ _menhir_stack _endpos_x_ _startpos_x_ _v _menhir_s
          | _ ->
              _menhir_fail ())
      | _ ->
          _eRR ()
  
  and _menhir_run_21 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_exp -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LITINT _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _v _tok
      | LET ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState21
      | ID _v ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState21
      | _ ->
          _eRR ()
  
  and _menhir_run_22 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_exp -> _ -> _ -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok ->
      let MenhirCell1_exp (_menhir_stack, _menhir_s, x, _startpos_x_, _) = _menhir_stack in
      let (_endpos_y_, y) = (_endpos, _v) in
      let _v = _menhir_action_02 _endpos_y_ _startpos_x_ x y in
      _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_y_ _startpos_x_ _v _menhir_s _tok
  
  and _menhir_goto_exp : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match _menhir_s with
      | MenhirState09 ->
          _menhir_run_35 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState33 ->
          _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState13 ->
          _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState30 ->
          _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState28 ->
          _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState14 ->
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState23 ->
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState21 ->
          _menhir_run_22 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _v _tok
      | MenhirState25 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | MenhirState16 ->
          _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_34 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_LET _menhir_cell0_ID, _menhir_box_program) _menhir_cell1_exp as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BOOL | COMMA | ELSE | EOF | IN | INT | RPAREN | THEN ->
          let MenhirCell1_exp (_menhir_stack, _, f, _, _) = _menhir_stack in
          let MenhirCell0_ID (_menhir_stack, i, _, _) = _menhir_stack in
          let MenhirCell1_LET (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_ff_, ff) = (_endpos, _v) in
          let _v = _menhir_action_07 _endpos_ff_ _startpos__1_ f ff i in
          _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_ff_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_23 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_exp -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer ->
      let _tok = _menhir_lexer _menhir_lexbuf in
      match (_tok : MenhirBasics.token) with
      | LITINT _v ->
          let _startpos = _menhir_lexbuf.Lexing.lex_start_p in
          let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
          let _tok = _menhir_lexer _menhir_lexbuf in
          let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
          _menhir_run_24 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState23 _tok
      | LET ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState23
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState23
      | ID _v ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState23
      | _ ->
          _eRR ()
  
  and _menhir_run_24 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_exp as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BOOL | COMMA | ELSE | EOF | IN | INT | RPAREN | THEN ->
          let MenhirCell1_exp (_menhir_stack, _menhir_s, x, _startpos_x_, _) = _menhir_stack in
          let (_endpos_y_, y) = (_endpos, _v) in
          let _v = _menhir_action_03 _endpos_y_ _startpos_x_ x y in
          _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_y_ _startpos_x_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_11 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
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
                  _menhir_run_32 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState13 _tok
              | LET ->
                  _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
              | IF ->
                  _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState13
              | ID _v_5 ->
                  _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v_5 MenhirState13
              | _ ->
                  _eRR ())
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_32 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_LET _menhir_cell0_ID as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | IN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LITINT _v_0 ->
              let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
              let _endpos_2 = _menhir_lexbuf.Lexing.lex_curr_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_endpos_x_, _startpos_x_, x) = (_endpos_2, _startpos_1, _v_0) in
              let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
              _menhir_run_34 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState33 _tok
          | LET ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState33
          | IF ->
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState33
          | ID _v_4 ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState33
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_14 : type  ttv_stack. ttv_stack -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
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
          _menhir_run_27 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState14 _tok
      | LET ->
          _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
      | IF ->
          _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState14
      | ID _v ->
          _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v MenhirState14
      | _ ->
          _eRR ()
  
  and _menhir_run_27 : type  ttv_stack. ((ttv_stack, _menhir_box_program) _menhir_cell1_IF as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
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
              _menhir_run_29 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState28 _tok
          | LET ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState28
          | IF ->
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState28
          | ID _v_4 ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState28
          | _ ->
              _eRR ())
      | PLUS ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | _ ->
          _eRR ()
  
  and _menhir_run_29 : type  ttv_stack. (((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_exp as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | ELSE ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | LITINT _v_0 ->
              let _startpos_1 = _menhir_lexbuf.Lexing.lex_start_p in
              let _endpos_2 = _menhir_lexbuf.Lexing.lex_curr_p in
              let _tok = _menhir_lexer _menhir_lexbuf in
              let (_endpos_x_, _startpos_x_, x) = (_endpos_2, _startpos_1, _v_0) in
              let _v = _menhir_action_01 _endpos_x_ _startpos_x_ x in
              _menhir_run_31 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState30 _tok
          | LET ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
          | IF ->
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState30
          | ID _v_4 ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState30
          | _ ->
              _eRR ())
      | _ ->
          _eRR ()
  
  and _menhir_run_31 : type  ttv_stack. ((((ttv_stack, _menhir_box_program) _menhir_cell1_IF, _menhir_box_program) _menhir_cell1_exp, _menhir_box_program) _menhir_cell1_exp as 'stack) -> _ -> _ -> _ -> _ -> _ -> ('stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
      | BOOL | COMMA | ELSE | EOF | IN | INT | RPAREN | THEN ->
          let MenhirCell1_exp (_menhir_stack, _, y, _, _) = _menhir_stack in
          let MenhirCell1_exp (_menhir_stack, _, x, _, _) = _menhir_stack in
          let MenhirCell1_IF (_menhir_stack, _menhir_s, _startpos__1_) = _menhir_stack in
          let (_endpos_z_, z) = (_endpos, _v) in
          let _v = _menhir_action_05 _endpos_z_ _startpos__1_ x y z in
          _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_z_ _startpos__1_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_15 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
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
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState16 _tok
          | LET ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState16
          | IF ->
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState16
          | ID _v_4 ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState16
          | _ ->
              _eRR ())
      | BOOL | COMMA | ELSE | EOF | IN | INT | LT | PLUS | RPAREN | THEN ->
          let (_endpos_x_, _startpos_x_, x) = (_endpos, _startpos, _v) in
          let _v = _menhir_action_04 _endpos_x_ _startpos_x_ x in
          _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v _menhir_s _tok
      | _ ->
          _eRR ()
  
  and _menhir_run_20 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _endpos _startpos _v _menhir_s _tok ->
      match (_tok : MenhirBasics.token) with
      | PLUS ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_21 _menhir_stack _menhir_lexbuf _menhir_lexer
      | LT ->
          let _menhir_stack = MenhirCell1_exp (_menhir_stack, _menhir_s, _v, _startpos, _endpos) in
          _menhir_run_23 _menhir_stack _menhir_lexbuf _menhir_lexer
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
              _menhir_run_20 _menhir_stack _menhir_lexbuf _menhir_lexer _endpos_x_ _startpos_x_ _v MenhirState25 _tok
          | LET ->
              _menhir_run_11 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
          | IF ->
              _menhir_run_14 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState25
          | ID _v_4 ->
              _menhir_run_15 _menhir_stack _menhir_lexbuf _menhir_lexer _v_4 MenhirState25
          | _ ->
              _eRR ())
      | RPAREN ->
          let x = _v in
          let _v = _menhir_action_15 x in
          _menhir_goto_separated_nonempty_list_COMMA_exp_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
      | _ ->
          _eRR ()
  
  and _menhir_goto_separated_nonempty_list_COMMA_exp_ : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s ->
      match _menhir_s with
      | MenhirState25 ->
          _menhir_run_26 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | MenhirState16 ->
          _menhir_run_17_spec_16 _menhir_stack _menhir_lexbuf _menhir_lexer _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run_26 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_exp -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_exp (_menhir_stack, _menhir_s, x, _, _) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_16 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_exp_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_17_spec_16 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_ID -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let _v =
        let x = _v in
        _menhir_action_08 x
      in
      let _endpos = _menhir_lexbuf.Lexing.lex_curr_p in
      let _tok = _menhir_lexer _menhir_lexbuf in
      let MenhirCell1_ID (_menhir_stack, _menhir_s, x, _startpos_x_, _) = _menhir_stack in
      let (_endpos__4_, f) = (_endpos, _v) in
      let _v = _menhir_action_06 _endpos__4_ _startpos_x_ f x in
      _menhir_goto_exp _menhir_stack _menhir_lexbuf _menhir_lexer _endpos__4_ _startpos_x_ _v _menhir_s _tok
  
  and _menhir_run_38 : type  ttv_stack. (ttv_stack, _menhir_box_program) _menhir_cell1_typeid -> _ -> _ -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _v ->
      let MenhirCell1_typeid (_menhir_stack, _menhir_s, x, _) = _menhir_stack in
      let xs = _v in
      let _v = _menhir_action_18 x xs in
      _menhir_goto_separated_nonempty_list_COMMA_typeid_ _menhir_stack _menhir_lexbuf _menhir_lexer _v _menhir_s
  
  and _menhir_run_05 : type  ttv_stack. ttv_stack -> _ -> _ -> _ -> _ -> (ttv_stack, _menhir_box_program) _menhir_state -> _ -> _menhir_box_program =
    fun _menhir_stack _menhir_lexbuf _menhir_lexer _startpos _v _menhir_s _tok ->
      let _menhir_stack = MenhirCell1_typeid (_menhir_stack, _menhir_s, _v, _startpos) in
      match (_tok : MenhirBasics.token) with
      | LPAREN ->
          let _tok = _menhir_lexer _menhir_lexbuf in
          (match (_tok : MenhirBasics.token) with
          | INT ->
              _menhir_run_01 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
          | BOOL ->
              _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState06
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
          _menhir_run_03 _menhir_stack _menhir_lexbuf _menhir_lexer MenhirState00
      | _ ->
          _eRR ()
  
end

let program =
  fun _menhir_lexer _menhir_lexbuf ->
    let _menhir_stack = () in
    let MenhirBox_program v = _menhir_run_00 _menhir_stack _menhir_lexbuf _menhir_lexer in
    v
