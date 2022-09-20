(* semantic.ml *)

open Absyn

let rec check_type_list list1 list2 loc = 
   match list1,list2 with 
   | [item1], [item2] -> 
     if item1 == item2 then () 
       else 
         Error.error (Location.loc loc) "Param type not match"
   | item1 :: rest1, item2 :: rest2 -> 
     if item1 == item2 then
       let x = check_type_list (rest1) (rest2) in
       ()
     else 
       Error.error (Location.loc loc) "Param type not match"

let rec check_exp (loc, exp) vtable ftable =
  match exp with
  | IntExp x -> Int
  | VarExp v ->
   ( match Symbol.look v vtable with
    | Some t -> t
    | None -> Error.error loc "undefined variable %s" (Symbol.name v)
   )
  | LetExp (v, init, body) ->
     let t_init = check_exp init vtable ftable in
     let vtable' = Symbol.enter v t_init vtable in
     check_exp body vtable' ftable
  | OpExp (op, l, r) -> 
      let t1 = check_exp l vtable ftable in
      let t2 = check_exp r vtable ftable in
      (match op with 
      | Plus -> 
      if t1 == Int && t2 == Int
        then Int
      else 
        Error.error (loc) "Sum exp not valid"
      | LT -> 
        if t1 == t2 
          then Bool
        else 
          Error.error (loc) "LT exp not valid")
   | IfExp (x, y, z) -> 
      let t1 = check_exp x vtable ftable in 
      let t2 = check_exp y vtable ftable in 
      let t3 = check_exp z vtable ftable in 
        if t1 == Bool && t2 == t3 
            then t2 
         else 
            Error.error (loc) "IfExp not valid"
   | CallExp (x, y) -> 
      (match Symbol.look x ftable with
         | Some (typeList, returnType) -> 
               let listTypes = check_exps y vtable ftable in
               let lengthList = List.length listTypes in
               let lengthOriginal = List.length typeList in 
               if (lengthList == lengthOriginal)
                  then 
                     let typeCheck = check_type_list typeList listTypes (loc, exp) in
                     returnType;
               else
                  Error.error loc "Invalid params size"
         | None -> Error.error loc "Function %s not found in ftable" (Symbol.name x))
  | _ -> Error.fatal "unimplemented"

and check_exps (exps) (vtable) (ftable) = 
  match exps with 
  | [exp] -> let t = check_exp exp vtable ftable in
        [t]
  | exp :: rest -> 
    check_exp exp vtable ftable ::
    check_exps rest vtable ftable

let get_typeid (t, id) =
    (t, id)

let rec check_typeids typeids =
  match typeids with
  | [] -> Error.fatal "parameter list cannot be null"
  | [typeid] ->
     let (t, (_loc, x)) = get_typeid typeid in
     Symbol.enter x t Symbol.empty
  | typeid :: typeids ->
     let (t, (loc, x)) = get_typeid typeid in
     let vtable = check_typeids typeids in
     match Symbol.look x vtable with
     | None -> Symbol.enter x t vtable
     | Some _ -> Error.error loc "parameter already defined"

let get_types typeids =
   List.map fst typeids

let get_fun (typeid, params, body) =
   let (t0, (_, f)) = get_typeid typeid in
   let tparams = get_types params in
   (f, (tparams, t0))

let check_fun (loc, (typeid, typeids, exp)) ftable =
   let (t0, (_, f)) = get_typeid typeid in
   let vtable = check_typeids typeids in
   let t1 = check_exp exp vtable ftable in
   if t0 <> t1 then
      Error.error (Location.loc exp) "type mismatch in function body"

let check_funs funs ftable =
   List.iter (fun f -> check_fun f ftable) funs

let rec get_funs funs =
  match funs with
  | [] -> Error.fatal "no funtion is not allowed"
  | [(_, fundec)] ->
     let (f, t) = get_fun fundec in
     Symbol.enter f t Symbol.empty
  | (loc, fundec) :: rest ->
     let (f, t) = get_fun fundec in
     let ftable = get_funs rest in
     match Symbol.look f ftable with
     | Some _ ->
        Error.error loc "function %s defined more than once" (Symbol.name f)
     | None ->
        Symbol.enter f t ftable

let check_program (loc, Program funs) =
  let ftable = get_funs funs in
  check_funs funs ftable;
  match Symbol.look (Symbol.symbol "main") ftable with
  | Some ([Int], Int) -> ()
  | Some _ -> Error.error loc "wrong type for main function"
  | None -> Error.error loc "missing main function"

let semantic ast =
   check_program ast
