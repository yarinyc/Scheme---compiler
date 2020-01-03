#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "SOB_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)
  val make_fvars_tbl : expr' list -> (string * int) list

  (* This signature represents the idea of outputing assembly code as a string
     for a single AST', given the full constants and fvars tables.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string

  (* let make_consts_tbl exprList = *)

end;;

  let rename exprList counterList =
    let rec run exprList =
      match exprList with
      | [] -> []
      | car::cdr -> (renameAST car)::(run cdr)

    and renameTagRef name =
      let optCounter = List.find_opt (fun x -> match x with |(currName,_)-> (if(currName=name) then true else false)) !counterList in
      let counter = match optCounter with | Some((x,y)) -> y | _-> raise X_this_should_not_happen in
      let newName = String.concat "" [name; (string_of_int !counter)] in
      newName

    and renameTagExp name =
      let optCounter = List.find_opt (fun x -> match x with |(currName,_)-> (if(currName=name) then true else false)) !counterList in
      let counter = match optCounter with | Some((x,y)) -> y | _-> (ref 0) in
      if((!counter)=0)
      then ((counterList:= (name, (ref 1))::(!counterList));
            let newName = String.concat "" [name; "1"] in
            newName)
      else ((counter:= !counter+1);
            let newName = String.concat "" [name;(string_of_int !counter)] in
            newName)

    and renameSexpr sexpr =
      match sexpr with
      | Pair(x,y) -> Pair((renameSexpr x), (renameSexpr y))
      | TagRef(x) -> TagRef(renameTagRef x)
      | TaggedSexpr(name, sexp) -> let newName = renameTagExp name in
                            TaggedSexpr(newName,(renameSexpr sexp))
      | _ -> sexpr

    and renameAST expr =
      match expr with
      | Const'(Sexpr(TagRef(x))) -> Const'(Sexpr(TagRef(renameTagRef x)))
      | Const'(Sexpr(TaggedSexpr(name,sexpr))) -> let newName = renameTagExp name in
                            Const'(Sexpr(TaggedSexpr(newName,(renameSexpr sexpr))))
      | Const'(Sexpr(x)) -> Const'(Sexpr(renameSexpr x))
      | Const'(Void) -> expr
      | Var'(x) -> expr
      | Box'(x) -> expr
      | BoxSet'(var,exp) -> BoxSet'(var,renameAST exp)
      | BoxGet'(x) -> expr
      | If'(test,dit,dif) -> If'((renameAST test), (renameAST dit), (renameAST dif))
      | Seq'(exps) -> Seq'(List.map renameAST exps)
      | Set'(x, exp) -> Set'(x, renameAST exp)
      | Def'(x, exp) -> Def'(x, renameAST exp)
      | Or'(exps) -> Or'(List.map renameAST exps)
      | LambdaSimple'(params,body) -> LambdaSimple'(params,(renameAST body))
      | LambdaOpt'(params,opt,body) -> LambdaOpt'(params,opt,renameAST body)
      | Applic'(op, args) -> Applic'((renameAST op), (List.map renameAST args))
      | ApplicTP'(op, args) -> ApplicTP'((renameAST op), (List.map renameAST args)) in

    run exprList;;

  (* let make_consts_tbl exps = *)


module Code_Gen : CODE_GEN = struct
  let make_consts_tbl asts = raise X_not_yet_implemented;;
  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

