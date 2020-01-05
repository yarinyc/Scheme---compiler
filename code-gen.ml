#use "semantic-analyser.ml";;
open Semantics;;

exception X_code_gen_error of string;;
exception X_debug of constant;;


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

module Code_Gen : CODE_GEN = struct
  (* aux functions: *)
  let car (x,y) = x;;
  let cdr (x,y) = y;;

  (* rename all tagged expressions: *)
  let rename exprList counterList =
    let rec run exprList =
      match exprList with
      | [] -> []
      | car::cdr -> let res = (renameAST car) in
                    res::(run cdr)

    and renameTagRef name =
      let optCounter = List.find_opt (fun x -> match x with |(currName,_)-> (if(currName=name) then true else false)) !counterList in
      let counter = match optCounter with | Some((x,y)) -> y | _-> raise (X_code_gen_error "TagRef without definition") in
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
      | If'(test,dit,dif) -> let newTest = renameAST test in
                             let newDit = renameAST dit in
                             let newDif = renameAST dif in
                             If'(newTest, newDit, newDif)
      | Seq'(exps) -> Seq'(List.map renameAST exps)
      | Set'(x, exp) -> Set'(x, renameAST exp)
      | Def'(x, exp) -> Def'(x, renameAST exp)
      | Or'(exps) -> Or'(List.map renameAST exps)
      | LambdaSimple'(params,body) -> LambdaSimple'(params,(renameAST body))
      | LambdaOpt'(params,opt,body) -> LambdaOpt'(params,opt,renameAST body)
      | Applic'(op, args) -> let newOp = renameAST op in
                             Applic'(newOp, (List.map renameAST args))
      | ApplicTP'(op, args) -> let newOp = renameAST op in
                               ApplicTP'(newOp, (List.map renameAST args)) in

    run exprList;;
  (* main aux function for make_consts_tbl: *)
  let aux_make_consts_tbl asts taggedCollection constTbl counter =

    (* ------> second pass: *)
    let aux_secondPass asts =
      let rec secondPass asts =
        match asts with
        | [] -> ()
        | car::cdr -> ((buildConstTbl car);(secondPass cdr))

      and buildConstTbl expr =
        match expr with
        | Const'(Sexpr(TagRef(x))) -> ()
        | Const'(Sexpr(TaggedSexpr(name,sexp))) -> ((collectTags name sexp);(addToConst sexp))
        | Const'(Sexpr(x)) -> (addToConst x)
        | Const'(Void) -> ()
        | Var'(x) -> ()
        | Box'(x) -> ()
        | BoxSet'(var,exp) -> (buildConstTbl exp)
        | BoxGet'(x) -> ()
        | If'(test,dit,dif) -> ((buildConstTbl test);(buildConstTbl dit);(buildConstTbl dif))
        | Seq'(exps) -> (aux_mapThenUnit exps )
        | Set'(x, exp) -> (buildConstTbl exp)
        | Def'(x, exp) -> (buildConstTbl exp)
        | Or'(exps) -> (aux_mapThenUnit exps)
        | LambdaSimple'(params,body) -> (buildConstTbl body)
        | LambdaOpt'(params,opt,body) -> (buildConstTbl body)
        | Applic'(op, args) ->  (buildConstTbl op) ;
                              (aux_mapThenUnit args)
        | ApplicTP'(op, args) -> (buildConstTbl op) ;
                                (aux_mapThenUnit args)
      and aux_mapThenUnit lst =
        let list = List.map buildConstTbl lst in
        let unit =() in
        let unitPair = (unit,list) in
        (car unitPair)

      and collectTags name sexp =
        taggedCollection:= (name, sexp)::(!taggedCollection)

      and addToConst sexp =
        match sexp with
        | Number(Int(x)) -> if(member sexp (!constTbl)) then () else (constTbl:= !constTbl@[((Sexpr(sexp)),(!counter, (Printf.sprintf "MAKE_LITERAL_INT(%d)\n" x)))]; (counter := (!counter) + 9))
        | Number(Float(x)) -> if(member sexp (!constTbl)) then () else (constTbl:= !constTbl@[((Sexpr(sexp)),(!counter, (Printf.sprintf "MAKE_LITERAL_FLOAT(%f)\n" x)))]; (counter := (!counter) + 9))
        | Bool(x) -> ()
        | Nil -> ()
        | Char(x) -> if(member sexp (!constTbl)) then () else (constTbl:= !constTbl@[((Sexpr(sexp)),(!counter, (Printf.sprintf "MAKE_LITERAL_CHAR(%c)\n" x)))]; (counter := (!counter) + 2))
        | String(x) -> if(member sexp (!constTbl)) then () else (constTbl:= !constTbl@[((Sexpr(sexp)),(!counter, (Printf.sprintf "MAKE_LITERAL_STRING(\"%s\")\n" x)))]; (counter := (!counter) + 9 + (String.length x)))
        | Symbol(x) -> if(member sexp (!constTbl)) then () else (constTbl:= !constTbl@[((Sexpr(sexp)),(!counter, (Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)\n" (findPtr x constTbl))))]; (counter := (!counter) + 9))
        | Pair(x,y) -> (addToConst x);
                      (addToConst y);
                      (if(member sexp (!constTbl)) then () else (constTbl:= !constTbl@[((Sexpr(sexp)),(!counter, (Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d,const_tbl+%d)\n" (getOffset x) (getOffset y))))]; (counter := (!counter) + 17)))
        | TaggedSexpr(name,sexp) -> ((collectTags name sexp);(addToConst sexp))
        | TagRef(x) -> ()

      and member exp list =
        (* let newExp = match exp with | Sexpr(x) -> x | _-> raise (X_code_gen_error "member expected only type sexpr") in *)
        match list with
        | [] -> false
        | (Void,(off,str))::xs -> (member exp xs)
        | x::xs -> let currExp = match (car x) with | Sexpr(x) -> x | _-> raise (X_code_gen_error "member expected only type sexpr") in
                if(sexpr_eq currExp exp) then true else (member exp xs)

      and find exp list =
        match list with
        | [] -> None
        | (Void,(off,str))::xs -> (find exp xs)
        | x::xs -> let currExp = match (car x) with | Sexpr(x) -> x | _-> raise (X_code_gen_error "find expected only type sexpr") in
                   if(sexpr_eq currExp exp) then Some (x) else (find exp xs)

      and getOffset exp =
        let toSearch = (match exp with | TaggedSexpr(name,sexp) -> sexp | _ -> exp) in
        let res = find toSearch (!constTbl) in
        match res with
        | None -> (-1)
        | Some(x,(off,str)) -> off

      and findPtr str list=
        let currCounter = (ref 0) in
        let found = (find (String(str)) (!list)) in
        match found with
        | None -> (constTbl:= !constTbl@[((Sexpr(String(str))), ((!counter), (Printf.sprintf "MAKE_LITERAL_STRING(\"%s\")\n" str)))];
                  currCounter := (!counter);
                  (counter := (!counter) + 9 + (String.length str))); (!currCounter)
        | Some (x) -> (car (cdr x)) in

      (secondPass asts) in
    (* ------> end of second pass *)

    (* ------> third pass: *)
    let aux_thirdPass currConstTable =
      let rec thirdPass constTable =
        match constTable with
        | [] -> []
        | (sexp,(off,asmStr))::cdr ->
            let (offset1,offset2) = (findTagRefs sexp) in
            let newAsmStr = (makeAsmString asmStr offset1 offset2) in
            (sexp,(off,newAsmStr))::(thirdPass cdr)

      and makeAsmString str offset1 offset2 =
        if(offset1=(-1) && offset2=(-1))
        then str
        else let oldOffsets = String.split_on_char ',' (String.sub str 28 ((String.length str)-30)) in
             let oldOffset1 = (int_of_string (List.hd oldOffsets)) in
             let tmp = (List.hd (List.tl oldOffsets)) in
             let oldOffset2 = (int_of_string (String.sub tmp 10 ((String.length tmp)-10) )) in
             let (newOffset1,newOffset2) =
               match offset1,offset2 with
               | (-1),_ -> (oldOffset1,offset2)
               | _,(-1) -> (offset1,oldOffset2)
               | _,_ -> (offset1,offset2) in
             (Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d,const_tbl+%d)\n" newOffset1 newOffset2)

      and findTagRefs sexp =
        match sexp with
        | Sexpr(Pair(TagRef(x),TagRef(y))) -> ((fixTagRef x),(fixTagRef y))
        | Sexpr(Pair(TagRef(x),y)) -> ((fixTagRef x),(-1))
        | Sexpr(Pair(x,TagRef(y))) -> ((-1),(fixTagRef y))
        | _ -> ((-1),(-1))

      and fixTagRef str =
        let value = (findRef str (!taggedCollection)) in
        let res = find value (!constTbl) in
        let res = match res with | Some((exp,(off,asmStr))) -> off | _ -> raise (X_code_gen_error "TagRef without definition (fixTagRef())") in
        res

      and find exp list =
        match list with
        | [] -> None
        | (Void,(off,str))::xs -> (find exp xs)
        | x::xs -> let currExp = match (car x) with | Sexpr(x) -> x | _-> raise (X_code_gen_error "find expected only type sexpr") in
                   if(sexpr_eq currExp exp) then Some (x) else (find exp xs)

      and findRef str list =
        match list with
        | [] -> raise (X_code_gen_error "TagRef without definition (findRef())")
        | (x,y)::cdr -> if (x = str) then y else (findRef str cdr) in

      thirdPass (!currConstTable) in
      (* ------> end of third pass *)


    let newAsts = rename asts (ref []) in (*activate first pass - rename all tagged exps*)
    (aux_secondPass newAsts) ; (aux_thirdPass constTbl);;

  let make_consts_tbl asts =
    let newTable = [((Sexpr(Nil)),(0,"MAKE_NIL\n"));(Void,(1,"MAKE_VOID\n"));((Sexpr(Bool(true))),(2,"MAKE_BOOL(1)\n"));((Sexpr(Bool(false))),(4,"MAKE_BOOL(0)\n"))] in
    aux_make_consts_tbl asts (ref []) (ref newTable) (ref 6);;
                (*definitions collection , const_table , counter*)

  let make_fvars_tbl asts = raise X_not_yet_implemented;;
  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

