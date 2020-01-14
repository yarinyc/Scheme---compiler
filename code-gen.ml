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

  val rename : expr' list -> (string * int ref * bool ref) list ref -> expr' list


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
                    (counterList:= List.map (fun ((x,y,z)) -> (x,y,(ref false))) !counterList;
                    res::(run cdr))

    and renameTagExp name =
      let optCounter = List.find_opt (fun x -> match x with |(currName,_,_)-> (if(currName=name) then true else false)) !counterList in
      let counter = match optCounter with | Some((x,y,z)) -> y | _-> (ref 0) in
      let boolean = match optCounter with | Some((x,y,z)) -> z | _-> (ref true) in
      if((!counter)=0)
      then ((counterList:= (name, (ref 1), (ref true))::(!counterList));
            let newName = String.concat "" [name; "1"] in
            newName)
      else if (!boolean)
           then let newName = String.concat "" [name;(string_of_int !counter)] in
                    newName
           else ((counter:= !counter+1);
                 (boolean:= true);
                 let newName = String.concat "" [name;(string_of_int !counter)] in
                 newName)


    and renameSexpr sexpr =
      match sexpr with
      | Pair(x,y) -> let renameX = (renameSexpr x) in
                     Pair(renameX, (renameSexpr y))
      | TagRef(x) -> TagRef(renameTagExp x)
      | TaggedSexpr(name, sexp) -> let newName = renameTagExp name in
                            TaggedSexpr(newName,(renameSexpr sexp))
      | _ -> sexpr

    and renameAST expr =
      match expr with
      | Const'(Sexpr(TagRef(x))) -> Const'(Sexpr(TagRef(renameTagExp x)))
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
        | Char(x) -> if(member sexp (!constTbl)) then () else (constTbl:= !constTbl@[((Sexpr(sexp)),(!counter, (Printf.sprintf "MAKE_LITERAL_CHAR('%c')\n" x)))]; (counter := (!counter) + 2))
        | String(x) -> if(member sexp (!constTbl)) then () else (constTbl:= !constTbl@[((Sexpr(sexp)),(!counter, (Printf.sprintf "MAKE_LITERAL_STRING \"%s\"\n" x)))]; (counter := (!counter) + 9 + (String.length x)))
        | Symbol(x) -> if(member sexp (!constTbl)) then () else (constTbl:= !constTbl@[((Sexpr(sexp)),(!counter, (Printf.sprintf "MAKE_SYMBOL(const_tbl+%d)\n" (findPtr x constTbl))))]; (counter := (!counter) + 9))
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
        | None -> (constTbl:= !constTbl@[((Sexpr(String(str))), ((!counter), (Printf.sprintf "MAKE_LITERAL_STRING \"%s\"\n" str)))];
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
    let newTable = [(Void,(0,"MAKE_VOID\n"));((Sexpr(Nil)),(1,"MAKE_NIL\n"));((Sexpr(Bool(true))),(2,"MAKE_BOOL(1)\n"));((Sexpr(Bool(false))),(4,"MAKE_BOOL(0)\n"))] in
    aux_make_consts_tbl asts (ref []) (ref newTable) (ref 6);;
                (*definitions collection , const_table , counter*)

  let aux_make_fvars_tbl asts counter =
    let rec run asts counter =
      match asts with
      | [] -> []
      | car::cdr -> (make_freeVars counter car)@(run cdr counter)

    and make_freeVars counter ast =
      match ast with
      (* | Seq'(exps) -> List.fold_left (fun acc e -> acc@e) [] (List.map (make_freeVars counter) exps) *)
      | Def'(Var'(VarFree(name)), exp) -> (counter:= (!counter) + 1) ;[(name,((!counter)-1))]
      | _ -> [] in
    (run asts counter);;

    let aux_primitive_names_to_labels = 
      ["boolean?", "is_boolean"; "float?", "is_float"; "integer?", "is_integer"; "pair?", "is_pair";
      "null?", "is_null"; "char?", "is_char"; "string?", "is_string";
      "procedure?", "is_procedure"; "symbol?", "is_symbol"; "string-length", "string_length";
      "string-ref", "string_ref"; "string-set!", "string_set"; "make-string", "make_string";
      "symbol->string", "symbol_to_string";
      "char->integer", "char_to_integer"; "integer->char", "integer_to_char"; "eq?", "is_eq";
      "+", "bin_add"; "*", "bin_mul"; "-", "bin_sub"; "/", "bin_div"; "<", "bin_lt"; "=", "bin_equ";
      "car", "car_prim" ; "cdr", "cdr_prim" ; "cons", "cons_prim" ; "set-car!" , "set_car_prim";
      "set-cdr!" , "set_cdr_prim"; "apply" ,"apply_prim"
    (* you can add yours here *)];;

  let make_fvars_tbl asts =
    let counter = (ref 0) in
    let primFreeVars = List.map (fun ((a,b)) -> ((counter:= !counter +1);(a,(!counter - 1))) ) aux_primitive_names_to_labels in
    primFreeVars@(aux_make_fvars_tbl asts counter);;

  let rec findAddress exp constable =
    match constable with
    | [] -> raise (X_code_gen_error "shouldn't happen (findAddress())")
    | (Void,(off,str))::xs -> if(exp = Void) then off  else (findAddress exp xs)
    | ((Sexpr(e)),(off,str))::xs -> let sexpr = match exp with | Sexpr(x) -> x | _-> raise (X_code_gen_error "shouldn't happen (findAdress())") in
                                  if(sexpr_eq e sexpr) then off else (findAddress exp xs);;

  let rec findFreeAddress name freeVar =
    match freeVar with
    | [] -> raise (X_code_gen_error (Printf.sprintf "shouldn't happen (findFreeAddress(%s))" name))
    | (x,index)::cdr -> if (x = name) then index else (findFreeAddress name cdr);;

  let rec findTagDefinition name collection =
    match collection with
    | [] -> raise (X_code_gen_error "shouldn't happen (findTagDefinition())")
    | (str,sexpr)::xs -> if (str = name) then Sexpr(sexpr) else (findTagDefinition name xs)

  let splitLast lst =
    let last = List.nth lst ((List.length lst)-1) in
    let rec cut l =
      match l with
      | [a] -> []
      | a::b -> [a]@ (cut b)
      | _ -> [] in
    ((cut lst),last);;

  let getCollection e taggedCollection =
    let collectTags name sexp =
        taggedCollection:= (name, sexp)::(!taggedCollection) in
    let rec collect sexp =
      match sexp with
      | Pair(x,y) -> (collect x);
                    (collect y)
      | TaggedSexpr(name,sexp) -> (collectTags name sexp)
      | _  -> ()
    and traverseAst ast =
        match ast with
      | Const'(Sexpr(TagRef(x))) -> ()
      | Const'(Sexpr(TaggedSexpr(name,sexp))) -> (collectTags name sexp);(collect sexp)
      | Const'(Sexpr(x)) -> (collect x)
      | Const'(Void) -> ()
      | Var'(x) -> ()
      | Box'(x) -> ()
      | BoxSet'(var,exp) -> (traverseAst exp)
      | BoxGet'(x) -> ()
      | If'(test,dit,dif) -> ((traverseAst test);(traverseAst dit);(traverseAst dif))
      | Seq'(exps) -> (aux_mapThenUnit exps )
      | Set'(x, exp) -> (traverseAst exp)
      | Def'(x, exp) -> (traverseAst exp)
      | Or'(exps) -> (aux_mapThenUnit exps)
      | LambdaSimple'(params,body) -> (traverseAst body)
      | LambdaOpt'(params,opt,body) -> (traverseAst body)
      | Applic'(op, args) ->  (traverseAst op) ;
                            (aux_mapThenUnit args)
      | ApplicTP'(op, args) -> (traverseAst op) ;
                              (aux_mapThenUnit args)
    and aux_mapThenUnit lst =
      let list = List.map traverseAst lst in
      let unit =() in
      let unitPair = (unit,list) in
      (car unitPair) in
    (traverseAst e); taggedCollection;;

  let counter_Lexit = ref 1;;
  let counter_Lelse = ref 1;;
  let counter_LNoError = ref 1;;
  let counter_Lfunc = ref 1;;
  let counter_Lcode =ref 1;;
  let counter_Lcont = ref 1;;
  let counter_Lloop = ref 1;;

  let getLabel label_name label_counter =
    let counter = (!label_counter) in
    let newLabel = (label_name ^ (string_of_int counter)) in
    (label_counter := !label_counter + 1) ; newLabel;;

  (* let rec extEnv currDepth =
    if(currDepth = 0)
    then (createArgsVector ())
    else (Printf.sprintf "\tmov rbx, qword [rdi + WORD_SIZE*%d]\n\tmov qword [rsi + WORD_SIZE*%d], rbx\n" (currDepth-1) currDepth) ^ (extEnv (currDepth - 1))
  and createArgsVector () =
      let myLoop = getLabel "myLoop" counter_Lloop in
      let endLoop = "end"^myLoop in
     "\tmov rcx, qword [rbp + WORD_SIZE*3]\n" ^ (Printf.sprintf "\tcmp rcx, 0\n\tje %s\n" endLoop)
     ^ "\tmov rdx, rcx\n" ^ "\tshl rdx, 3\n" ^ "\tMALLOC rbx, rdx\n"
     ^ (Printf.sprintf "\t%s:\n" myLoop) ^
     "\t\tmov rdx, rcx\n" ^
     "\t\tdec rdx\n" ^
     "\t\tmov rdx, PVAR(rdx)\n" ^
     "\t\tmov rax, rcx\n\t\tdec rax\n" ^
     "\t\tmov qword [rbx + WORD_SIZE*rax], rdx\n" ^
     (Printf.sprintf "\t\tloop %s, rcx\n" myLoop) ^"\t mov qword[rsi], rbx\n"^ Printf.sprintf "\t%s:\n" endLoop;; *)

  let rec extEnv currDepth pLength =
      if(currDepth = 0)
      then if(pLength = 0)
           then "\tmov qword [rsi], 0\n"
           else (Printf.sprintf "\tMALLOC rbx, WORD_SIZE*%d\n" pLength)
                ^ (createArgsVector pLength)
                ^ "\tmov qword [rsi], rbx\n"
      else (Printf.sprintf "\tmov rbx, qword [rdi + WORD_SIZE*%d]\n\tmov qword [rsi + WORD_SIZE*%d], rbx\n" (currDepth-1) currDepth) ^ (extEnv (currDepth - 1) pLength)
    and createArgsVector pLength =
      if(pLength = 0)
      then ""
      else (Printf.sprintf "\tmov rdi, PVAR(%d)\n" (pLength-1))
           ^ (Printf.sprintf "\tmov [rbx + WORD_SIZE*%d], rdi \n" (pLength-1))
           ^ (createArgsVector (pLength -1));;




  let generate consts fvars e =
    let tagCollection = getCollection e (ref []) in

    let rec aux_generate depth paramsLength e =
      match e with
      | Const'(x) ->  let exp = (match x with
                                | Sexpr(TaggedSexpr(name, sexpr)) -> Sexpr(sexpr)
                                | Sexpr(TagRef(name)) -> (findTagDefinition name (!tagCollection))
                                | _-> x) in
                      let address = (findAddress exp consts) in
                      (Printf.sprintf "\tmov rax, (const_tbl + %d)\n" address)
      | Var'(VarParam(_, minor)) -> (Printf.sprintf "\tmov rax, qword [rbp + WORD_SIZE*(4 + %d)]\n" minor)
      | Set'(Var'(VarParam(_, minor)),exp) -> String.concat "" [(aux_generate depth paramsLength exp); (Printf.sprintf "\tmov qword [rbp + WORD_SIZE*(4+%d)], rax \n
                                                                           \tmov rax, SOB_VOID_ADDRESS \n" minor)]
      | Var'(VarBound(_, major, minor)) ->
      (Printf.sprintf "\tmov rax, qword [rbp + WORD_SIZE*2]\n\tmov rax, qword [rax + WORD_SIZE*%d]\n\tmov rax, qword [rax + WORD_SIZE*%d]\n" major minor)
      | Set'(Var'(VarBound(_,major,minor)),exp) -> String.concat "" [(aux_generate depth paramsLength exp); (Printf.sprintf "\tmov rbx, qword [rbp + WORD_SIZE*2] \n
                                                                                   \tmov rbx, qword [rax + WORD_SIZE*%d] \n
                                                                                   \tmov qword [rbx + WORD_SIZE*%d], rax \n
                                                                                   \tmov rax, SOB_VOID_ADDRESS\n" major minor)]
      | Var'(VarFree(v)) -> let address = findFreeAddress v fvars in
                            (Printf.sprintf "\tmov rax, qword [fvar_tbl + WORD_SIZE*%d]\n" address)
      | Set'(Var'(VarFree(v)),exp) ->
                            let address = (findFreeAddress v fvars) in
                            (aux_generate depth paramsLength exp) ^
                            (Printf.sprintf "\tmov qword [fvar_tbl + WORD_SIZE*%d], rax\n
                                             \tmov rax, SOB_VOID_ADDRESS\n" address)
      | Seq'(exps) -> String.concat " " (List.map (aux_generate depth paramsLength)  exps)
      | Or'(exps) -> let (list,last) = (splitLast exps) in
                     let labelExit = (getLabel "Lexit" counter_Lexit) in
                    (String.concat ""  ((List.map (fun(x) -> String.concat "" [(aux_generate depth paramsLength x);
                             "\tcmp rax, SOB_FALSE_ADDRESS \n"; "\tjne " ^ labelExit ^ "\n"]) list) @ [(aux_generate depth paramsLength last); "\t" ^ labelExit ^ ":\n"]))
      | If'(test,dit,dif) -> let labelExit = (getLabel "Lexit" counter_Lexit) in
                             let labelElse = (getLabel "Lelse" counter_Lelse) in
                              ((aux_generate depth paramsLength test) ^ "\tcmp rax, SOB_FALSE_ADDRESS \n\tje " ^ labelElse ^ "\n" ^
                              (aux_generate depth paramsLength dit) ^ "\tjmp " ^ labelExit ^"\n\t" ^ labelElse ^ ":\n" ^
                              (aux_generate depth paramsLength dif) ^ "\t" ^ labelExit ^ ":\n")
      | BoxGet'(v) -> (aux_generate depth paramsLength (Var'(v))) ^ "\tmov rax, qword [rax]\n"
      | BoxSet'(v,exp) -> (aux_generate depth paramsLength exp) ^ "\tpush rax\n" ^ (aux_generate depth paramsLength (Var'(v)))
                          ^ "\tpop qword [rax]\n" ^ "\tmov rax, SOB_VOID_ADDRESS\n"
      | Def'(Var'(VarFree(v)),exp) -> let address = findFreeAddress v fvars in
                                      let value = aux_generate depth paramsLength exp in
                                      value ^ (Printf.sprintf "\tmov qword [fvar_tbl + WORD_SIZE*%d], rax\n" address)
                                      ^ "\tmov rax, SOB_VOID_ADDRESS\n"
      | Applic'(op, args) ->
            let pushedArgs = String.concat "" (List.map (fun e -> (aux_generate depth paramsLength e) ^ "\tpush rax\n") (List.rev args)) in
            let n = (Printf.sprintf "\tpush %d\n" (List.length args)) in
            let operator = aux_generate depth paramsLength op in
            let pushMagic = "\tpush SOB_NIL_ADDRESS\n" in
            let labelNoError = getLabel "LNoError" counter_LNoError in
            let callClosure =  "\tcmp TYPE(rax), T_CLOSURE\n"
                              ^ "\tje " ^ labelNoError ^ "\n"
                              ^ "\tmov rax, 1\n\tmov rbx, 1\n\tint 0x80 ;exit program when trying to apply a non closure\n"
                              ^ "\t" ^ labelNoError ^ ": ;(applic)\n"
                              ^ "\tpush GET_ENV(rax)\n"
                              ^ "\tcall GET_BODY(rax)\n"
                              ^ "\tadd rsp, 8*1 ; pop env\n"
                              ^ "\tpop rbx ; pop arg count\n"
                              ^ "\tshl rbx, 3 ; rbx = rbx * 8\n"
                              ^ "\tadd rsp, rbx ; pop args\n"
                              ^ "\tadd rsp, 8\n" ^ "\t;;(*** end of applic ***)\n" in
            (pushMagic ^ pushedArgs ^ n ^ operator ^ callClosure)
      | ApplicTP'(op, args) ->
            let pushedArgs = String.concat "" (List.map (fun e -> (aux_generate depth paramsLength e) ^ "\tpush rax\n") (List.rev args)) in
            let n = (Printf.sprintf "\tpush %d\n" (List.length args)) in
            let operator = aux_generate depth paramsLength op in
            let pushMagic = "\tpush SOB_NIL_ADDRESS\n" in
            let labelNoError = getLabel "LNoError" counter_LNoError in
            let callClosure =  "\tcmp TYPE(rax), T_CLOSURE\n"
                              ^ "\tje " ^ labelNoError ^ "\n"
                              ^ "\tmov rax, 1\n\tmov rbx, 1\n\tint 0x80 ;exit program when trying to apply a non closure\n"
                              ^ "\t" ^ labelNoError ^ ": ;(applicTP)\n"
                              ^ "\tmov qword [temp_ptr], rax\n"
                              ^ "\tpush GET_ENV(rax)\n"
                              ^ "\tpush qword [rbp +WORD_SIZE]\n"

                              ^ "\tmov rbx, [rbp + WORD_SIZE*3];to get the n \n"
                              ^ "\tadd rbx, 5\n"
                              ^ "\tshl rbx, 3 ; size of first frame\n"
                              ^ (Printf.sprintf "\tsub rbx, WORD_SIZE*(4 + %d) ; (a-b)\n" (List.length args))
                              ^ "\tadd rbx, rbp\n"
                              ^ "\tmov rdi, rbx\n"
                              ^ "\tmov rsi, rsp\n"
                              ^ (Printf.sprintf "\tmov rdx, WORD_SIZE*(4 + %d)\n" (List.length args))
                              ^ "\tmov rbp, qword [rbp]\n"
                              ^ "\tcall memmove\n"
                              ^ "\tmov rsp, rax\n"

                              ^ "\tmov rax, qword [temp_ptr]\n"
                              ^ "\tjmp GET_BODY(rax)\n"
                              ^ "\tadd rsp, 8*1 ; pop env\n"
                              ^ "\tpop rbx ; pop arg count\n"
                              ^ "\tshl rbx, 3 ; rbx = rbx * 8\n"
                              ^ "\tadd rsp, rbx ; pop args\n"
                              ^ "\tadd rsp, 8\n" ^ "\t;;(*** end of applicTP ***)\n" in
            (pushMagic ^ pushedArgs ^ n ^ operator ^ callClosure)
      | LambdaSimple'(params,body) ->
            let labelFunc = getLabel "Lfunc" counter_Lfunc in
            let labelCode = getLabel "Lcode" counter_Lcode in
            let labelCont = getLabel "Lcont" counter_Lcont in
            let createEnv = (if (depth = (-1))
                            then ("\tmov rsi, SOB_NIL_ADDRESS\n")
                            else (Printf.sprintf "\tMALLOC rsi, (WORD_SIZE*%d)\n" (depth+1)) (*rsi holds ExtEnv ptr*)
                                  ^ "\tmov rdi, qword [rbp + WORD_SIZE*2]\n" ^ (extEnv depth paramsLength) ) in (*rdi holds current env ptr*)
            let createBody = aux_generate (depth+1) (List.length params) body in
            "\t" ^ labelFunc ^ ": ;(LambdaSimple)\n"
            ^ createEnv
            ^ (Printf.sprintf "\tMAKE_CLOSURE(rax, rsi, %s)\n" labelCode)
            ^ (Printf.sprintf "\tjmp %s\n" labelCont)
            ^ (Printf.sprintf "\t%s:\n" labelCode)
            ^ "\tpush rbp\n\tmov rbp, rsp\n"
            ^ createBody
            ^ "\tleave\n" ^ "\tret\n" ^ (Printf.sprintf "\t%s:\n" labelCont) ^ "\t;;(*** end of LambdaSimple ***)\n"
      | LambdaOpt'(params,opt,body) ->
            let labelFunc = getLabel "Lfunc" counter_Lfunc in
            let labelCode = getLabel "Lcode" counter_Lcode in
            let labelCont = getLabel "Lcont" counter_Lcont in
            let createEnv = (if (depth = (-1))
                            then ("\tmov rsi, SOB_NIL_ADDRESS\n")
                            else (Printf.sprintf "\tMALLOC rsi, (WORD_SIZE*%d)\n" (depth+1)) (*rsi holds ExtEnv ptr*)
                                  ^ "\tmov rdi, qword [rbp + WORD_SIZE*2]\n" ^ (extEnv depth paramsLength) ) in (*rdi holds current env ptr*)
            let createBody = aux_generate (depth+1) ((List.length params)+1) body in
            let labelMyLoop = getLabel "myLoop" counter_Lloop in
            let labelEndmyLoop = "end"^labelMyLoop in
            (* let labelEndmyLoop2 = "end2"^labelMyLoop in *)
            let shrinkStack =
              "\tmov rcx, qword [rbp + WORD_SIZE*3]\n" ^
              "\tmov rsi, rcx\n" ^
              (Printf.sprintf "\tsub rcx, %d\n" (List.length params)) ^
              "\tcmp rcx , 0\n" ^
              (Printf.sprintf "\tje %s\n" labelEndmyLoop) ^
              "\tpush rcx\n" ^
              "\tsub rsi, 1\n" ^
              "\tmov rbx, SOB_NIL_ADDRESS\n" ^

              (Printf.sprintf "\t%s:\n" labelMyLoop) ^
              "\tmov rdi, PVAR(rsi)\n" ^
              "\tMAKE_PAIR (rax, rdi, rbx)\n" ^
              "\tmov rbx, rax\n" ^
              "\tsub rsi, 1\n" ^
              (Printf.sprintf "\tloop %s, rcx\n" labelMyLoop) ^

              "\tmov rcx, qword [rbp + WORD_SIZE*3]\n" ^
              "\tsub rcx, 1\n" ^
              "\tmov PVAR(rcx), rax\n" ^

              (Printf.sprintf "\tmov rcx, %d\n" (List.length params)) ^
              "\tinc rcx\n" ^
              "\tmov qword [rbp + WORD_SIZE*3], rcx\n" ^

              "\tpop rdi\n" ^
              "\tsub rdi, 1\n" ^
              "\tshl rdi, 3\n" ^
              "\tadd rdi, rbp\n" ^

              "\tmov rsi, rbp\n" ^

              (Printf.sprintf "\tmov rdx, WORD_SIZE*(4+%d)\n" (List.length params)) ^
              "\tcall memmove\n" ^
              "\tmov rbp, rax\n" ^
              "\tmov rsp, rbp\n" ^
              (Printf.sprintf "\t%s:\n" labelEndmyLoop) in

            "\t" ^ labelFunc ^ ": ;(LambdaSimple)\n"
            ^ createEnv
            ^ (Printf.sprintf "\tMAKE_CLOSURE(rax, rsi, %s)\n" labelCode)
            ^ (Printf.sprintf "\tjmp %s\n" labelCont)
            ^ (Printf.sprintf "\t%s:\n" labelCode)
            ^ "\tpush rbp\n\tmov rbp, rsp\n"
            ^ shrinkStack
            ^ createBody
            ^ "\tleave\n" ^ "\tret\n" ^ (Printf.sprintf "\t%s:\n" labelCont) ^ "\t;;(*** end of LambdaOpt ***)\n"
      | (Box'(var)) ->  let getVar = (aux_generate depth paramsLength (Var'(var))) in
                        let boxing = "\tMALLOC rbx, 8\n"
                                  ^ "\tmov qword [rbx], rax\n"
                                  ^ "\tmov rax, rbx\n" in
                        getVar ^ boxing
      | _ -> raise X_not_yet_implemented in
    (aux_generate (-1) 0 e);;



end;;

