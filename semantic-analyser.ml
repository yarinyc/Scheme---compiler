#use "tag-parser.ml";;
open Tag_Parser;;
type var =
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of expr' * expr'
  | Def' of expr' * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;


exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct
(* module Semantics = struct *)

(* return the first element of a list *)
let first = function
  |car::cdr -> car
  |_ -> raise X_syntax_error;;

(* given a list, return a pair of the list without the last element, and the last element *)
let splitLast lst =
  let last = List.nth lst ((List.length lst)-1) in
  let rec cut l =
    match l with
    | [a] -> []
    | a::b -> [a]@ (cut b)
    | _ -> [] in
  ((cut lst),last);;

let annotate_lexical_addresses e =
  let rec annotater seenVars exp =
    match exp with
    | Const(x) -> Const'(x)
    | Var(x) -> (annotateVar seenVars x)
    | If(x,y,z) -> If'((annotater seenVars x),(annotater seenVars y),(annotater seenVars z))
    | Seq(exps) -> Seq'(List.map (annotater seenVars) exps)
    | Set(x,y) -> Set'((annotater seenVars x),(annotater seenVars y))
    | Def(x,y) -> Def'((annotater seenVars x),(annotater seenVars y))
    | Or(exps) -> Or'(List.map (annotater seenVars) exps)
    | LambdaSimple(varNames, body) -> (annotateLambda seenVars varNames [] body)
    | LambdaOpt(varNames, varopt, body) -> (annotateLambda seenVars varNames [varopt] body)
    | Applic(op,exps) -> Applic'((annotater seenVars op),(List.map (annotater seenVars) exps))

  (* assume seenVars looks like this:  [ (varName, bound/param, Major, minor) ,...] *)
  (* given all seen vars in the current environment, annotate var *)
  and annotateVar seenVars var =
    match seenVars with
    | [] -> Var'(VarFree(var))
    | car::cdr -> (match car with
                    | (varName,"bound",major,minor) -> if(varName=var)
                                                      then Var'(VarBound(var,major,minor))
                                                      else annotateVar cdr var
                    | (varName,_,_,minor) -> if(varName=var)
                                            then Var'(VarParam(var,minor))
                                            else annotateVar cdr var)

  and annotateLambda seenVars varNames varopt body =
    (* update current env -> all params become bound with major 0 and  bound.major = major+1 *)
    let rec updateEnv seenVars =
      (match seenVars with
      | [] -> [] (*add the new record of varname to the environment*)
      | car::cdr -> (let (currentName,bound,maj,min) = (match car with
                                                      | (var,bound,maj,min) -> (var,bound,maj,min)) in
                    [(currentName,"bound",(maj+1),min)]@(updateEnv cdr))) in
    let rec extendEnv seenVars varName minor =
      (match seenVars with
      | [] -> [(varName,"param",-1,minor)] (*add new record of varName to environment*)
      | car::cdr -> (let (currentName,bound,maj,min) = (match car with
                                                      | (var,bound,maj,min) -> (var,bound,maj,min)) in
                      if (currentName = varName)
                      then (extendEnv cdr varName minor) (* delete current record of varname from the environment*)
                      else [car]@(extendEnv cdr varName minor))) in (* update current record of currentName in the environment *)
    let rec run seenVars vars minor =
      (match vars with
      | [] -> seenVars
      | [varName] -> (extendEnv seenVars varName minor)
      | car::cdr -> run (extendEnv seenVars car minor) cdr (minor+1)) in

    let updatedEnv = (updateEnv seenVars) in
    let extendedEnv = (run updatedEnv (varNames@varopt) 0)in
    if (varopt = [])
    then LambdaSimple'(varNames ,(annotater extendedEnv body))
    else LambdaOpt'(varNames, (first varopt) ,(annotater extendedEnv body)) in

  (* body of annotate_lexical_addresses: *)
  annotater [] e;;

let annotate_tail_calls e =
  let rec annotater in_tp e =
    match e with
    | Const'(x) -> e
    | Var'(x) -> e
    | If'(test,dit,dif) -> If'((annotater false test), (annotater in_tp dit), (annotater in_tp dif))
    | Seq'(exps) -> let (exps,exp)= splitLast exps in
                    Seq'((List.map (annotater false) exps)@[(annotater in_tp exp)])
    | Set'(var,exp) -> Set'((annotater false var), (annotater false exp))
    | Def'(var,exp) -> Def'((annotater false var), (annotater false exp))
    | Or'(exps) -> let (exps,exp)= splitLast exps in
                   Or'((List.map (annotater false) exps)@[(annotater in_tp exp)])
    | LambdaSimple'(params,body) -> LambdaSimple'(params,(annotater true body))
    | LambdaOpt'(params,optParam,body) -> LambdaOpt'(params, optParam, (annotater true body))
    | Applic'(op, args) -> if(in_tp)
                           then (ApplicTP'((annotater false op), (List.map (annotater false) args)))
                           else (Applic'((annotater false op), (List.map (annotater false) args)))
    | _ -> raise X_syntax_error in
  (* body of annotate_tail_calls: *)
  annotater false e;;

(* given 2 tupples, merge t1.x1 with t2.x2 and merge t1.y1 with t2.y2 *)
let mergeTuples t1 t2 =
  match t1,t2 with
  | (x1,y1),(x2,y2) -> (x1@x2, y1@y2);;

(* similar to map only it can maintain a counter for lambda occurences , and in case of if,seq,or and applic maintains the correctness of the counter *)
let rec map_with_counter f envIndex param counter lst =
  match lst with
  | [] -> []
  | car::cdr -> match car with
                | LambdaSimple'(p,b) -> (f envIndex param counter car)::(map_with_counter f envIndex param (counter+1) cdr)
                | LambdaOpt'(p,opt,b) -> (f envIndex param counter car)::(map_with_counter f envIndex param (counter+1) cdr)
                | Seq'(exps) -> (map_with_counter f envIndex param counter (exps@cdr))
                | Or'(exps) -> (map_with_counter f envIndex param counter (exps@cdr))
                | Applic'(op,exps) -> (map_with_counter f envIndex param counter ((op::exps)@cdr))
                | ApplicTP'(op,exps) -> (map_with_counter f envIndex param counter ((op::exps)@cdr))
                | If'(test,dit,dif) -> (map_with_counter f envIndex param counter ([test;dit;dif]@cdr))
                | Set'(var,exp) -> let varResult = (match var with
                                          | Var'(VarParam(name,_)) -> if (name=param)
                                                                      then ([],[envIndex])
                                                                      else ([],[])
                                          | Var'(VarBound(name,_,_)) -> if (name=param)
                                                                      then ([],[envIndex])
                                                                      else ([],[])
                                          | _ -> ([],[])) in
                                          varResult::((map_with_counter f envIndex param counter (exp::cdr)))
                | _ -> (f envIndex param counter car)::(map_with_counter f envIndex param counter cdr);;

  (* main aux function for box_set: *)
  let rec box_setter e =
    match e with
    | Const'(x) -> e
    | Var'(x) -> e
    | Box'(x) -> e
    | BoxGet'(x) -> e
    | If'(test,dit,dif) -> If'((box_setter test),(box_setter dit),(box_setter dif))
    | Seq'(exps) -> Seq'(List.map box_setter exps)
    | BoxSet'(var,exp) -> BoxSet'(var,(box_setter exp))
    | Set'(var,exp) -> Set'((box_setter var),(box_setter exp))
    | Def'(var,exp) -> Def'((box_setter var),(box_setter exp))
    | Or'(exps) -> Or'(List.map box_setter exps)
    | LambdaSimple'(params,body) -> let boxedLambdaBody = boxLambda params body in
                                    LambdaSimple'(params, (box_setter boxedLambdaBody))
    | LambdaOpt'(params,optParam,body) -> let boxedLambdaBody = boxLambda (params@[optParam]) body in
                                          LambdaOpt'(params, optParam, (box_setter boxedLambdaBody))
    | Applic'(op, args) -> Applic'((box_setter op),(List.map box_setter args))
    | ApplicTP'(op,args) -> ApplicTP'((box_setter op),(List.map box_setter args))

  and boxLambda params body =
    (* returns a tupple: int list list(all get occurences) * int list list(all set occurences)
    each occurence of a get or set is represented by a unique id of it's parent lambda
    example: (lambda(x) x:0 (lambda() x:1 (lambda() x:11)) (lambda() x:2)) *)
    let rec getParamOccurrences envIndex param count e =
      match e with
      | Const'(x) -> ([],[])
      | Var'(x) -> (match x with
                  | VarParam(name,_) -> if (name=param)
                                              then ([envIndex],[])
                                              else ([],[])
                  | VarBound(name,_,_) -> if (name=param)
                                              then ([envIndex],[])
                                              else ([],[])
                  | VarFree(_) -> ([],[]))
      | Box'(x) -> ([],[])
      | BoxGet'(x) -> ([],[])
      | If'(test,dit,dif) -> List.fold_left mergeTuples ([],[]) (map_with_counter getParamOccurrences envIndex param count [test;dit;dif])
      | Seq'(exps) -> List.fold_left mergeTuples ([],[]) (map_with_counter getParamOccurrences envIndex param count exps)
      | BoxSet'(var,exp) -> (getParamOccurrences envIndex param count exp)
      | Set'(var,exp) -> let varResult = (match var with
                                          | Var'(VarParam(name,_)) -> if (name=param)
                                                                      then ([],[envIndex])
                                                                      else ([],[])
                                          | Var'(VarBound(name,_,_)) -> if (name=param)
                                                                      then ([],[envIndex])
                                                                      else ([],[])
                                          | _ -> ([],[])) in
                        mergeTuples varResult (getParamOccurrences envIndex param count exp)
      | Or'(exps) -> List.fold_left mergeTuples ([],[]) (map_with_counter getParamOccurrences envIndex param count exps)
      | LambdaSimple'(params,body) -> if(List.mem param params)
                                      then ([],[])
                                      else getParamOccurrences (envIndex@[count]) param 1 body
      | LambdaOpt'(params,optParam,body) -> if(List.mem param (optParam::params))
                                            then ([],[])
                                            else getParamOccurrences (envIndex@[count]) param 1 body
      | Applic'(op, args) -> List.fold_left mergeTuples ([],[]) (map_with_counter getParamOccurrences envIndex param count (op::args))
      | ApplicTP'(op,args) -> List.fold_left mergeTuples ([],[]) (map_with_counter getParamOccurrences envIndex param count (op::args))
      | _ -> raise X_syntax_error in

    (* checks for a single parameter if it should be boxed in body*)
    let shouldBox body param=
      let auxFunc e = if (e=[]) then [0] else e in
      let (getVars, setVars) = getParamOccurrences [] param 1 body in
      let (getVars, setVars) = ((List.map auxFunc getVars),(List.map auxFunc setVars)) in
      let rec findMatch getVar setVars =
        match setVars with
        | [] -> false
        | car::cdr -> (if(car = getVar)
                      then false
                      else (if ((first car)=(first getVar))
                            then false
                            else true)) || (findMatch getVar cdr) in
      let rec findMatches getVars setVars =
        match getVars with
        | [] -> false
        | car::cdr -> (findMatch car setVars) || (findMatches cdr setVars) in

      (findMatches getVars setVars) in

    (* runs shouldBox on every parameter and returns list of boolean *)
    let shouldBoxAll params body =
      (List.map (shouldBox body) params) in

    (* each occurence of param is wrapped with BoxGet' or BoxSet' *)
    let rec boxVar param body =
      match body with
      | Const'(x) -> body
      | Var'(x) ->  (match x with
                  | VarParam(name,_) -> if (name=param)
                                              then BoxGet'(x)
                                              else body
                  | VarBound(name,_,_) -> if (name=param)
                                              then (BoxGet'(x))
                                              else body
                  | VarFree(_) -> body)
      | Box'(x) -> body
      | BoxGet'(x) -> body
      | If'(test,dit,dif) -> If'((boxVar param test),(boxVar param dit),(boxVar param dif))
      | Seq'(exps) -> Seq'(List.map (boxVar param) exps)
      | BoxSet'(var,exp) -> BoxSet'(var,(boxVar param exp))
      | Set'(var,exp) -> let (varName,v) = (match var with
                                      | Var'(VarParam(name,minor)) -> (name,(VarParam(name,minor)))
                                      | Var'(VarBound(name,major,minor)) -> (name,(VarBound(name,major,minor)))
                                      | Var'(VarFree(name)) -> (name,(VarFree(name)))
                                      | _ -> raise X_syntax_error) in
                         if(varName = param)
                         then BoxSet'(v,(boxVar param exp))
                         else Set'((boxVar param var),(boxVar param exp))
      | Def'(var,exp) -> Def'((boxVar param var),(boxVar param exp))
      | Or'(exps) -> Or'(List.map (boxVar param) exps)
      | LambdaSimple'(params,body) -> if(List.mem param params)
                                      then LambdaSimple'(params,body)
                                      else LambdaSimple'(params, (boxVar param body))
      | LambdaOpt'(params,optParam,body) -> if(List.mem param (optParam::params))
                                            then LambdaOpt'(params,optParam,body)
                                            else LambdaOpt'(params, optParam, (boxVar param body))
      | Applic'(op, args) -> Applic'((boxVar param op),(List.map (boxVar param) args))
      | ApplicTP'(op,args) -> ApplicTP'((boxVar param op),(List.map (boxVar param) args)) in

    (* returns a set statement for the begining of the lambda's body *)
    let addBox param minor =
      (Set'(Var'(VarParam(param, minor)),Box'(VarParam(param, minor)))) in

    (* creates a list of set statements for each boxed parameter *)
    let rec addSeq params boolList counter =
      match params, boolList with
      | [],[] -> []
      | car1::cdr1, car2::cdr2 -> if(car2 = true)
                                  then (addBox car1 counter)::(addSeq cdr1 cdr2 (counter+1))
                                  else (addSeq cdr1 cdr2 (counter+1))
      | _,_ -> [] in

    (* runs boxVar for each parameter that needs to be boxed *)
    let rec boxVars params boolList body =
      match params, boolList with
      | [],[] -> body
      | car1::cdr1, car2::cdr2 -> if(car2 = true)
                                  then (boxVars cdr1 cdr2 (boxVar car1 body))
                                  else (boxVars cdr1 cdr2 body)
      | _,_ -> body in

    let boolList = shouldBoxAll params body in
    let boxedBody = boxVars params boolList body in
    let setBindings = addSeq params boolList 0 in
    let newBody = if ((List.length setBindings) > 0) then Seq'(setBindings@[boxedBody]) else boxedBody in
    newBody

let box_set e = (box_setter e);;

let run_semantics expr =
  (* box_set *)
    (* (annotate_tail_calls *)
       (annotate_lexical_addresses expr);;

end;; (* struct Semantics *)