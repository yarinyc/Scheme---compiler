#use "reader.ml";;
open Reader;;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

(* work on the tag parser starts here *)

(* general aux functions: *)
let car (x,y) = x;;
let cdr (x,y) = y;;

let isProperList p =
  let rec checkPairs pair =
    match pair with
    | Nil -> true
    | Pair(a,b) -> checkPairs b
    | _ -> false in
  match p with
  | Nil -> true
  | Pair(a,b) -> checkPairs p
  | _ -> false;;

(* takes an ocaml sexpr list [a1;a2...an] and returns a Pair(a1,Pair(a2,...,Pair(an,Nil))) *)
let rec listToPairs lst =
  match lst with
  | [] -> Nil
  | car::cdr -> Pair(car,(listToPairs cdr));;

let rec listToPairsImproper lst =
  match lst with
  | [x] -> x
  | car::cdr -> Pair(car,(listToPairsImproper cdr))
  | [] -> Nil;;

let rec pairsToList e =
  match e with
  |Pair(x,Nil) -> [x]
  |Pair(x,y) -> [x]@(pairsToList y)
  |Nil->[]
  | x -> [x];;

(* given an expression e, a nested Pair of symbols, return an ocaml list of all the values of the symbols in that nested list *)
let symbolsToStrings e =
  let lst = pairsToList e in
  let lst = List.map (fun(e) ->
                        match e with
                        | Symbol(x)-> (if(List.mem x reserved_word_list) then raise X_syntax_error else x)
                        | _ -> raise X_syntax_error)
                      lst in
  lst;;

(* given a list, return a pair of the list without the last element, and the last element *)
let cut_last lst =
  let last = List.nth lst ((List.length lst)-1) in
  let rec cut l =
    match l with
    | [a] -> []
    | a::b -> [a]@ (cut b)
    | _ -> [] in
  ((cut lst),last);;

(* gets nested pairs of symbols and returns true if there are no 2 equal symbols: *)
let check_duplicates arglist =
  let rec checkDuplicates nameList lst =
    match lst with
    | [] -> true
    | car::cdr -> (if(List.mem car nameList) then false else (checkDuplicates (car::nameList) cdr) ) in
  let args = pairsToList arglist in
  let names = List.map (fun(e) -> match e with | Symbol(x)->x | _->raise X_syntax_error) args in
  checkDuplicates [] names;;

(* main tag-parser function: *)
let rec tag_parser = function
  (* self evaluated: *)
  | Nil -> raise X_syntax_error
  | Number(x) -> Const(Sexpr(Number(x)))
  | Bool(x) -> Const(Sexpr(Bool(x)))
  | Char(x) -> Const(Sexpr(Char(x)))
  | String(x) -> Const(Sexpr(String(x)))
  (* quoted: *)
  | Pair(Symbol("quote"),Pair(x, Nil)) -> Const(Sexpr(x))
  (* tagged expr: *)
  | TaggedSexpr(x,y) -> (match y with
                          |Pair(Symbol("quote"),Pair(expr, Nil)) -> Const(Sexpr(TaggedSexpr(x,expr)))
                          | _ -> Const(Sexpr(TaggedSexpr(x,y))))
  | TagRef(x) -> Const(Sexpr(TagRef(x)))
  (* var: *)
  | Symbol(x) -> (if(List.mem x reserved_word_list)
                  then raise X_syntax_error
                  else Var(x))
  (* if: *)
  | Pair(Symbol("if"),Pair(test,Pair(thenExp,Pair(elseExp,Nil)))) -> If(tag_parser test, tag_parser thenExp, tag_parser elseExp)
  | Pair(Symbol("if"),Pair(test,Pair(thenExp,Nil))) -> If(tag_parser test, tag_parser thenExp, Const(Void))
  (* lambda: *)
  | Pair(Symbol ("lambda"), Pair(Nil,body)) -> LambdaSimple([],(make_implicit_seq body))
  | Pair(Symbol ("lambda"), Pair(Pair(arg, args), body))
        -> (if(check_duplicates (Pair(arg, args)))
           then (if(isProperList (Pair(arg, args)))
                then (LambdaSimple((symbolsToStrings (Pair(arg, args))),(make_implicit_seq body)))  (*lambda simple*)
                else (let lst = pairsToList (Pair(arg, args)) in  (*lambda opt*)
                      let (arguments,vs) = cut_last lst in
                      let arguments = List.map (fun(e) -> match e with | Symbol(x)-> (if(List.mem x reserved_word_list) then raise X_syntax_error else x) | _ -> raise X_syntax_error) arguments in
                      let vs = (match vs with | Symbol(x)-> (if(List.mem x reserved_word_list) then raise X_syntax_error else x) | _ -> raise X_syntax_error) in
                      LambdaOpt(arguments, vs, (make_implicit_seq body))))
           else raise X_syntax_error)
  | Pair(Symbol ("lambda"), Pair(Symbol(x), body)) -> (if(List.mem x reserved_word_list)
                                                      then raise X_syntax_error
                                                      else LambdaOpt([],x,(make_implicit_seq body)))  (*lambda variadic*)
  (* or: *)
  | Pair(Symbol("or"), Nil) -> Const(Sexpr(Bool(false)))
  | Pair(Symbol("or"), Pair(x, Nil)) -> (tag_parser x)
  | Pair(Symbol("or"), Pair(x, y)) -> (make_or (Pair(x,y)))
  (* and: *)
  | Pair(Symbol("and"), Nil) -> Const(Sexpr(Bool(true)))
  | Pair(Symbol("and"), Pair(x, Nil)) -> (tag_parser x)
  | Pair(Symbol("and"), Pair(x, y)) -> (tag_parser (expansion_and (Pair(x,y))))
  (*define: *)
  | Pair(Symbol "define", Pair(Pair(name, argl), body))
        -> (tag_parser (mitDefine_expansion name argl body))
  | Pair(Symbol("define"),Pair(Symbol(x), Pair(y, Nil))) -> Def((tag_parser (Symbol(x))),(tag_parser y))
  (*set!: *)
  | Pair(Symbol("set!"), Pair(x, Pair(y, Nil))) -> Set((tag_parser x),(tag_parser y))
  (*sequences: *)
  | Pair(Symbol("begin"), Nil) -> Const(Void)
  | Pair(Symbol("begin"), Pair(x, Nil)) -> (tag_parser x)
  | Pair(Symbol("begin"), Pair(x, y)) -> (make_sequence (Pair(x,y)))
  (*let: *)
  | Pair(Symbol ("let"), Pair(Nil, body)) -> tag_parser (expansion_let Nil body)
  | Pair(Symbol ("let*"), Pair(Nil, body)) -> tag_parser (expansion_let Nil body)
  | Pair(Symbol ("let"), Pair(Pair(rib, ribs), body)) -> tag_parser (expansion_let (Pair(rib,ribs)) body)
  | Pair(Symbol ("let*"), Pair(Pair(rib, ribs), body)) -> tag_parser (expansion_letStar (Pair(rib,ribs)) body)
  (*letrec: *)
  | Pair(Symbol ("letrec"), Pair(Nil, body)) -> tag_parser (expansion_let Nil body)
  | Pair(Symbol ("letrec"), Pair(Pair(rib, ribs), body)) -> tag_parser (expansion_letrec (Pair(rib,ribs)) body)
  (* quasiquote: *)
  | Pair(Symbol("quasiquote"),Pair(x,Nil)) -> (quasiquote_expansion x)
  (* cond: *)
  | Pair(Symbol("cond"), ribs) -> tag_parser (expansion_cond ribs)
  (* applic: *)
  | Pair(operator, Nil) -> (make_applic operator Nil)
  | Pair(operator, Pair(x,y)) -> (make_applic operator (Pair(x,y)))
  | _ -> raise X_syntax_error

and make_applic op rands =
  let operands =
    if (isProperList rands)
    then (List.map tag_parser (pairsToList rands))
    else raise X_syntax_error in
  Applic((tag_parser op), operands)

and make_or rands =
  let operands =
    if (isProperList rands)
    then (List.map tag_parser (pairsToList rands))
    else raise X_syntax_error in
  Or(operands)

(* make an explicit sequence (begin ...): *)
and make_sequence rands =
  let operands =
    if (isProperList rands)
    then (List.map tag_parser (pairsToList rands))
    else raise X_syntax_error in
  Seq(operands)

(* make an implicit sequence (body of lambda/let/cond...): *)
and make_implicit_seq body =
  if(isProperList body)
  then (match body with
        | Nil -> raise X_syntax_error  (*imlicit sequence must be non empty*)
        | Pair(x, Nil) -> (tag_parser x)
        | Pair(x, y) -> (if(isProperList body)
                        then Seq(List.map tag_parser (pairsToList body))
                        else raise X_syntax_error)
        | _ -> raise X_syntax_error)
  else raise X_syntax_error

and quasiquote_expansion sexpr =
  let rec expander exp =
    match exp with
    | Pair(Symbol("unquote"), Pair(x,Nil)) -> x
    | Pair(Symbol("unquote-splicing"), Pair(x,Nil)) -> raise X_syntax_error
    | Symbol(x) -> Pair(Symbol("quote"),Pair(exp,Nil))
    | Nil -> Pair(Symbol("quote"),Pair(Nil,Nil))
    | Pair(x,y) -> (match x,y with
                  | Pair(Symbol("unquote-splicing"), Pair(w,Nil)), _ -> Pair(Symbol("append"), Pair(w, Pair((expander y),Nil)))
                  | _, Pair(Symbol("unquote-splicing"), Pair(w,Nil))-> Pair(Symbol("cons"),Pair((expander x),Pair(w,Nil)))
                  | _, _-> Pair(Symbol("cons"),Pair((expander x),Pair((expander y),Nil))))

    | _ -> exp in
  let expandedExp = expander sexpr in
  tag_parser expandedExp

and expansion_let ribs body =
  let rec toTuples ribs =
    match ribs with
    | Nil -> []
    | Pair(Pair(var,Pair(value,Nil)),Nil) -> [(var,value)]
    | Pair(Pair(var,Pair(value,Nil)),rest) -> [(var,value)]@(toTuples rest)
    | _ -> raise X_syntax_error in
  let rec expand_let exp =
    match exp with
    | Pair(Symbol ("let"), Pair(Pair(rib, ribs), body)) -> (expansion_let (Pair(rib,ribs)) body)
    | Pair(x,y) -> Pair(expand_let x, expand_let y)
    | _ -> exp in
  let expander tuples body =
    let params = listToPairs (List.map car tuples) in
    let funcBody = expand_let body in
    let lambda = Pair(Symbol("lambda"),Pair(params , funcBody)) in
    let args = listToPairs (List.map expand_let (List.map cdr tuples)) in
    (Pair(lambda , args)) in
  if(isProperList body)
  then expander (toTuples ribs) body
  else raise X_syntax_error

and expansion_letStar ribs body =
  let (var,value,bool,rest) = match ribs with
                    | Pair(Pair(x,y),Nil) -> (x,y,true,Nil)
                    | Pair(Pair(x,y), rest) -> (x,y,false,rest)
                    | _ -> raise X_syntax_error in
  if(bool)
  then Pair(Symbol("let"),Pair(Pair(Pair(var,value),Nil),body))
  else Pair(Symbol("let"),Pair(Pair(Pair(var,value),Nil),Pair((expansion_letStar rest body),Nil)))

and expansion_letrec ribs body =
  let rec toTuples ribs =
    match ribs with
    | Nil -> []
    | Pair(Pair(var,Pair(value,Nil)),Nil) -> [(var,value)]
    | Pair(Pair(var,Pair(value,Nil)),rest) -> [(var,value)]@(toTuples rest)
    | _ -> raise X_syntax_error in
  let whatever = Pair(Symbol("quote"),Pair(Symbol("whatever"),Nil)) in
  let tuples = toTuples ribs in
  let funcNames = (List.map car tuples) in
  let newBindings = listToPairs (List.map (fun(e) -> Pair(e, Pair(whatever,Nil))) funcNames) in
  let setPart = List.map (fun((x,y)) -> Pair(Symbol("set!"), Pair(x, Pair(y, Nil)))) tuples in
  let lastElement = body in
  let newBody =  listToPairsImproper (setPart@[lastElement]) in
  Pair(Symbol("let"), Pair(newBindings, newBody))

and expansion_cond ribs =
  let getf exp =
    match exp with
    | Pair(x, Nil) -> Pair(Symbol("lambda"), Pair(Nil, Pair(x, Nil)))
    | _ -> raise X_syntax_error in
  let ribsList = pairsToList ribs in
  let check = let length = (List.length ribsList) in
              let filtered = List.filter isProperList ribsList in
              if(length = (List.length filtered)) then true else false in
  let rec expander ribsList =
    match ribsList with
    | [] -> Pair(Symbol("begin"),Nil)
    | car::cdr -> (match car with
                  | Pair(Symbol("else"), rest) -> Pair(Symbol("begin"),rest)
                  | Pair(x, Pair(Symbol("=>"), rest))
                  -> (let f = getf rest in
                      let valueBinding = Pair(Symbol("value"), Pair(x, Nil)) in
                      let fBinding = Pair(Symbol("f"), Pair(f, Nil)) in
                      let restLambda = Pair(Symbol("lambda"), Pair(Nil, Pair((expander cdr), Nil))) in
                      let restBinding = Pair(Symbol("rest"), Pair(restLambda, Nil)) in
                      let dit = Pair(Pair(Symbol("f"),Nil),Pair(Symbol("value"),Nil)) in
                      (match cdr with
                      | [] -> (let body = Pair(Symbol("if"), Pair(Symbol("value"),Pair(dit,Nil))) in
                              let bindings = Pair(valueBinding,Pair(fBinding,Nil)) in
                              Pair(Symbol("let"),Pair(bindings,Pair(body,Nil))))
                      | _ ->  (let dif = Pair(Symbol("rest"),Nil) in
                              let body = Pair(Symbol("if"), Pair(Symbol("value"),Pair(dit, Pair(dif, Nil)))) in
                              let bindings = Pair(valueBinding,Pair(fBinding,Pair(restBinding, Nil))) in
                              Pair(Symbol("let"),Pair(bindings,Pair(body,Nil))))))
                  | Pair(x, rest) -> Pair(Symbol("if"),Pair(x,Pair(Pair(Symbol("begin"),rest),Pair((expander cdr),Nil))))
                  | _ -> raise X_syntax_error) in
  if(check)
  then (expander ribsList)
  else raise X_syntax_error

and expansion_and args =
  match args with
  | Pair(x,Nil) -> x
  | Pair(x,y) -> Pair(Symbol "if", Pair(x, Pair((expansion_and y), Pair(Bool(false), Nil))))
  | _ -> raise X_syntax_error

and mitDefine_expansion name argl body =
  let lambda = Pair(Symbol("lambda"),Pair(argl,body)) in
  Pair(Symbol("define"),Pair(name,Pair(lambda,Nil)));;

(* main functions: *)
let tag_parse_expression sexpr = tag_parser sexpr;;

let tag_parse_expressions sexpr = List.map tag_parser sexpr;;

end;; (* struct Tag_Parser *)
