
#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type number =
  | Int of int
  | Float of float;;

type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | TaggedSexpr of string * sexpr
  | TagRef of string;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Int n1), Number(Int n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | TaggedSexpr(name1, expr1), TaggedSexpr(name2, expr2) -> (name1 = name2) && (sexpr_eq expr1 expr2)
  | TagRef(name1), TagRef(name2) -> name1 = name2
  | _ -> false;;

module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct

let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

(* aux general functions: *)
let make_paired nt_left nt_right nt =
  let nt = caten nt_left nt in
  let nt = pack nt (function (_, e) -> e) in
  let nt = caten nt nt_right in
  let nt = pack nt (function (e, _) -> e) in
  nt;;

let make_spaced nt =
  make_paired (star nt_whitespace) (star nt_whitespace) nt;;

(* tuple aux procedeurs: *)
let car (x,y) = x;;
let cdr (x,y) = y;;

(* Aux. parsers: *)

(* parse a bool exp (wraped in spaces) *)
let make_boolean b = match b with
| [] -> raise X_no_match
| car::cdr -> let chr = lowercase_ascii (List.nth b 1) in
              match chr with
              |'t'-> Bool(true)
              |'f'-> Bool(false)
              |_-> raise X_no_match;;

let bool_parser =
  let nt = disj (word_ci "#f") (word_ci "#t") in
  let nt = make_spaced nt in
  let nt = pack nt make_boolean in
  nt;;

(* -> char parser: *)
let make_character c = match c with
| [] -> raise X_no_match
| car::cdr -> let length = List.length c in
              match length with
              |3-> Char((List.nth c 2))
              |_-> let chr = String.sub (list_to_string (List.map lowercase_ascii c)) 2 (length -2 ) in
                   match chr with
                   |"nul" -> Char(Char.chr 0)
                   |"newline" -> Char(Char.chr 10)
                   |"return" -> Char(Char.chr 13)
                   |"tab" -> Char(Char.chr 9)
                   |"page" -> Char(Char.chr 12)
                   |"space" -> Char(Char.chr 32)
                   | _ -> raise X_no_match;;

let char_parser =
  let nt = disj_list (List.map word_ci ["newline"; "nul"; "page"; "return"; "space"; "tab"]) in
  let nt = disj nt ( pack (range '!' '~') (fun (e) ->[e])) in
  let nt = caten (word "#\\") nt in
  let nt = pack nt (fun x-> match x with
                   | (a,b)-> a@b) in
  let nt = make_spaced nt in
  let nt = pack nt make_character in
  nt;;

(* ->   symbol parser: *)
let symbolchar_parser =
  let nt = range '0' '9' in
  let nt = disj nt (range 'a' 'z') in
  let nt = disj nt (range 'A' 'Z') in
  let nt = disj nt (one_of "!$^*-_=+<>?/:") in
  let nt = pack nt lowercase_ascii in
  nt;;

let make_symbol s = Symbol(list_to_string s);;

let symbol_parser =
  let nt = plus symbolchar_parser in
  let nt = pack nt make_symbol in
  make_spaced nt;;

(*  ->   number parser: *)
(* taken from the tutorial -> parses natural numbers in stringList format to int
[5;3;7] -> 537 in decimal *)

let natural_parser =
  let make_nt_digit ch_from ch_to displacement =
    let nt = const (fun ch -> ch_from <= ch && ch <= ch_to) in
    let nt = pack nt (let delta = (Char.code ch_from) - displacement in
		      fun ch -> (Char.code ch) - delta) in
    nt in
  let nt = make_nt_digit '0' '9' 0 in
  let nt = plus nt in
  let nt = pack nt (fun digits ->
		    List.fold_left (fun a b -> 10 * a + b) 0 digits) in
  nt;;

(* returns the sign of a number (if it exists) *)
let sign_parser = pack (maybe (disj (char '+') (char '-')))
    (fun (e)-> match e with
    |Some('+')-> ['+']
    |Some('-')-> ['-']
    |_ -> [] );;

(* (a:= sign , b:= natural number) returns an integer x wrapped in Number(Int(x)):= sexpr  *)
let make_integer i = match i with
| (a,b) -> let sign = let chr = a in
                        match chr with
                        | ['-'] -> (-1)
                        | _ -> 1 in
              Number(Int(b*sign));;

let integer_parser =
  let nt= caten sign_parser natural_parser in
  let nt= pack nt make_integer in
  nt;;

(* ->  453 -> 0.453 takes an integer n and turns it into 0.n float *)
let make_frac n = float_of_string (list_to_string(['0';'.']@n));;

(* parser for the int part of float ("3.14" -> ("3." , "14")) : *)
let leftFloat_parser =
  let nt = caten sign_parser natural_parser in
  let nt = caten nt (word ".") in
  let nt = pack nt car in
  nt;;

let float_parser s =
  let nt = leftFloat_parser in
  let sign = (fun(e)-> match e with |['-']-> (-1.) |_-> 1.) (car (car (nt s))) in
  let nt = pack nt cdr in
  let nt = caten nt (plus (range '0' '9')) in
  let nt = pack nt (fun (e)-> match e with | (a,b)-> (float_of_int a) +. (make_frac b)) in
  let nt = pack nt (fun(e)-> Number(Float(e*.sign))) in
  nt s;;

(* -> Scientific Notaion Parser: 3.14e-4 = 3.14 *(10^-4) = 0.000314  *)
let scientificNotaion_parser =
  let nt = disj float_parser integer_parser in
  let nt = pack nt (fun (e) ->
                    match e with
                    |Number(Int(n)) -> (float_of_int n)
                    |Number(Float(n)) -> n
                    | _ -> raise X_this_should_not_happen) in
  let nt = caten nt (char_ci 'e') in
  let nt = pack nt car in
  let nt = caten nt integer_parser in
  let nt = pack nt (fun (a,b) ->
                    match b with
                    |Number(Int(n))-> (a,(float_of_int n))
                    |_ ->raise X_this_should_not_happen) in
  let nt = pack nt (fun (a, b)-> Number(Float(a*.(10.** b)))) in
  nt;;

(* factory that takes base b and returns a parser for a natural number in base b (returns an int list)
  -> b=16 ; A3C -> [10;3;12] *)
let make_radixDigit_parser b  =
  let digits = "0123456789abcdefghijklmnopqrstuvwxyz"  in
  let radixDigits = string_to_list (String.sub digits 0 b) in
  let radixDigits_parsers = List.map char_ci radixDigits in
  let nt = disj_list radixDigits_parsers in
  let nt = pack nt lowercase_ascii in
  let nt = pack nt (fun(ch)->
                      let displacement = if('0' <= ch && ch <= '9')
                                          then 0
                                          else 10 in
                      if displacement=0
                      then ((Char.code ch) - (Char.code '0'))
                      else (((Char.code ch) - (Char.code 'a')) + displacement)) in
  nt;;

  let make_radixNatural_parser b =
    let nt = make_radixDigit_parser b in
    let nt = plus nt in
    nt;;

(* parser for an int in base b *)
let radixInt_parser b =
  let nt_tmp = make_radixNatural_parser b in
  let nt_tmp = pack nt_tmp (fun digits ->
		    List.fold_left (fun acc curr -> b * acc + curr) 0 digits) in
  let nt = caten sign_parser nt_tmp in
  let nt = pack nt (fun(x, y)-> match x with
                    | ['-'] -> (-1)*y
                    |  _ -> y) in
  let nt = pack nt (fun(e)-> Number(Int(e))) in
  nt;;

(* similar to fold.left with accumulator and index that changes
-> takes base b, int list(if list = A,B,4,F => number=0.AB4F), index=1, acc =0. ->  16,[10,12,4],1,0. -> 0.AC4 in HEX base *)
let rec fracVlaue b numList index acc =
  match numList with
  | [] -> acc
  | car::cdr -> let curr = (float_of_int car) *. ((float_of_int b) ** (float_of_int(index*(-1)))) in
                fracVlaue b cdr (index+1) (acc+.curr);;

let aux_makeRadixFloat (x,y) =
  (float_of_int x) +. y;;

(* parser for a float in base b *)
let radixFloat_parser b s =
  let nt_tmp = make_radixNatural_parser b in
  let nt_tmp = pack nt_tmp (fun digits ->
		    List.fold_left (fun acc curr -> b * acc + curr) 0 digits) in
  let nt = caten sign_parser nt_tmp in
  let nt = caten nt (char '.') in
  let nt = pack nt (function (x, y) -> x) in
  let car (x,y) = x in
  let sign = (fun(e)-> match e with |['-']-> (-1.) |_-> 1.) (car (car (nt s))) in
  let nt = pack nt (fun(x, y)-> y) in
  let nt = caten nt (make_radixNatural_parser b) in
  let nt = pack nt (function (x, y) -> (x , (fracVlaue b y 1 0.) ) ) in
  let nt = pack nt aux_makeRadixFloat in
  let nt = pack nt (fun (e)-> Number(Float(e *. sign))) in
  nt s;;

let radix_parser s =
  let car (a,b) = a in
  let nt = caten (char '#') natural_parser in
  let nt = pack nt (function (a,b)->b) in
  let nt = guard nt (fun (e)-> (e>=2 && e<=36)) in
  let nt = caten nt (char_ci 'R') in
  let nt = pack nt (function (a,b)->a) in
  let base = car (nt s) in
  let radixNumber_parser = disj (radixFloat_parser base) (radixInt_parser base) in
  let nt = caten nt radixNumber_parser in
  let nt = pack nt (function (a,b)-> b) in
  nt s;;

let number_parser =
  let nt_tmp = disj scientificNotaion_parser float_parser in
  let nt_tmp = disj nt_tmp integer_parser in
  let nt_tmp = not_followed_by nt_tmp (diff symbolchar_parser (range '0' '9') ) in
  let nt = disj radix_parser nt_tmp in
  let nt = make_spaced nt in
  nt ;;

(* parses all chars execpt for '"' and '/' *)
let stringLiteralChar_parser =
  let nt = disj (char '\\') (char '\"') in
  let nt = diff nt_any nt in
  nt;;

let stringMetaChar_parser =
  let nt = char '\\' in
  let nt = caten nt (disj_list (List.map char_ci ['\\';'\"';'T'; 'F' ;'N';'R'])) in
  let nt = pack nt
    (fun (a,b)-> match b with
    | ('T'|'t')-> '\t'
    | ('F'|'f')-> Char.chr 12
    | ('N'|'n')-> '\n'
    | ('R'|'r')-> '\r'
    | _ -> b ) in
  nt;;

let stringChar_parser = disj stringLiteralChar_parser stringMetaChar_parser;;

let make_string e = String(e);;

let aux_doubleQuote_parser = word "\"";;

let string_parser =
  let nt = star stringChar_parser in
  let nt = make_paired aux_doubleQuote_parser aux_doubleQuote_parser nt in
  let nt = make_spaced nt in
  let nt = pack nt list_to_string in
  let nt = pack nt make_string in
  nt;;

(* list parsers: *)

let make_Pair (a,b) = Pair(a,b);;

(* create a symbolic Symbol("ToRemove") for values we need to remove from the AST,
 Symbol "ToRemove" is not in lower ascii so there is no conflict with a valid scheme AST of a symbol
 that only comes in lowercase *)
let getNil e = Symbol("ToRemove");;

(* takes an ocaml sexpr list [a1;a2...an] and returns a Pair(a1,Pair(a2,...,Pair(an,Nil))) *)
let rec makeListToPairs lst = match lst with
| [] -> Nil
| car::cdr -> Pair(car,(makeListToPairs cdr));;

(* takes an ocaml sexpr list and sexpr ([a1;a2...an],X) and returns a Pair(a1,Pair(a2,...,Pair(an,X))) *)
let rec makeDottedList (l,x) = match l with
| [a] -> Pair(a,x)
| car::cdr -> Pair(car,(makeDottedList (cdr,x)))
| [] -> raise X_this_should_not_happen ;;

(* main sexpr parser for any kind of scheme expr *)
let rec sexpr_parser s =
  let nt_sexpr = disj_list [bool_parser; char_parser; number_parser; string_parser; symbol_parser;
  list_parser; dottedList_parser; quoted_parser; quasiQuoted_parser; unquoted_parser;
  unquotedAndSpliced_parser; taggedExpr_parser; tag_parser; lineComment_parser; sexprComment_parser] in
  let nt_tmp = star (disj lineComment_parser sexprComment_parser) in
  let nt_sexpr = make_paired nt_tmp nt_tmp nt_sexpr in
  nt_sexpr s

and list_parser s =
  (* let nt = star sexpr_parser in
  let nt = disj (star (disj lineComment_parser sexprComment_parser )) nt in *)
  let nt = star (disj (disj lineComment_parser sexprComment_parser) sexpr_parser) in
  let nt = make_spaced nt in
  let nt = make_paired (char '(') (char ')') nt in
  let nt = make_spaced nt in
  let nt = pack nt (fun (e)-> List.filter (fun (x)-> x<>Symbol("ToRemove")) e) in
  let nt = pack nt makeListToPairs in
  nt s

and dottedList_parser s =
  let nt = plus sexpr_parser in
  let nt = caten nt (char '.') in
  let nt = pack nt car in
  let nt = caten nt sexpr_parser in
  let nt = make_paired (char '(') (char ')') nt in
  let nt = make_spaced nt in
  let nt = pack nt makeDottedList in
  nt s

and quoted_parser s =
  let nt = caten (char '\'') sexpr_parser in
  let nt = pack nt (function (a,b)-> Pair( Symbol("quote") , Pair( b , Nil ))) in
  let nt = make_spaced nt in
  nt s

and quasiQuoted_parser s =
  let nt = caten (char '`') sexpr_parser in
  let nt = pack nt (function (a,b)-> Pair( Symbol("quasiquote") , Pair( b , Nil ))) in
  let nt = make_spaced nt in
  nt s

and unquoted_parser s =
  let nt = caten (char ',') sexpr_parser in
  let nt = pack nt (function (a,b)-> Pair( Symbol("unquote") , Pair( b , Nil ))) in
  let nt = make_spaced nt in
  nt s

and unquotedAndSpliced_parser s =
  let nt = caten (word ",@") sexpr_parser in
  let nt = pack nt (function (a,b)-> Pair( Symbol("unquote-splicing") , Pair( b , Nil ))) in
  let nt = make_spaced nt in
  nt s

and tag_parser s =
  let nt = make_paired (char '{') (char '}') symbol_parser in
  let nt = caten (char '#') nt in
  let nt = pack nt cdr in
  let nt = make_spaced nt in
  nt s

and taggedExpr_parser s =
  let nt = make_spaced (char '=') in
  let nt = caten nt sexpr_parser in
  let nt = pack nt cdr in
  let nt = maybe nt in
  let nt = caten tag_parser nt in
  let nt = pack nt (function (a,b)-> let lhs = match a with | Symbol(x)-> x | _->raise X_this_should_not_happen in
                    match b with
                    |None -> TagRef(lhs)
                    |Some(x) -> TaggedSexpr(lhs , x)) in
  nt s

and lineComment_parser s =
  let nt = diff nt_any (char '\n') in
  let nt = star nt in
  let nt = caten (char ';') nt in
  let nt = caten nt (disj nt_end_of_input (word "\n")) in
  let nt = make_spaced nt in
  let nt = pack nt getNil in
  nt s

and sexprComment_parser s =
  let rec aux_sexprComment_parser s =
      let nt = word "#;" in
      let nt = make_paired nt sexpr_parser aux_sexprComment_parser in
      let nt_tmp = (caten nt nt) in
      let nt_tmp = pack nt_tmp (fun(a,b)-> a@b) in
      let nt = disj nt_tmp nt in
      let nt = disj nt nt_epsilon in
      let nt = make_spaced nt in
      nt s in
  let nt = word "#;" in
  let nt = make_paired nt sexpr_parser aux_sexprComment_parser in
  let nt = make_spaced nt in
  let nt = pack nt getNil in
  nt s;;

(* **  end of sexpr parsers  ** *)

(* takes a Pair(a1,Pair(a2,...,Pair(an,Nil(|an+1)))) and returns [a1;a2;...;an(;an+1)] *)
let rec pairsToList e =
  match e with
  |Pair(x,Nil) -> [x]
  |Pair(x,y) -> [x]@(pairsToList y)
  | x -> [x];;

let rec concatMap func lst s =
  match s with
  | [] -> []
  | car :: cdr -> let newlst = func lst car in
                  newlst @ ( concatMap func newlst cdr);;

(* recurrsive function that finds all tagged expressions in an AST of a single sexpr and raises an exception if it finds
duplicates of the same ref name  *)
let rec findDuplicatesTags l sexp =
  match sexp with
  | TaggedSexpr(a,b) -> (if(List.mem a l)
                       then raise X_this_should_not_happen
                       else let lst = a::l in
                            findDuplicatesTags lst b)
  | Pair(a,b) -> concatMap findDuplicatesTags l (pairsToList sexp)
  | _ -> l;;

(* main functions: *)
let read_sexprs string =
  let chrlist = string_to_list string in
  let program_parser = make_spaced (plus sexpr_parser) in
  let program_parser = disj program_parser (pack (make_spaced(star (disj lineComment_parser sexprComment_parser))) (fun(e)->[])) in
  let tmp = program_parser chrlist in
  match (cdr tmp) with
  |[] ->(let result = car tmp in
        let list = List.map (findDuplicatesTags []) result in
        let resultPair = (result,list) in
        car resultPair)
  |_-> raise X_no_match;;

let read_sexpr string =
  let chrlist = string_to_list string in
  let res = sexpr_parser chrlist in
  match (cdr res) with
  |[] ->(let result = car res in
        let list = findDuplicatesTags [] result in
        let resultPair = (result,list) in
        car resultPair)
  |_-> raise X_no_match;;

end;; (* struct Reader *)
