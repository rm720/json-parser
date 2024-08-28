(*TODO:
1. Remove redundaunt stuff
2. Make definitions neater
3. Fix names so they self explanotary
4. Put recursion where possible
5. add comprehensive tests
6. Termination proofs
7. Write descriptimn in the begining
 *)



(* Imported *)
open stringTheory; (* string *)
open listTheory; (* LENGTH_CONS TAKE*)
open extra_stringTheory; (* EXTRACT *)

(* Drafting *)     
open jsonLangTheory;
open mlstringTheory;

(*
Not imported 
open PSLPathTheory; (* CONS_def *)
open arithmeticTheory; (* SUC_ONE_ADD *)
open sexpcodeTheory; (* STRING_def*)
open source_valuesTheory; (* option_def *)
open optionTheory; (* SOME THE NONE*)
*)


(*
Record Datatype for the parser domain.
Input: {Location: position where parsing starts of the type natural number, String: source string to parse}
*)
Datatype:
  Input = <| Location : num;
             String: string;
          |>
End

(*
Define a datatype for the parsing Error.
ParserError is a Constructor that takes a position of parse problem of type natural number and a error message of type string.
*)
Datatype:
  ParserError = ParserError num string
End

(*
Output is Alternative datatype for parser Codomain
Alternatives are Falure or Success.
Failure constructor takes a variable of the type ParseError. Defined above.
Success constructor takes a pair of variables. First one is of the type Input and second one is of the abstract type alpha.
*)
Datatype:
  Output = Failure ParserError | Success (Input # α)
End

(*
Abstract parser: record with one field run. run is a function from Input to 
 *)
Datatype:
  Parser = <| run: Input -> α Output |>
End

                   
Definition inputUncons_def:
  inputUncons input =
  if (LENGTH(input.String) > 0) then
    let input' = Input (input.Location + 1) (TL input.String);
        x = HD input.String
    in SOME (x, input')
  else NONE
End


Theorem cons_lenght_thm:
  ∀s x xs. (LENGTH s > 0) ⇒ LENGTH (TL s) < LENGTH s
Proof
  fs[LENGTH_TL]
QED
 

Theorem input_thm:
  ∀s input. input = Input l s ⇒ input.String = s
Proof
  rw[]
QED
   
   
Theorem inputUncons_length_thm:
  ∀x xs input input'. inputUncons input = SOME (x, input') ⇒ LENGTH(input'.String) < LENGTH(input.String)
Proof
  rw[]>>
  fs[inputUncons_def]>>
  metis_tac[input_thm, cons_lenght_thm]
QED


Theorem inputUncons_some_thm:
  ∀ input. IS_SOME (inputUncons input) ⇒ LENGTH input.String > 0
Proof
  rw[]>>
  fs[inputUncons_def]>>
  spose_not_then assume_tac >>
  fs[]   
QED
        
   
Datatype:
  JsonValue = JsonNull
             | JsonBool bool
             | JsonNumber num
             | JsonString string
             | JsonArray (JsonValue list)
             | JsonObject ((string # JsonValue) list)
End


Datatype:
  JsonValue = JsonNull
             | JsonBool bool
             | JsonNumber int
             | JsonString string
             | JsonArray (JsonValue list)
             | JsonObject ((string # JsonValue) list)
End


Definition char_parser_def:
  char_parser x =
  Parser (λ input.
            let r = inputUncons input
            in 
              if (IS_SOME r) then
                (
                if (FST (THE r)) = x then
                  Success ((SND (THE r)), x)
                else
                  Failure (ParserError (input.Location) "E")
                )
              else
                Failure (ParserError (input.Location) "E")
         )
End


Theorem char_parser_success_thm:
  ∀input input' c. (char_parser c).run input = Success (input', parsed) ⇒ LENGTH(input.String) > 0
Proof
  rw[]>>
  fs[char_parser_def]>>
  Cases_on ‘inputUncons input’ >| [
    fs[]
    ,
    fs[]>>
    Cases_on ‘FST x = c’ >| [
        fs[]>>
        fs[inputUncons_some_thm]
        ,
        fs[inputUncons_some_thm]
      ]
  ]
QED
        
Theorem char_parser_length_thm:
  ∀input input' c parsed. (char_parser c).run input = Success (input', parsed) ⇒ LENGTH(input'.String) < LENGTH(input.String)
Proof
  rw[]>>
  fs[char_parser_def]>>
  Cases_on ‘IS_SOME (inputUncons input)’ >|
  [
    fs[]>>
    Cases_on ‘FST (THE (inputUncons input)) = c’ >|
    [
      fs[]>>
      fs[inputUncons_def]>>
      fs[]>>
      Cases_on ‘STRLEN input.String > 0’ >|
      [
        fs[]>>
        rw[LENGTH_TL]
        ,
        fs[]
      ]
      ,
      fs[]
    ]
    ,
    fs[]
  ]
QED
        
                                                      
(*returns v if p was successul *)
Definition const_parser_def:
  const_parser v p =
  Parser (λ input.
      case p.run input of
        Success (rest, _) => Success (rest, v)
      | Failure err => Failure err)
End

        
Overload "<$>"[local] = “const_parser”;
val _ = set_fixity "<$>" (Infixl 550);


Theorem const_parser_length_thm:
  ∀p input input' c. (const_parser v (char_parser c)).run input = Success (input', v) ⇒ LENGTH(input'.String) < LENGTH(input.String)
Proof
  rw[]>>
  fs[const_parser_def]>>
  Cases_on ‘(char_parser c).run input’ >|
  [
    fs[]
    ,
    fs[]>>
    Cases_on ‘p’ >|
    [
      fs[]>>
      metis_tac[char_parser_length_thm]
    ]
  ]
QED
   

(* Parser optional whitespase *)
Definition whitespace_parser_def:
  whitespace_parser = const_parser "" (char_parser #" ")
End

Theorem whitespace_parser_length_thm:
  ∀ input input'. whitespace_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  rw[]>>
  fs[whitespace_parser_def]>>
  fs[const_parser_def]>>
  Cases_on ‘(char_parser #" ").run input’ >|
  [
    fs[]
    ,
    fs[]>>
    Cases_on ‘p’ >|
    [
      fs[]>>
      metis_tac[char_parser_length_thm]
    ]
  ]
QED

        
Definition whitespace_loop_helper_def:
  whitespace_loop_helper input =
  case (whitespace_parser.run input) of
    Success (input', _) => whitespace_loop_helper input'
  | Failure _ => Success (input, "")                            
Termination
  WF_REL_TAC ‘measure (λ input. LENGTH(input.String))’ >>
  rw[whitespace_parser_length_thm]
End       

Definition many_whitespace_parser_def:
  many_whitespace_parser = Parser (λ input. whitespace_loop_helper input)
End
          

(* OR-parser *)
Definition alt_parser_def:
  alt_parser p1 p2 =
    Parser (λ input.
      case p1.run input of
        Failure _ => p2.run input
      | Success _ => p1.run input)
End

Overload "<|>"[local] = “alt_parser”;
val _ = set_fixity "<|>" (Infixl 570);
       

Definition string_parser_joiner_def:
  string_parser_joiner p = λ output.
                             case output of
                               (* if the input is good then apply parser *)
                               Success (input1, parsed1) =>
                                 (
                                 case p.run(input1) of
                                   (* if parsed succeeds then attach the input to the result and return *)
                                   Success (input2, parsed2)  => Success (input2, (parsed1 ++ [parsed2]))
                                 (* if parser fails the return the original input *)
                                 |  Failure err => output)
                             (* if input is bad then return it as it is*)
                             | Failure err => Failure err
End


        

Definition SWAP_ARGS_def:
  SWAP_ARGS f = λx y. f y x
End

        
Definition string_parser_def:
  string_parser s =
  Parser (λ input.
            case (FOLDL (SWAP_ARGS string_parser_joiner) (Success (input, "")) (MAP char_parser s)) of 
              Success (input', parsed) =>
                (case input'.String of
                   "" => Success (input', parsed)
                 | _ => Failure (ParserError input'.Location ("Expected '" ++ s ++ "', but found '" ++ input.String ++ "'"))
                )
            | Failure (ParserError location message) => Failure (ParserError location ("Expected '" ++ s ++ "', but found '" ++ input.String ++ "'"))
         )                          
End


Definition true_parser_def:
  true_parser =
  Parser (λ input.
            if LENGTH input.String >= 4 then
              case (string_parser "true").run (Input input.Location (TAKE 4 input.String))  of 
                Success (input'', "true") => Success ((Input input''.Location (DROP 4 input.String)), JsonBool T)
              | Failure e => Failure e
            else Failure (ParserError input.Location "Expected string of length grater than 3 but found shorter")
         )                          
End

Definition false_parser_def:
  false_parser =
  Parser (λ input.
            if LENGTH input.String >= 5 then
              case (string_parser "false").run (Input input.Location (TAKE 5 input.String))  of 
                Success (input'', "false") => Success ((Input input''.Location (DROP 5 input.String)), JsonBool F)
              | Failure e => Failure e
            else Failure (ParserError input.Location "Expected string of length grater than 4 but found shorter")
         )                          
End

        
Definition jsonBool_parser_def:
  jsonBool_parser = true_parser <|> false_parser                       
End
        

Definition jsonNull_parser_def:
  jsonNull_parser =
  Parser (λ input.
            if LENGTH input.String >= 4 then
              case (string_parser "null").run (Input input.Location (TAKE 4 input.String))  of 
                Success (input'', "null") => Success ((Input input''.Location (DROP 4 input.String)), JsonNull)
              | Failure e => Failure e
            else Failure (ParserError input.Location "Expected string of length grater than 3 but found shorter")
         )                          
End


Definition first_is_minus_def:
  first_is_minus s = case s of
                       "" => F
                     | _ => SUBSTRING (s, 0, 1) = "-"     
End

        
Definition first_is_digit_def:
  first_is_digit s = case s of
                       "" => F
                     | _ => isDigit (EL 0(s))           
End

Definition extract_first_digits_def:
  extract_first_digits s = if first_is_digit s then EL 0 (TOKENS (λ c. ~ (isDigit c)) s)
                           else ""
End

EVAL“extract_first_digits "123 000"”;
EVAL“(char_parser #"0").run  (Input 0 "0") ”;
type_of“char_parser”;

Definition zero_parser_def:
  zero_parser = const_parser "" (char_parser #"-")
End

Definition zero_parser_def:
  zero_parser = const_parser 0:int (char_parser #"0")
End

        
Definition character_parser_def:
  character_parser c v = (λ x. if c = x then SOME v else NONE)                                              
End

(* for p in parsers 
       if *)        

type_of“(character_parser #"0" (0:int))”
EVAL“(character_parser #"0" (0:int)) #"0"”;  
        
(*returns v if p was successul *)
Definition const_parser_def:
  const_parser v p =
  Parser (λ input.
      case p.run input of
        Success (rest, _) => Success (rest, v)
      | Failure err => Failure err)
End        
        

Definition minus_parser_def:
  minus_parser = const_parser "" (char_parser #"-")
End

(* assume the input is a string of digints with optional leading minus *)
Definition toInt_def:
  toInt s = if (first_is_minus s) then 0-t
End

Definition toInt_def:
  toInt s = if (first_is_minus s) then 0-t
EndDefinition

        
EVAL“LENGTH "1234"”;
EVAL“SUBSTRING ("1234", 0, 4)”  ;
EVAL“ -1:int * (toNum "4"):int ”;


toNum parsed_digits_string
        

type_of“minus_parser.run”;
EVAL “minus_parser.run (Input 0 "-123")”;
type_of“minus_parser.run”;
EVAL“first_is_digit "1"”;

EVAL“(0-2):int”;
type_of“(0-2):int”;
type_of“(3:num):int”;


Definition integer_parser_precursor_def:
  integer_parser_precursor input = if first_is_digit input.String then
                                     (
                                        


                                      case minus_parser.run input of
                                        
End  


(* TODO redo using recursion *)
Definition jsonNumber_parser_def:
  jsonNumber_parser = Parser (λ input.
                                case input of
                                  Input location "" => Failure (ParserError location ("Expected digits, but reached end of string"))
                                | Input location1 string1 =>
                                    let parsed_digits_list = extract_first_digits string1
                                    in
                                      case parsed_digits_list of
                                        "" =>
                                          let first_character_string = SUBSTRING (input.String, input.Location, 1)
                                          in
                                            Failure (ParserError location1 ("Expected digits, but found '" ++ first_character_string ++ "'"))
                                            | parsed_digits_string =>
                                                let string2 = EXTRACT (string1, (LENGTH parsed_digits_list), NONE)
                                                in
                                                  Success (Input (location1 + LENGTH parsed_digits_string) string2,  (JsonNumber (toNum parsed_digits_string)))
                                                  | _ => Failure (ParserError location ("Expected digits, but found '" ++ input.String ++ "'"))
                             )
End


EVAL“jsonNumber_parser.run (Input 0 "123Something-Else")”;



        
        
Definition parser_sequenser_string_def:
  parser_sequenser_string p2 p1 =
  Parser (λ input1.
            case p1.run input1 of
              Success (input2, parsed1) =>
                (
                case p2.run input2 of
                  Success (input3, parsed2) =>
                    let
                      parsed = "" ++ parsed1 ++ parsed2
                    in
                        Success (input3, parsed)
                | Failure err => Failure err
                )
            | Failure err => Failure err
         )
End
(* Overloading for short-hand notation *)
Overload "<&>"[local] = “parser_sequenser_string”;
val _ = set_fixity "<&>" (Infixl 520);


Definition special_char_parser_def:
  special_char_parser = const_parser "" (char_parser (CHR 34))
End


Definition parse_if_def:
  parse_if desc pred =
    Parser (λ input.
      case inputUncons input of
        NONE => Failure (ParserError (input.Location) ("Expected " ++ desc ++ ", but reached end of string"))
      | SOME (c, rest) =>
          if pred c then
            Success (rest, c)
          else
            Failure (ParserError (input.Location) ("Expected " ++ desc ++ ", but found '" ++ [c] ++ "'")))
End


Definition normal_char_parser_def:
  normal_char_parser =
    parse_if "non-special character" (λ c. c ≠ #"\"" ∧ c ≠ #"\\")
End     


(* TODO redo using recursion *)
(* TODO generalise and call "many". I am  not sure if this needed*)
Definition normal_string_parser_def:
  normal_string_parser =
  Parser (
    λ input. FOLDL (SWAP_ARGS string_parser_joiner) (Success (input, "")) (REPLICATE (LENGTH input.String) normal_char_parser)
    )
End


Definition stringliteral_parser_def:
  stringliteral_parser = Parser (λ input.
                                case (special_char_parser <&> (normal_string_parser <&> special_char_parser)).run input of
                                  Success (input', parsed_string) =>  Success (input', parsed_string)
                                | Failure err => Failure err
                             )
End


Definition jsonString_parser_def:
  jsonString_parser = Parser (λ input.
                                case (special_char_parser <&> (normal_string_parser <&> special_char_parser)).run input of
                                  Success (input', parsed_string) =>  Success (input', JsonString parsed_string)
                                | Failure err => Failure err
                             )
End



(* Array parser *)

(* Consumes a compulsory single comma *)
Definition comma_parser_def:
  comma_parser = const_parser "" (char_parser #",")
End    
        
(* consumes a compulsory single comma surrounded by optional whitespaces. E.g.: "     ,     "  *)
Definition separator_parser_def:
  separator_parser = (many_whitespace_parser <&> (comma_parser <&> many_whitespace_parser))
End
        
Definition open_bracket_parser_def:
  open_bracket_parser = (many_whitespace_parser <&> ((const_parser "" (char_parser #"[")) <&> many_whitespace_parser))
End

Definition closed_bracket_parser_def:
  closed_bracket_parser = (many_whitespace_parser <&> ((const_parser "" (char_parser #"]")) <&> many_whitespace_parser))
End  

(* Consumes a compulsory single colon *)
Definition colon_parser_def:
  colon_parser = const_parser "" (char_parser #":")
End

Definition open_brace_parser_def:
  open_brace_parser = (many_whitespace_parser <&> ((const_parser "" (char_parser #"{")) <&> many_whitespace_parser))
End

Definition closed_brace_parser_def:
  closed_brace_parser = (many_whitespace_parser <&> ((const_parser "" (char_parser #"}")) <&> many_whitespace_parser))
End

Definition separator_colon_parser_def:
  separator_colon_parser =  (many_whitespace_parser <&> (colon_parser <&> many_whitespace_parser))
End



Definition jsonValue_parser_components_def:
  (jsonValue_parser_precursor input =  (jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> (Parser(jsonArray_parser_precursor)) <|> (Parser(jsnObject_parser_precursor))).run input) ∧

(array_recursive_helper input accumulator =
 case (jsonValue_parser_precursor input) of
   Success (input', parsed) =>
     (let accumulator' = accumulator ++ [parsed]
      in case separator_parser.run input' of     
           Success (input'', _) =>
             array_recursive_helper input'' accumulator'
         | Failure _ =>
             Success (input', accumulator'))
 | Failure _ =>
     Success (input, accumulator)) ∧

(jsonArray_parser_precursor input = case open_bracket_parser.run input of
                                 Success (input', _) =>
                                   (case (array_recursive_helper input' []) of
                                      Success (input'', parsed'') =>
                                        (case closed_bracket_parser.run input'' of
                                           Success (input''', _) => Success (input''', JsonArray parsed'')
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                                    | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))) ∧
                                
(dictionary_helper input = case (separator_colon_parser <&> stringliteral_parser).run input of
                              Success (input',parsed') =>
                                (
                                case jsonValue_parser_precursor input' of
                                  Success (input'', parsed'') => Success (input'', (parsed', parsed''))
                                | Failure e => Failure e
                                )
                            | Failure e => Failure e) ∧

(dictionary_recursive_helper input accumulator =
 case (dictionary_helper input) of
   Success (input', parsed) =>
     (
     let accumulator' = accumulator ++ [parsed]
     in
       case separator_parser.run input' of
         Success (input'', _) =>
           dictionary_recursive_helper input'' accumulator'
       | Failure _ =>
           Success (input', accumulator')
     )
 | Failure _ =>
     Success (input, accumulator)) ∧


(jsnObject_parser_precursor input = case open_brace_parser.run input of

                                 (* found "{" *)
                                 Success (input', _) =>

                                   (* try to parse list of json-pairs *)
                                   (case (dictionary_recursive_helper input' []) of

                                      (* found list of json-pairs *)
                                      Success (input'', parsed'') =>

                                        (* try to parse "}" *)
                                        (case closed_brace_parser.run input'' of

                                           (* found "}" *)
                                           Success (input''', _) => Success (input''', JsonObject parsed'')

                                         (* did not find "]"*)
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))

                                    (* did not find json values *)
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))

                               (* did not find "[" *)
                                    | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'")))
Termination
  cheat
End





(* SIMPLIFIED TRIAL *)

Definition jsonValue_parser_components_def:
  (jsonValue_parser_precursor input =  (jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> (Parser(jsonArray_parser_precursor))).run input) ∧

(array_recursive_helper input accumulator =
 case (jsonValue_parser_precursor input) of
   Success (input', parsed) =>
     (let accumulator' = accumulator ++ [parsed]
      in case separator_parser.run input' of     
           Success (input'', _) =>
             array_recursive_helper input'' accumulator'
         | Failure _ =>
             Success (input', accumulator'))
 | Failure _ =>
     Success (input, accumulator)) ∧

(jsonArray_parser_precursor input = case open_bracket_parser.run input of
                                 Success (input', _) =>
                                   (case (array_recursive_helper input' []) of
                                      Success (input'', parsed'') =>
                                        (case closed_bracket_parser.run input'' of
                                           Success (input''', _) => Success (input''', JsonArray parsed'')
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                                    | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))) 

Termination
  cheat
End


 

(* requires jsonValue_parser_precursor*)
Definition jsonValue_parser_def:
  jsonValue_parser = Parser(λ input. case jsonValue_parser_precursor input of
                                      Failure e => Failure e
                                    |Success (input', parsed) =>
                                       (if input'.String = "" then Success (input', parsed)
                                        else Failure (ParserError input'.Location ("Unexpected input:" ++ input'.String))
                                       )
                           )
End
  

val _ = export_theory();      


(* TESTS *)
type_of“jsonValue_parser”;
type_of“jsonValue_parser.run”;  
        
(* PASS TESTS *)
EVAL“jsonValue_parser.run (Input 0 "[1, [null, []],[],[true, \"my_string\" ],false, ]")”;
EVAL“jsonValue_parser.run (Input 0 "{      }")”;
EVAL“jsonValue_parser.run (Input 0 "{ \"mykey\": {}     }")”;
EVAL“jsonValue_parser.run (Input 0 "{ \"mykey\": []    }")”;
EVAL“jsonValue_parser.run (Input 0 "{ \"mykey\": true    }")”;
EVAL“jsonValue_parser.run (Input 0 "{ \"my_key\": \"my_value\", \"my_next_key\": \"my_next_value\",  }")”; 
EVAL“jsonValue_parser.run (Input 0 (" { " ++ [CHR 34] ++ "cat" ++ [CHR 34] ++ ":123," ++ [CHR 34] ++ "dog" ++ [CHR 34] ++ " :    45,  } " ))”;   
EVAL“jsonValue_parser.run (Input 0 ("123"))”;
EVAL“jsonValue_parser.run (Input 0 ("null"))”;
EVAL“jsonValue_parser.run (Input 0 ("true"))”;
EVAL“jsonValue_parser.run (Input 0 ("false"))”;
EVAL“jsonValue_parser.run (Input 0 ("[{\"key-1\": [\"100\", 100, true]}, {\"key-2\": \"value\"}]"))”;
EVAL“jsonValue_parser.run (Input 0 ([CHR 34] ++ "mystring" ++ [CHR 34]))”;
EVAL“jsonValue_parser.run (Input 0 "[1, [null, []],[],[true, \"my_string\" ],false, ]")”;

EVAL“jsonValue_parser.run (Input 0 "[{}]")”;
EVAL“jsonValue_parser.run (Input 0 "[{},{},{}]")”;
EVAL“jsonValue_parser.run (Input 0 "[{ \"key-1\" : { \"key-2\" : { \"key-3\" : [] } }}]")”;


(* FAIL TESTS *)
EVAL“ jsonValue_parser.run (Input 0 ([CHR 34] ++ "normal string" ++ [CHR 34] ++ "another_normal_string"))”;
EVAL“ jsonValue_parser.run (Input 0 ("[1, true123]"))”;

      
      

(* MUTUALLY RECURSIVE DEFINITION EXAMPLE *)

type_of“LENGTH ”;
EVAL“LENGTH [1;2;3] ”;
EVAL“HD [1;2;3] ”;
EVAL“HD [] ”;

Definition fc_def:
  fc (n:num) (x:(num list))  = if ((HD x) = n) then (SOME n) else NONE
End
   
Definition fc_def:
  fc (n:int) (x:(int list)) = if (LENGTH x) > 0 then 
                                (if ((HD x) = n) then (SOME n) else NONE)
                              else NONE
End

Definition or_def:
  or p1 p2 = λx. case p1 x of
                          SOME r => SOME r
                        |NONE => p2 x
End

(* Experiment [tailrecursive] *)
Definition example_def:
  (comb s = or (or (fc 5) (fc 7)) foo s) ∧
        
  (helper s acc =                                                                                       
   if comb s = NONE then acc else helper (TL s) (1 + acc)) ∧

   (helper1 x = helper x 0) ∧
   
  (foo x = case fc 0 x of
           | NONE => NONE
           | SOME _ => SOME (1 + helper1 (TL x)))
Termination
  cheat
End

        
(* MUTUALLY RECURSIVE DEFINITION EXAMPLE *)



open jsonLangTheory;
open mlstringTheory;

type_of“json_to_mlstring”;
EVAL“”;
type_of“json_to_mlstring”;
type_of“Int 3”;
type_of“Object ([])”;
type_of“Object ([("",Int 3)])”;
type_of“strlit”;


type_of“String”;
type_of“strlit "mystring"”;
type_of“String (strlit "mystring")”;

type_of“Object ([(strlit "my-key",Int 3)])”;
type_of“Object ([(strlit "my-key-1",Int 111); (strlit "my-key-2",Int 222)])”;

(*

CONVERTION FROM:

Datatype:
  JsonValue = JsonNull
             | JsonBool bool
             | JsonNumber num
             | JsonString string
             | JsonArray (JsonValue list)
             | JsonObject ((string # JsonValue) list)
End

CONVERTION TO:

val _ = Datatype`
  obj =
     Object ((mlstring # obj ) list)
   | Array (obj list)
   | String mlstring
   | Int int
   | Bool bool
   | Null`;

*)

EVAL“JsonBool true”;
type_of“JsonBool true”;
type_of“Null”;

Definition jsonObject_to_Object_def:
  jsonObject_to_Object obj = case x o
End
        


(MAP char_parser s))        
EVAL“MAP ”

Definition inputUncons_def:
  inputUncons input =
  if (LENGTH(input.String) > 0) then
    let input' = Input (input.Location + 1) (TL input.String);
        x = HD input.String
    in SOME (x, input')
  else NONE
End


               
Definition jsonvalue_to_obj_def:
  jsonvalue_to_obj x = case x of
                            
                         (* ob is a list of pairs *)
                         JsonObject ob =>

                           (* if more than one pair then*)
                           (if ((LENGTH ob) > 0) then
                              let
                                        
                                (* convert the list of pairs and extract the list from the Object*)
                                Object tail = jsonvalue_to_obj (TL ob)
                              in
                                        
                                (* convert the head manually *)
                                Object ([((String (strlit (FST (HD ob)))), (jsonvalue_to_obj (SND(HD ob))))] ++ tail)
                            else (Object [])
                           )
                       | JsonArray a => Array []
                       | JsonString s => String (strlit s)
                       | JsonNumber n => Int n
                       | JsonBool b => Bool b
                       | JsonNull => Null
End

Definition jsonvalue_to_obj_def:
  jsonvalue_to_obj x = case x of
                         JsonObject ob => Array []
                       | JsonArray a => Array []
                       | JsonString s => String (strlit s)
                       | JsonNumber n => Int n
                       | JsonBool b => Bool b
                       | JsonNull => Null
End
        
        
                                                
EVAL“[1] ++ [1;2;3]” ;
EVAL“TL [1]”;
type_of“Object ([(strlit "my-key-1",Int 111); (strlit "my-key-2",Int 222)])”;
EVAL“Object ([(strlit "my-key-1",Int 111); (strlit "my-key-2",Int 222)])”;
EVAL“HD ([(strlit "my-key-1",Int 111); (strlit "my-key-2",Int 222)])”;
type_of“-3: int”;
    
                                     
                                    


 (*
  This module contains a datatype for representing JSON objects, and
  related functions. A JSON object can be an array of objects, a
  string, an int, a bool or null, or it can be an object enclosed
  in {}, in which case it can be viewed as a key-value store of names
  (strings) and JSON objects.
*)
open preamble;
open mlintTheory;
open mlstringTheory;

val _ = new_theory"jsonLang";

val _ = Datatype`
  obj =
     Object ((mlstring # obj ) list)
   | Array (obj list)
   | String mlstring
   | Int int
   | Bool bool
   | Null`;

Overload "++"[local] = ``Append``

val concat_with_def = Define`
  (concat_with [] c = List []) /\
  (concat_with [s] c = s) /\
  (concat_with (s::ss) c = s ++ (c ++ concat_with ss c))`;

val printable_def = Define`
  printable c <=> ORD c >= 32 /\ ORD c < 127 /\ c <> #"\"" /\ c <> #"\\"`;

val num_to_hex_digit_def = Define `
  num_to_hex_digit n =
    if n < 10 then [CHR (48 + n)] else
    if n < 16 then [CHR (55 + n)] else []`;

val n_rev_hex_digs = Define `
  n_rev_hex_digs 0 x = [] /\
  n_rev_hex_digs (SUC n) x = (num_to_hex_digit (x MOD 16) ++
    n_rev_hex_digs n (x DIV 16))`;

val encode_str_def = Define`
  encode_str unicode s =
  let s2 = explode s in
  if EVERY printable s2 then s
  else concat (MAP (\c. if printable c then implode [c]
    else if unicode then implode ("\\u" ++ REVERSE (n_rev_hex_digs 4 (ORD c)))
    else concat [strlit "\\"; toString (ORD c)]) s2)`;

Definition json_to_mlstring_def:
  (json_to_mlstring obj = 
    case obj of
        | Object mems => List [strlit "{"] ++
                concat_with (MAP mem_to_string mems) (List [strlit ","]) ++
                List [strlit "}"]
        | Array obs => List [strlit "["] ++
                concat_with (MAP json_to_mlstring obs) (List [strlit ","]) ++
                List [strlit "]"]
       | String s => List ([strlit "\""; encode_str T s; strlit "\""])
       | Int i => List [toString i]
       | Bool b => if b then List [strlit "true"] else List [strlit "false"]
       | Null => List [strlit "null"])
  /\
  (mem_to_string n_obj = let (n, obj) = n_obj in
        List [strlit "\""; n; strlit "\":"] ++ json_to_mlstring obj)
Termination
   WF_REL_TAC `measure (\x. case x of
       | INL obj => obj_size obj
       | INR p => obj2_size p)` \\ rw []
End

val _ = export_theory();



