(* Imported *)
open stringTheory; (* string *)
open listTheory; (* LENGTH_CONS TAKE*)
open extra_stringTheory; (* EXTRACT *)
open PSLPathTheory; (* CONS_def *)

(* Not imported *)

open arithmeticTheory; (* SUC_ONE_ADD *)
open sexpcodeTheory; (* STRING_def*)
open source_valuesTheory; (* option_def *)
open optionTheory; (* SOME THE NONE*)



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

(*
Definition runParser_def:
  runParser p input = p.run input
End

Definition fmap_def:
  fmap f p = Parser (λ input.
                case p.run input of
                                Failure (ParserError n e) => Failure (ParserError n e)
                              | Success (i, r) => Success (i, f r))
End

Definition fmap_parser_def:
  fmap_parser f (Parser p) =
    Parser (λ input.
      case p input of
        Failure err => Failure err
      | Success (input', x) => Success (input', f x))
End


(* Parser Functior*)      
Definition pure_parser_def:
  pure_parser x = Parser (λ input. Success (input, x))
End
*)      


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
        
                                                      

Definition const_parser_def:
  const_parser v p =
  Parser (λ input.
      case p.run input of
        Success (rest, _) => Success (rest, v)
      | Failure err => Failure err)
End

        
Overload "<$>" = “const_parser”;
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
          

(* 
Definition apply_parser_def:
  apply_parser p1 p2 =
    Parser (λ input.
      case p1.run input of
        Success (input', f) =>
          case p2.run input' of
            Success (input'', a) => Success (input'', f a)
          | Failure err => Failure err
      | Failure err => Failure err)            
End

Overload "<*>" = “apply_parser”;
val _ = set_fixity "<*>" (Infixl 600);


Definition empty_parser_def:
  empty_parser = Parser (λ input. Failure (ParserError 0 "empty"))
End
*)

(* OR-parser *)
Definition alt_parser_def:
  alt_parser p1 p2 =
    Parser (λ input.
      case p1.run input of
        Failure _ => p2.run input
      | Success _ => p1.run input)
End

Overload "<|>" = “alt_parser”;
val _ = set_fixity "<|>" (Infixl 570);
       
(*
Definition string_parser_joiner_def:
  string_parser_joiner p = λ output.
                         case output of
                           Success (input1, parsed1) =>
                             (case p.run(input1) of
                                Success (input2, parsed2)  => Success (input2, (SNOC parsed2 parsed1))
                              |  Failure err => Failure err)
                         | Failure err => Failure err
End
*)
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


(* ----------------------------------- *)
        
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


(* TODO redefine using fmap*)
Definition jsonBool_parser_def:
  jsonBool_parser =
  Parser (λ input.
            case (string_parser "true" <|> string_parser "false").run input of 
              Success (input1, "true") =>  Success (input1, JsonBool T)
            | Success (input1, "false") => Success (input1, JsonBool F)
            | Failure e => Failure e
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

Definition span_def:
  span s = APPEND (TOKENS (λ c. ~ (isDigit c)) s) (TOKENS isDigit s)
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

(*
Tests 
> # val it = ⊢ extract_first_digits "" = "": thm
> # val it = ⊢ extract_first_digits "123" = "123": thm
*)
EVAL“extract_first_digits  "123 456"”;
type_of“EXTRACT”;


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


        

Overload "<&>" = “parser_sequenser_string”;
val _ = set_fixity "<&>" (Infixl 520);


Definition special_char_parser_def:
  special_char_parser = const_parser "" (char_parser (CHR 34))
End

(*TODO:
1. Remove redundaunt stuff
2. Make definitions neater
3. Fix names so they self explanotary
4. Put recursion where possible
5. add comprehensive tests
6. Termination proofs
 *)



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


(*
Tests
> # val it =
   ⊢ jsonString_parser.run (Input 0 (STRCAT (STRCAT "\"" "my_string") "\"")) =
     Success (Input 11 "",JsonString "my_string"): thm
> 
*)
EVAL“[CHR 34] ++ "my_string" ++ [CHR 34]”;
EVAL“jsonString_parser.run (Input 0 ( [CHR 34] ++ "my_string" ++ [CHR 34]))”;
        
(* Incomplete Json parser *)
Definition jsonValue_parser_def:
  jsonValue_parser = jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser
End


(* List parser *)

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

(* Deprecated from here to ...
Definition many_json_parser_helper_def[tailrecursive]:
  many_json_parser_helper input accumulator =
  case (jsonValue_parser.run input) of
    Success (input', parsed) =>
      (let accumulator' = accumulator ++ [parsed]
      in case separator_parser.run input' of     
          Success (input'', _) =>
            many_json_parser_helper input'' accumulator'
        | Failure _ =>
            Success (input', accumulator'))
  | Failure _ =>
      Success (input, accumulator)
End
          
Definition many_json_parser_def:
  many_json_parser = Parser (λ input. many_json_parser_helper input [])
End

EVAL“open_bracket_parser.run (Input 0 "c [")”;
EVAL“many_json_parser.run (Input 0 " null")”;

(*TODO: define an AND-parser for lists:*)



(* Working *)                           
Definition jsonArray_parser_def:
  jsonArray_parser = Parser (λ input.
                          case open_bracket_parser.run input of
                            Success (input', _) =>
                              (case many_json_parser.run input' of
                                 Success (input'', parsed'') =>
                                   (case closed_bracket_parser.run input'' of
                                      Success (input''', _) => Success (input''', JsonArray parsed'')
                                    | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                               | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                          | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'")))
End

          
Definition jsonValue_parser_def:
  jsonValue_parser = jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> jsonArray_parser 
End


        


        
(* Experiment *)

       
Definition jsonValue_parser_run_def:
  jsonValue_parser_run input = (jsonValue_helper_parser <|> (Parser(jsonArray_parser_run))).run input
End


(* TODO: Use IF THEN ELSE and Go to Failure first*)
Definition jsonArray_parser_def:
  jsonArray_parser = Parser (λ input.
                          case open_bracket_parser.run input of
                            Success (input', _) =>
                              (case (many_json_parser_helper input' []) of
                                 Success (input'', parsed'') =>
                                   (case closed_bracket_parser.run input'' of
                                      Success (input''', _) => Success (input''', JsonArray parsed'')
                                    | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                               | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                          | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'")))
End


Definition jsonArray_parser_run_def:
  jsonArray_parser_run input = case open_bracket_parser.run input of
                                 Success (input', _) =>
                                   (case (many_json_parser_helper input' []) of
                                      Success (input'', parsed'') =>
                                        (case closed_bracket_parser.run input'' of
                                           Success (input''', _) => Success (input''', JsonArray parsed'')
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                               | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))
End


Definition json_single_array_parser_def:
  json_single_array_parser = jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser
End

... Deprecated to here
*)

(* Working*)
(* Mutually recursive definitions for the Json Array Parser*)
Definition jsonArray_parser_components_def:
(jsonValue_parser_precursor input = (jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> (Parser(jsonArray_parser_precursor))).run input) ∧

(jsonArray_recursive_helper input accumulator =
 case (jsonValue_parser_precursor input) of
   Success (input', parsed) =>
     (let accumulator' = accumulator ++ [parsed]
      in case separator_parser.run input' of     
           Success (input'', _) =>
             jsonArray_recursive_helper input'' accumulator'
         | Failure _ =>
             Success (input', accumulator'))
 | Failure _ =>
     Success (input, accumulator)) ∧

(jsonArray_parser_precursor input = case open_bracket_parser.run input of
                                 Success (input', _) =>
                                   (case (jsonArray_recursive_helper input' []) of
                                      Success (input'', parsed'') =>
                                        (case closed_bracket_parser.run input'' of
                                           Success (input''', _) => Success (input''', JsonArray parsed'')
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                              | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'")))
Termination
  cheat
End

        
  rw[]>>
  fs[]
End

Definition jsonValue_parser_def:
  jsonValue_parser = Parser(jsonValue_parser_precursor)
End
     

(* Tests

EVAL“jsonObject_parser_incomplete.run (Input 0 "[1, [null, []],[],[true, \"my_string\" ],false, ]")”;
[1, [null, []], [], [true, \"my_string\" ],false, ] =

[1; [Null; []]; []; [T;     "my_string" ]; F]     ]
 
 *)        

      


(* ------- Example from Discord -------- *)

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

(* Experiment *)
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

        
(* ------- Example from Discord  -------- *)


    
     

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

Definition pair_parser_def:
  pair_parser = Parser( λ input.
                          case (separator_colon_parser <&> stringliteral_parser).run input of
                            Success (input',parsed') =>
                              (
                              case jsonValue_parser.run input' of
                                Success (input'', parsed'') => Success (input'', (parsed', parsed''))
                              | Failure e => Failure e
                              )
                          | Failure e => Failure e
                      )
End

EVAL“stringliteral_parser.run (Input 0 ([CHR 34] ++ "mystring" ++ [CHR 34]))”;       

(* Darft *)
Definition pair_parser_helper_def:
  pair_parser_helper input = case (separator_colon_parser <&> stringliteral_parser).run input of
                            Success (input',parsed') =>
                              (
                              case jsonValue_parser.run input' of
                                Success (input'', parsed'') => Success (input'', (parsed', parsed''))
                              | Failure e => Failure e
                              )
                          | Failure e => Failure e
End       

      

Definition many_pairs_parser_helper_def[tailrecursive]:
  many_pairs_parser_helper input accumulator =
  case (pair_parser.run input) of
    Success (input', parsed) =>
      (
      let accumulator' = accumulator ++ [parsed]
      in
        case separator_parser.run input' of
          Success (input'', _) =>
            many_pairs_parser_helper input'' accumulator'
        | Failure _ =>
            Success (input', accumulator')
      )
  | Failure _ =>
      Success (input, accumulator)
End
     
Definition many_pairs_parser_def:
  many_pairs_parser = Parser (λ input. many_pairs_parser_helper input [])
End


Definition JsonObject_parser_def:
  JsonObject_parser = Parser (λ input.
                          
                          (* try to parse "{" *)
                          case open_brace_parser.run input of

                            (* found "{" *)
                            Success (input', _) =>

                              (* try to parse list of pairs *)
                              (case many_pairs_parser.run input' of

                                 (* found list of jsonspairs *)
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
                          | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))
                       )
End
(* Draft *)
Definition JsonObject_parser_def:
  JsonObject_parser input = case open_brace_parser.run input of

                            (* found "{" *)
                            Success (input', _) =>

                              (* try to parse list of pairs *)
                              (case (many_pairs_parser_helper input' []) of

                                 (* found list of jsonspairs *)
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
                          | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))
End




(jsonValue_parser_precursor input = (jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> (Parser(jsonArray_parser_precursor))).run input) ∧

Definition jsonValue_parser_def:
  jsonValue_parser  = jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|>  JsonObject_parser
End

Definition jsonValue_parser_def:
  jsonValue_parser input  = (jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|>  Parser(JsonObject_parser.run)).run input
End

(* Experiment *)


Definition jsonObject_parser_helper_def:
  jsonObject_parser_helper = Parser(jsonvalue_array_parser_run)
End


(*(jsonValue_parser_precursor input = (jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> (Parser(jsonArray_parser_precursor)) <|> (Parser(jsonObject_parser_precursor))).run  input) *)
(* Json Object Parser compiles *)


(* Compiles! *)
Definition jsonValue_parser_components_def:
  (jsonValue_parser_precursor input =  (jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> (Parser(jsonArray_parser_precursor)) <|> (Parser(jsnObject_parser_precursor))).run input) ∧

(jsonArray_recursive_helper input accumulator =
 case (jsonValue_parser_precursor input) of
   Success (input', parsed) =>
     (let accumulator' = accumulator ++ [parsed]
      in case separator_parser.run input' of     
           Success (input'', _) =>
             jsonArray_recursive_helper input'' accumulator'
         | Failure _ =>
             Success (input', accumulator'))
 | Failure _ =>
     Success (input, accumulator)) ∧

(jsonArray_parser_precursor input = case open_bracket_parser.run input of
                                 Success (input', _) =>
                                   (case (jsonArray_recursive_helper input' []) of
                                      Success (input'', parsed'') =>
                                        (case closed_bracket_parser.run input'' of
                                           Success (input''', _) => Success (input''', JsonArray parsed'')
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                                    | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))) ∧
                                
(pair_parser_helper input = case (separator_colon_parser <&> stringliteral_parser).run input of
                              Success (input',parsed') =>
                                (
                                case jsonValue_parser_precursor input' of
                                  Success (input'', parsed'') => Success (input'', (parsed', parsed''))
                                | Failure e => Failure e
                                )
                            | Failure e => Failure e) ∧

(many_pairs_parser_helper input accumulator =
 case (pair_parser_helper input) of
   Success (input', parsed) =>
     (
     let accumulator' = accumulator ++ [parsed]
     in
       case separator_parser.run input' of
         Success (input'', _) =>
           many_pairs_parser_helper input'' accumulator'
       | Failure _ =>
           Success (input', accumulator')
     )
 | Failure _ =>
     Success (input, accumulator)) ∧

(jsnObject_parser_precursor input = case open_brace_parser.run input of

                                 (* found "{" *)
                                 Success (input', _) =>

                                   (* try to parse list of pairs *)
                                   (case (many_pairs_parser_helper input' []) of

                                      (* found list of jsonspairs *)
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


        
Definition jsonValue_parser_def:
  jsonValue_parser = Parser(jsonValue_parser_precursor)
End


Definition jsonValue_parser_def:
  jsonValue_parser = Parser(λ input. case jsonValue_parser_precursor input of
                                      Failure e => Failure e
                                    |Success (input', parsed) =>
                                       (if input'.String = "" then Success (input', parsed)
                                        else Failure (ParserError input'.Location ("Unexpected input:" ++ input'.String))
                                       )
                           )
End
        

        
(* TESTS *)  
EVAL“jsonValue_parser.run (Input 0 "[1, [null, []],[],[true, \"my_string\" ],false, ]")”;
EVAL“jsonValue_parser.run (Input 0 "{      }")”;
(* NOT A BUG:
 > # val it =
   ⊢ jsonValue_parser.run (Input 0 "{      }") =
     Success (Input 8 "",JsonObject []): thm

THIS IS BY THE DEFINITION...
Dictionary is a list of pairs. Empty dictionary is an empty list
 *)
EVAL“jsonValue_parser.run (Input 0 "{ \"mykey\": {}     }")”;
EVAL“jsonValue_parser.run (Input 0 "{ \"mykey\": []    }")”;
EVAL“jsonValue_parser.run (Input 0 "{ \"mykey\": true    }")”;
EVAL“jsonValue_parser.run (Input 0 "{ \"my_key\": \"my_value\", \"my_next_key\": \"my_next_value\",  }")”; 
EVAL“jsonValue_parser.run (Input 0 (" { " ++ [CHR 34] ++ "cat" ++ [CHR 34] ++ ":123," ++ [CHR 34] ++ "dog" ++ [CHR 34] ++ " :    45,  } " ))”;   
EVAL“ jsonValue_parser.run (Input 0 ([CHR 34] ++ "normal string" ++ [CHR 34] ++ "another_normal_string"))”;
EVAL“ jsonValue_parser.run (Input 0 ("123"))”;
EVAL“ jsonValue_parser.run (Input 0 ("null"))”;
EVAL“ jsonValue_parser.run (Input 0 ("true"))”;
EVAL“ jsonValue_parser.run (Input 0 ("false"))”;
EVAL“ jsonValue_parser.run (Input 0 ("[1, true123]"))”;
EVAL“ jsonValue_parser.run (Input 0 ("[{\"key-1\": [\"100\", 100, true]}, {\"key-2\": \"value\"}]"))”;


val _ = export_theory();

      

