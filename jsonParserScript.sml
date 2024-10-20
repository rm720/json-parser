(*TODO:
1. Remove redundaunt stuff
2. Make definitions neater
3. Fix names so they self explanotary
4. Put recursion where possible
5. add comprehensive tests
6. Termination proofs
7. Write description in the begining
8. Error message: make it uniform i.e return index and the only one character
9. Fix Number parser error message:
jsonNumber_parser.run (Input 0 "--123456789") =
Failure (ParserError 1 "Expected digits, but found '1'"): thm
 *)
 



(* Imported *)
open stringTheory; (* string *)
open listTheory; (* LENGTH_CONS TAKE*)
open extra_stringTheory; (* EXTRACT *)
open arithmeticTheory;  (* SUC_ONE_ADD EXP*)
open mlstringTheory; (* int *)
open jsonLangTheory; (* obj *)


val _ = new_theory"jsonParser";

(*
FOR REFERENCE:
val _ = Datatype`
  obj =
     Object ((mlstring # obj ) list)
   | Array (obj list)
   | String mlstring
   | Int int
   | Bool bool
   | Null`;

*)  


(*
Not imported
open jsonLangTheory;
open PSLPathTheory; (* CONS_def *)
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
                  Failure (ParserError (input.Location) ("Expected '" ++ [x] ++ "', but found '" ++ input.String ++ "'"))
                )
              else
                Failure (ParserError (input.Location) ("Expected SOME but found NONE"))
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

        
Overload "<x>" = “const_parser”;
val _ = set_fixity "<x>" (Infixl 550);


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
   
(*  Parser optional whitespase *)
Definition whitespace_parser_def:
  whitespace_parser = "" <x> (char_parser #" ")
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


Theorem alt_parser_length_thm:
  ∀ input input' p1 p2 parsed. (alt_parser p1 p2).run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
       
   
Definition parser_sequenser_string_def:
  parser_sequenser_string p2 p1 =
  Parser (λ input1.
            case p1.run input1 of
              Success (input2, parsed1) =>
                (
                case p2.run input2 of
                  Success (input3, parsed2) =>
                    let
                      parsed = [] ++ parsed1 ++ parsed2
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

(* Joiner: Output -> Output*)
Definition string_parser_joiner_def:
  string_parser_joiner p = λ output.
                             case output of
                               Success (input1, parsed1) =>
                                 ( case p.run(input1) of
                                   Success (input2, parsed2)  => Success (input2, (parsed1 ++ [parsed2]))
                                 |  Failure err => output)
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
                Success (input'', "true") => Success ((Input input''.Location (DROP 4 input.String)), Bool T)
              | Failure e => Failure e
            else Failure (ParserError input.Location "Expected string of length grater than 3 but found shorter")
         )                          
End     

Definition false_parser_def:
  false_parser =
  Parser (λ input.
            if LENGTH input.String >= 5 then
              case (string_parser "false").run (Input input.Location (TAKE 5 input.String))  of 
                Success (input'', "false") => Success ((Input input''.Location (DROP 5 input.String)), Bool F)
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
                Success (input'', "null") => Success ((Input input''.Location (DROP 4 input.String)), Null)
              | Failure e => Failure e
            else Failure (ParserError input.Location "Expected string of length grater than 3 but found shorter")
         )                          
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


Definition dec_digit_parser_def:
  dec_digit_parser = (
((0:int) <x> (char_parser #"0")) <|>
((1:int) <x> (char_parser #"1")) <|>
((2:int) <x> (char_parser #"2")) <|>
((3:int) <x> (char_parser #"3")) <|>
((4:int) <x> (char_parser #"4")) <|>
((5:int) <x> (char_parser #"5")) <|>
((6:int) <x> (char_parser #"6")) <|>
((7:int) <x> (char_parser #"7")) <|>
((8:int) <x> (char_parser #"8")) <|>
((9:int) <x> (char_parser #"9"))
)
End

Definition hex_digit_helper_def:
  hex_digit_helper = (
((10:int) <x> (char_parser #"a")) <|>
((10:int) <x> (char_parser #"A")) <|>
((11:int) <x> (char_parser #"b")) <|>
((11:int) <x> (char_parser #"B")) <|>
((12:int) <x> (char_parser #"c")) <|>
((12:int) <x> (char_parser #"C")) <|>
((13:int) <x> (char_parser #"d")) <|>
((13:int) <x> (char_parser #"D")) <|>
((14:int) <x> (char_parser #"e")) <|>
((14:int) <x> (char_parser #"E")) <|>
((15:int) <x> (char_parser #"f")) <|>
((15:int) <x> (char_parser #"F")) 
)
End

Definition hex_digit_parser_def:
  hex_digit_parser = (dec_digit_parser <|> hex_digit_helper)
End
                            
Definition extract_def:
  extract r = case r of
                Success (input, parsed) => SOME parsed
              |_ => NONE
End

     
Definition dec_digit_parser_joiner_def[tailrecursive]:
  dec_digit_parser_joiner output
  = case output of
      Success (input0, parsed0) =>
        (case (dec_digit_parser.run input0) of
          Success (input1, parsed1) => dec_digit_parser_joiner (Success (input1, (parsed0 + (10 ** ((LENGTH input0.String)-1)) * parsed1)))
        | Failure err => output)
    | Failure err => Failure err
End

Definition minus_parser_def:
  minus_parser = "" <x> (char_parser #"-")
End

Definition dec_str_to_int_def:
  dec_str_to_int s = THE(extract(dec_digit_parser_joiner (Success ((Input 0 s), (0:int)))))
End

Definition dec_str_to_negative_int_def:
  dec_str_to_negative_int s = 0 - THE(extract(dec_digit_parser_joiner (Success ((Input 0 s), (0:int)))))
End        


Definition jsonNumber_dec_non_negative_parser_def:
  jsonNumber_dec_non_negative_parser =
  Parser (λ input.
            case input of

              (*if nothing to parse*)
              Input location "" => Failure (ParserError location ("Expected digits, but reached end of string"))

            (* if something to parse *)                           
            | Input location1 string1 =>

                (* get first digits *)
                let parsed_digits_list = extract_first_digits string1
                in

                  (* chek if there are digits *)
                  case parsed_digits_list of

                    (* if no digits then Fail *)
                    "" =>

                      let first_character_string = SUBSTRING (input.String, input.Location, 1)
                      in
                        Failure (ParserError location1 ("Expected digits, but found '" ++ first_character_string ++ "'"))

                        (* if thre are some digits *)                     
                        | parsed_digits_string =>

                            (* extract the substring containing only digits*)
                            let string2 = EXTRACT (string1, (LENGTH parsed_digits_list), NONE)
                            in

                              (* convert digiut string to Num and return *)
                              Success (Input (location1 + LENGTH parsed_digits_string) string2,  (Int (dec_str_to_int parsed_digits_string)))
                              | _ => Failure (ParserError location ("Expected digits, but found '" ++ input.String ++ "'"))
         )
End

Definition jsonNumber_dec_negative_parser_def:
  jsonNumber_dec_negative_parser =
  Parser (λ input.
            case input of

              (*if nothing to parse*)
              Input location "" => Failure (ParserError location ("Expected digits, but reached end of string"))

            (* if something to parse *)                           
            | Input location1 string1 =>

                (* get first digits *)
                let parsed_digits_list = extract_first_digits string1
                in

                  (* chek if there are digits *)
                  case parsed_digits_list of

                    (* if no digits then Fail *)
                    "" =>

                      let first_character_string = SUBSTRING (input.String, input.Location, 1)
                      in
                        Failure (ParserError location1 ("Expected digits, but found '" ++ first_character_string ++ "'"))

                        (* if thre are some digits *)                     
                        | parsed_digits_string =>

                            (* extract the substring containing only digits*)
                            let string2 = EXTRACT (string1, (LENGTH parsed_digits_list), NONE)
                            in

                              (* convert digiut string to Num and return *)
                              Success (Input (location1 + LENGTH parsed_digits_string) string2,  (Int (dec_str_to_negative_int parsed_digits_string)))
                              | _ => Failure (ParserError location ("Expected digits, but found '" ++ input.String ++ "'"))
         )
End

          
Definition jsonNumber_dec_parser_def:
  jsonNumber_dec_parser = Parser (λ input.case input of
                                        Input location "" => Failure (ParserError location ("Expected digits, but reached end of string"))                        
                                      | Input _ _ =>
                                          case minus_parser.run input of
                                            Failure f => jsonNumber_dec_non_negative_parser.run input
                                          | Success (input1, _ ) => jsonNumber_dec_negative_parser.run input1                                                                         
                             )
End

        
Definition hex_prefix_parser_def:
  hex_prefix_parser = ((("" <x> (char_parser #"x")) <|>
  (const_parser "" (char_parser #"X"))) <&> ("" <x> (char_parser #"0")))
End


Definition hex_digit_parser_joiner_def[tailrecursive]:
  hex_digit_parser_joiner output =
  case output of
    Success (input0, parsed0) =>
      (case (hex_digit_parser.run input0) of
        Success (input1, parsed1) =>
          hex_digit_parser_joiner (Success (input1, (parsed0 + (16 ** ((LENGTH input0.String)-1)) * parsed1)))
      | Failure err => output)
  | Failure err => Failure err
End


Definition hex_str_to_int_def:
  hex_str_to_int s = 0 - THE(extract(hex_digit_parser_joiner (Success ((Input 0 s), (0:int)))))
End        


Definition jsonNumber_hex_parser_def:
  jsonNumber_hex_parser =
  Parser (λ input.
            case input of

              (*if nothing to parse*)
              Input location "" => Failure (ParserError location ("Expected digits, but reached end of string"))

            (* if something to parse *)                           
            | Input location1 string1 =>

                (* get first digits *)
                let parsed_digits_list = extract_first_digits string1
                in

                  (* chek if there are digits *)
                  case parsed_digits_list of

                    (* if no digits then Fail *)
                    "" =>

                      let first_character_string = SUBSTRING (input.String, input.Location, 1)
                      in
                        Failure (ParserError location1 ("Expected digits, but found '" ++ first_character_string ++ "'"))

                        (* if thre are some digits *)                     
                        | parsed_digits_string =>

                            (* extract the substring containing only digits*)
                            let string2 = EXTRACT (string1, (LENGTH parsed_digits_list), NONE)
                            in

                              (* convert digiut string to Num and return *)
                              Success (Input (location1 + LENGTH parsed_digits_string) string2,  (Int (hex_str_to_int parsed_digits_string)))
                              | _ => Failure (ParserError location ("Expected hex digits, but found '" ++ input.String ++ "'"))
         )
End



Definition jsonNumber_parser_def:
  jsonNumber_parser =
  Parser (λ input.case input of
                    Input location "" => Failure (ParserError location ("Expected digits, but reached end of string"))                        
                  | Input _ _ =>
                      case minus_parser.run input of
                        Success (input1, _ ) => jsonNumber_dec_negative_parser.run input1  
                      | Failure _ =>
                          (case hex_prefix_parser.run input of
                             Success (input1, _ ) => jsonNumber_hex_parser.run input1  
                           | Failure _ => jsonNumber_dec_non_negative_parser.run input
                          )
         )
End
      

Definition special_char_parser_def:
  special_char_parser = "" <x> (char_parser (CHR 34))
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


Definition normal_string_parser_def:
  normal_string_parser =
  Parser (
    λ input. FOLDL (SWAP_ARGS string_parser_joiner) (Success (input, "")) (REPLICATE (LENGTH input.String) normal_char_parser)
    )
End


Definition stringliteral_parser_def:
  stringliteral_parser =
  Parser (λ input.
            case (special_char_parser <&> (normal_string_parser <&> special_char_parser)).run input of
              Success (input', parsed_string) =>  Success (input', parsed_string)
            | Failure err => Failure err
         )
End

        
Definition jsonString_parser_def:
  jsonString_parser =
  Parser (λ input.
            case (special_char_parser <&> (normal_string_parser <&> special_char_parser)).run input of
              Success (input', parsed_string) =>  Success (input', String (strlit parsed_string))
            | Failure err => Failure err
         )
End

   

(* Array parser *)

(* Consumes a compulsory single comma *)
Definition comma_parser_def:
  comma_parser = "" <x> (char_parser #",")
End    
        
(* consumes a compulsory single comma surrounded by optional whitespaces. E.g.: "     ,     "  *)
Definition comma_separator_parser_def:
  comma_separator_parser = (many_whitespace_parser <&> (comma_parser <&> many_whitespace_parser))
End
 

Theorem comma_separator_parser_length_thm:
  ∀ input input' parsed. comma_separator_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    
      
        
(* parser of simple json values *)
Definition jsonSimple_parser_def:
  jsonSimple_parser = jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser
End

        
Theorem jsonSimple_parser_length_thm:
  ∀ input input' parsed. jsonSimple_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    

Definition open_bracket_parser_def:
  open_bracket_parser = Parser(λinput.
  case (many_whitespace_parser <&> (("" <x> (char_parser #"[")) <&> many_whitespace_parser)).run input of
    Success (input', parsed) => Success(input', [])
  | Failure e => Failure e)
End


Theorem open_bracket_parser_length_thm:
  ∀ input input' parsed. open_bracket_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    

        
Definition closed_bracket_parser_def:
  closed_bracket_parser = Parser(λinput.
  case (many_whitespace_parser <&> (("" <x> (char_parser #"]")) <&> many_whitespace_parser)).run input of
    Success (input', parsed) => Success(input', [])
  | Failure e => Failure e)
End


Theorem closed_bracket_parser_length_thm:
  ∀ input input' parsed. closed_bracket_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    
        
(* Proving Termination: Three mutually recursive definitions *)
Definition json_parser_def:
(
array_recursive_parser output =
  case output of
    Success (input, previously_parsed) =>
      (case jsonValue_parser input of
         Success (input1, parsed_element) =>
           (case comma_separator_parser.run input1 of     
              Success (input2, _) => array_recursive_parser (Success (input2, (previously_parsed ++ [parsed_element])))
            | Failure _ => Success (input1, (previously_parsed ++ [parsed_element])))
       | Failure _ => output)
  | Failure e => Failure e
) ∧                      
(
jsonArray_parser input =
           let p = closed_bracket_parser <&> Parser(λ x. (array_recursive_parser (open_bracket_parser.run x)))
           in
             case p.run input of
               Success (input1, parsed_list) => Success (input1, (Array parsed_list))
             | Failure e => Failure e
) ∧
(
jsonValue_parser input = (jsonSimple_parser <|> Parser(jsonArray_parser)).run input
)
End
Termination

WF_REL_TAC ‘measure (\x. case x of
  | INL (Failure _) => 0                             
  | INL (Success(input, previously_parsed)) => STRLEN(input.String)
  | INR (INL input) => STRLEN(input.String)          
  | INR (INR input) => STRLEN(input.String))’ 


WF_REL_TAC ‘measure (\x. case x of
  | INL (Failure _) => 0                             
  | INL (Success(input, previously_parsed)) => STRLEN(input.String) + LENGTH(previously_parsed)
  | INR (INL input) => STRLEN(input.String)          
  | INR (INR input) => STRLEN(input.String))’ 

End  

        
(* parses some values separated by comma and collects them in a list *)
Definition array_recursive_parser_def[tailrecursive]:
  array_recursive_parser p output =
  case output of
    Success (input, previously_parsed) =>
      (case p input of
         Success (input1, parsed_element) =>
           (case comma_separator_parser.run input1 of     
              Success (input2, _) => array_recursive_parser p (Success (input2, (previously_parsed ++ [parsed_element])))
            | Failure _ => Success (input1, (previously_parsed ++ [parsed_element])))
       | Failure _ => output)
  | Failure e => Failure e
End

    

Definition jsonArray_parser_def:
  jsonArray_parser element_parser input =
           let p = closed_bracket_parser <&> Parser(λ x. (array_recursive_parser element_parser (open_bracket_parser.run x)))
           in
             case p.run input of
               Success (input1, parsed_list) => Success (input1, (Array parsed_list))
             | Failure e => Failure e
End   



Theorem jsonArray_parser_length_thm:
  ∀ input input' parsed parser. jsonArray_parser parser  input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED

                                    

(* Working version Working do  not touch*)
Definition jsonValue_parser_def:
  jsonValue_parser input = (jsonSimple_parser <|> Parser(jsonArray_parser jsonValue_parser)).run input
Termination
  cheat
End


EVAL“jsonValue_parser (Input 0 "[[[null]]]")”;
EVAL“jsonValue_parser (Input 0 "5")”;
EVAL“jsonValue_parser (Input 0 "[null, true, false, 44]")”;        


   

(* Consumes a compulsory single colon *)
Definition colon_parser_def:
  colon_parser = "" <x> (char_parser #":")
End


Theorem colon_parser_length_thm:
  ∀ input input' parsed. colon_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    
       

Definition open_brace_parser_def:
  open_brace_parser = Parser(λinput.
  case (many_whitespace_parser <&> (("" <x> (char_parser #"{")) <&> many_whitespace_parser)).run input of
    Success (input', parsed) => Success(input', [])
  | Failure e => Failure e)
End


Theorem open_brace_parser_length_thm:
  ∀ input input' parsed. open_brace_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    
        
Definition closed_brace_parser_def:
  closed_brace_parser = Parser(λinput.
  case (many_whitespace_parser <&> (("" <x> (char_parser #"}")) <&> many_whitespace_parser)).run input of
    Success (input', parsed) => Success(input', [])
  | Failure e => Failure e)
End


Theorem closed_brace_parser_length_thm:
  ∀ input input' parsed. closed_brace_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    
        
        
Definition separator_colon_parser_def:
  separator_colon_parser =  (many_whitespace_parser <&> (colon_parser <&> many_whitespace_parser))
End



Theorem separator_colon_parser_length_thm:
  ∀ input input' parsed. separator_colon_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    
        

EVAL“(separator_colon_parser <&> stringliteral_parser).run (Input 0 "\"my-key\":")”;



Definition dictionary_entry_parser_def:
dictionary_entry_parser value_parser = Parser(λ input. case (separator_colon_parser <&> stringliteral_parser).run input of
                              Success (input',parsed') =>
                                (
                                case value_parser input' of
                                  Success (input'', parsed'') => Success (input'', ((strlit parsed'), parsed''))
                                | Failure e => Failure e
                                )
                          | Failure e => Failure e)
End



Theorem dictionary_entry_parser_length_thm:
  ∀ input input' parsed parser. (dictionary_entry_parser parser).run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    




Definition jsonDictionary_parser_def:
  jsonDictionary_parser value_parser input =
  let p =
      closed_brace_parser <&> Parser(λ x. (array_recursive_parser ((dictionary_entry_parser value_parser).run) (open_brace_parser.run x)))
  in
    case p.run input of
      Success (input1, parsed_list) => Success (input1, (Object parsed_list))
    | Failure e => Failure e
End



Theorem jsonDictionary_parser_length_thm:
  ∀ input input' parsed parser. jsonDictionary_parser parser  input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
         

(* Working version Working do  not touch*)
Definition jsonValue_parser_def:
  jsonValue_parser input = (jsonSimple_parser <|> (Parser(jsonDictionary_parser jsonValue_parser)) <|> (Parser(jsonArray_parser jsonValue_parser)) ).run input
Termination
  cheat
End


 
EVAL“jsonValue_parser (Input 0 "{\"key\":1}")”
EVAL“jsonValue_parser (Input 0 "[{\"my-key-1\":true,\"my-key-2\":[false, null, {\"kkk\":-10}, 0x11, [] ]}, {}, {}, []]") ”;
    

Definition mlstring_list_to_string_def:
  (mlstring_list_to_string (List []) = "") ∧
  (mlstring_list_to_string (List ((strlit s)::xs)) = 
    s ++ mlstring_list_to_string (List xs)) ∧
  (mlstring_list_to_string (Append l1 l2) = 
    mlstring_list_to_string l1 ++ mlstring_list_to_string l2) ∧
  (mlstring_list_to_string Nil = "")
End
        

Definition json_to_string_def:
  json_to_string json = mlstring_list_to_string (json_to_mlstring json)
End


(* CORRECTNESS EXAMPLE *)
EVAL“json_to_string (Object [(strlit "my-key", Null)])”;
EVAL“jsonValue_parser (Input 0 (json_to_string (Object [(strlit "my-key", Null)])))”;
EVAL“Object [(«my-key»,Null)] = THE(extract(jsonValue_parser (Input 0 (json_to_string (Object [(strlit "my-key", Null)])))))”;


EVAL“jsonValue_parser (Input 0 "-123456789")”;
                    

(* Final Goal*)
Theorem parser_correctness_thm:
  ∀json. THE(extract(jsonValue_parser (Input 0 (json_to_string json)))) = json
Proof
  (*
  rw[json_to_string_def, jsonValue_parser_def, extract_def]>>
  fs[json_to_string_def; jsonValue_parser_def; extract_def]>>
  *)
  cheat
QED
                   
        
val _ = export_theory();      

