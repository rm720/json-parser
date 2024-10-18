(*TODO:
1. Remove redundaunt stuff
2. Make definitions neater
3. Fix names so they self explanotary
4. Put recursion where possible
5. add comprehensive tests
6. Termination proofs
7. Write description in the begining
8. Error message: make it uniform i.e return index and the only one character
9. fix Number parser error message:
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
  wf_rel_tac `measure (\s. LENGTH s)`  (* The well-founded measure is the length of the list *)
  THEN REWRITE_TAC [LENGTH_TL]         (* Rewrite using the definition of TL *)
  THEN INDUCT_TAC                      (* Apply induction over the structure of the list *)
  THEN ASM_REWRITE_TAC []              (* Simplify using the assumptions *)
  THEN ARITH_TAC                       (* Use arithmetic tactics to complete the proof *)
QED



        


Theorem cons_lenght_thm:
  ∀s x xs. (LENGTH s > 0) ⇒ LENGTH (TL s) < LENGTH s

Proof
  (* Start by applying induction on the structure of the list `s` *)
  Induct_on ‘s’>>

  (* Case 1: `s` is the empty list, but LENGTH s > 0 eliminates this case *)
  (* Thus, we automatically move to the second case *)

  (* Case 2: `s = x::xs` *)
  STRIP_TAC>>

  (* Now, we need to prove LENGTH(TL (x::xs)) < LENGTH(x::xs). Simplify this expression *)
  REWRITE_TAC [TL]>>

  (* TL (x::xs) = xs, so we need to show LENGTH(xs) < LENGTH(x::xs) *)
  REWRITE_TAC [LENGTH]>>

  (* This reduces to proving that SUC (LENGTH xs) > LENGTH xs *)
  ARITH_TAC

QED

        

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
       
    


    

(* parser_1 <&> parser_2 
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
 *)

(* New version *) 
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

     
(* Assuming the input string contains only digits and the parsed component is 0 to start with*)
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


(* TODO redo using recursion *)
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

          
(* TODO: include negative numbers *)
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
      
(* PASS *)
EVAL“jsonNumber_parser.run (Input 0 "123456789")”;             
EVAL“jsonNumber_parser.run (Input 0 "-123456789")”;
EVAL“jsonNumber_parser.run (Input 0 "0x123456789")”;
EVAL“jsonNumber_parser.run (Input 0 "1x23456789")”;
EVAL“jsonNumber_parser.run (Input 0 "0x0123456789")”;
EVAL“jsonNumber_parser.run (Input 0 "-0")”;

(* FAIL *)
EVAL“jsonNumber_parser.run (Input 0 "-0x123456789")”;
EVAL“jsonNumber_parser.run (Input 0 "--123456789")”;
EVAL“jsonNumber_parser.run (Input 0 "+123456789")”;

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


(* TODO redo using recursion *)
(* TODO generalise and call "many". I am  not sure if this needed*)
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
    


(* Working New version *)
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

 
  

(* Trying to prove termination *)
Definition jsonValue_parser_def:
  jsonValue_parser input = (jsonSimple_parser <|> Parser(jsonArray_parser jsonValue_parser)).run input
End
        
Termination
  cheat
End
 
Termination
  WF_REL_TAC ‘measure (λ input. LENGTH input.String)’ >>
  rw[]>>
End


      

(* Consumes a compulsory single colon *)
Definition colon_parser_def:
  colon_parser = "" <x> (char_parser #":")
End


Theorem colon_parser_length_thm:
  ∀ input input' parsed. colon_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    
        

  (*      
Definition open_brace_parser_def:
  open_brace_parser = (many_whitespace_parser <&> (("" <x> (char_parser #"{")) <&> many_whitespace_parser))
End

Definition closed_brace_parser_def:
  closed_brace_parser = (many_whitespace_parser <&> (("" <x> (char_parser #"}")) <&> many_whitespace_parser))
End
*)


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
type_of“jsonSimple_parser”;
type_of“separator_colon_parser <&> stringliteral_parser”;


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
    


        
type_of“array_recursive_parser”;
type_of“(dictionary_entry_parser jsonValue_parser).run”;
type_of“jsonValue_parser”;
type_of“(dictionary_entry_parser jsonValue_parser).run”;
type_of“array_recursive_parser (dictionary_entry_parser jsonValue_parser).run ”;
EVAL“(dictionary_entry_parser jsonValue_parser).run (Input 0 "\"my-key-1\":true,\"my-key-2\":false ")”;
EVAL“array_recursive_parser ((dictionary_entry_parser jsonValue_parser).run) (Success ((Input 0 "\"my-key-1\":true,\"my-key-2\":false "),[]))”;
type_of“array_recursive_parser ((dictionary_entry_parser jsonValue_parser).run) (Success ((Input 0 "\"my-key-1\":true,\"my-key-2\":false "),[]))”;


(* Compiles New version *)
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
         

EVAL“(jsonDictionary_parser jsonValue_parser).run (Input 0 "\"my-key-1\":true,\"my-key-2\":false ") ”;
type_of“jsonDictionary_parser”;
type_of“jsonValue_parser”;
type_of“jsonDictionary_parser jsonValue_parser”;


Definition input_size_def:
  input_size (Input loc str) = LENGTH str
End

Termination

  WF_REL_TAC ‘measure input_size’ >>
  rw[]>>
        
   Cases_on ‘input’>|
   fs [input_size_def]>>
   imp_res_tac open_bracket_parser_decreases_input
   \\ imp_res_tac array_recursive_parser_decreases_input
   \\ decide_tac)
                                 

(* Working version Working do  not touch*)
Definition jsonValue_parser_def:
  jsonValue_parser input = (jsonSimple_parser <|> (Parser(jsonDictionary_parser jsonValue_parser)) <|> (Parser(jsonArray_parser jsonValue_parser)) ).run input
Termination
  cheat
End

EVAL“jsonValue_parser (Input 0 "{\"key\":1}")”
EVAL“jsonValue_parser (Input 0 "[{\"my-key-1\":true,\"my-key-2\":[false, null, {\"kkk\":-10}, 0x11, [] ]}, {}, {}, []]") ”;



Theorem jsonValue_parser_length_thm:
  ∀ input input' parsed any_parser. any_parser = (jsonSimple_parser <|> (Parser(jsonDictionary_parser jsonValue_parser)) <|> (Parser(jsonArray_parser any_parser))) ∧
  any_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
       




                      


Definition jsonValue_parser_def:
  jsonValue_parser input = (jsonSimple_parser <|> (Parser(jsonDictionary_parser jsonValue_parser)) <|> (Parser(jsonArray_parser jsonValue_parser)) ).run input
End
Termination
  
  (* Establish the measure function based on input length *)
  WF_REL_TAC ‘measure (λ input. LENGTH input.String)’ >>

  (* Case split for alternative parser *)
  Cases_on ‘jsonSimple_parser.run input’ THENL

  [
    (* Case 1: jsonSimple_parser is successful *)
    rw[jsonSimple_parser_length_thm] THEN
    meson_tac[]>>

    
        
Termination
  WF_REL_TAC ‘measure (λ input. LENGTH input.String)’ >>
  rw[alt_parser_length_thm, jsonSimple_parser_length_thm, jsonArray_parser_length_thm, jsonDictionary_parser_length_thm]>>
End




Definition parser1_def:
  parser1 input = Parser(simple_json_parser) <|> 
  let p2 = λx. case simple_json_parser x of Success s => Success s | _ => parser1 x
      in array_parser_builder p2 input                                                               
Termination
  cheat
End

   
Definition parser1_def:
  parser1 input =
  let p2 = λx. case simple_json_parser x of Success s => Success s | _ => parser1 x
      in array_parser_builder p2 input                                                               
Termination
  cheat
End
Termination
  rw[]>>
  WF_REL_TAC ‘measure (λx input. LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
End

EVAL“parser1 (Input 0 "[[[null]]]")”;
EVAL“parser1 (Input 0 "5")”;
EVAL“parser1 (Input 0 "[null, true, false, 44]")”;



        

Termination
  fs[]>>
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
  rw[]>>

         
        
(* TRY make it tailrecursive by introducin an inner recursive lambda function *)
(* TRY to introduce empty string exit immediately in parser *)
  
(* Experiment: measure works, proof is not finished *)
Definition parser1_def:
  parser1 input =
   let p2 = λx. case parserC x of Success s => Success s | _ => parser1 input 
   in
     case parserOR parserB (parserOR p2 parserA) input of
       Success (input', parsed) =>  Success (input', parsed)
     | Failure e => Failure e
End
WF_REL_TAC ‘measure (λx. LENGTH x.String)’ >>
           rw[]>>


(* Experiment: measure works, proof is not finished don't touch*)
Definition example_def:
  (parser1 input = case parserOR parserB (parserOR parser2 parserA) input of
                     Success (input', parsed) =>
                       let f = λx. x in Success (input', f(parsed))
                     | Failure e => Failure e
  ) ∧

  (parser2 input = case parserC input of
                     Failure e => parser1 input
                   | s => s
  ) 
End
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
  rw[]>>
                 
End


Definition jsonArray_recursive_parser_precursor_def:
  jsonArray_recursive_parser_precursor input = (jsonBool_parser <|>
jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> (jsonArray_parser Parser(jsonArray_recursive_parser_precursor))).run input          
End
Termination
  rw[]>>
    WF_REL_TAC ‘measure (λinput. LENGTH input.String)’ >>
(*  ∃R. WF R ∧ ∀input a. R a input: proof *)

                       
        
EVAL“open_bracket_parser.run (Input 0 "[123")”;

type_of“open_bracket_parser”;
type_of“simple_json_parser”;
type_of“open_bracket_parser <&> open_bracket_parser”;
        


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
                                           Success (input''', _) => Success (input''', Array parsed'')
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                                    | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))) 

End

Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
  fs[LENGTH_TL]
End


Definition simple_json_parser_def:
  simple_json_parser = jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser
End
        

(* MODIFIED SIMPLIFIED TRIAL *)
  

Definition jsonValue_parser_components_def:

(array_recursive_helper input accumulator =
 case ((simple_json_parser <|> Parser(jsonArray_parser_precursor)).run input)of
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
                                           Success (input''', _) => Success (input''', Array parsed'')
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                                    | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))) 

End

Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
  fs[LENGTH_TL]
End


        

type_of“INR”;
type_of“INL”;
type_of“OUTR”;
type_of“OUTL”;



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


       
EVAL“json_to_string (Object [(strlit "my-key", Null)])”;
EVAL“jsonValue_parser.run (Input 0 (json_to_string (Object [(strlit "my-key", Null)])))”;

(* CORRECTNESS EXAMPLE *)                         
EVAL“(Object [(strlit "my-key", Null)]) = THE(extract((jsonValue_parser.run (Input 0 (json_to_string (Object [(strlit "my-key", Null)]))))))”;


Theorem parser_correctness_thm:
  ∀json. THE(extract(jsonValue_parser.run (Input 0 (json_to_string json)))) = json
Proof
  rw[json_to_string_def, jsonValue_parser_def, extract_def]>>
                           fs[json_to_string_def; jsonValue_parser_def; extract_def]>>
QED
                   
type_of“THE”;

                   
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
EVAL“jsonValue_parser.run (Input 0 ("[-1, true, -123]"))”;


(* FAIL TESTS *)
EVAL“ jsonValue_parser.run (Input 0 ([CHR 34] ++ "normal string" ++ [CHR 34] ++ "another_normal_string"))”;
EVAL“ jsonValue_parser.run (Input 0 ("[1, true123]"))”;

type_of“json_to_mlstring Null”;
type_of“json_to_mlstring”;
EVAL“json_to_mlstring Null”;
EVAL“json_to_mlstring Null”;
EVAL“json_to_mlstring Bool true”;
EVAL“json_to_mlstring Bool false”;

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

        

Definition example_def:
  (comb s = or (or (fc 5) (fc 7)) foo s) ∧
        
  (helper s acc =                                                                                       
   if comb s = NONE then acc else helper (TL s) (1 + acc)) ∧
   
  (foo x = case fc 0 x of
           | NONE => NONE
           | SOME _ => SOME (1 + (helper (TL x) 0)))
End
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL x => LENGTH x.String
                           | INR x => LENGTH x.String)’ >>
  fs[LENGTH_TL]>>



        
  WF_REL_TAC ‘inv_image ($< LEX $<) (λx. case x of
                INL s => (LENGTH s, 0)
              | INR (INL (s, acc)) => (LENGTH s, acc)
              | INR (INR s) => (LENGTH s, 0))’ >>
  rw[] >>
  TRY(Cases_on `OUTR (scratch$old37->example_def_UNION_aux<-old R (INL s))`) >>
  fs[LENGTH_TL] >>
  TRY(Cases_on `fc 0 x`) >>
  fs[] >>
  decide_tac
End


Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λx. case x of
                INL s => (LENGTH s, 0)
              | INR (INL (s, acc)) => (LENGTH s, acc)
              | INR (INR s) => (LENGTH s, 0))` >>
  rw[] >>

  fs[LENGTH_TL] >>
  TRY(Cases_on `fc 0 x`) >>
  fs[] >>
  metis_tac[LESS_EQ_LESS_TRANS, LESS_TRANS, NOT_LESS, LESS_OR_EQ]
End
        

(* Parsing a list of numbers [tailrecursive]: works*)
Definition example_def:
  (parse1 acc s = case s of
                    [] => acc
                  | l =>
                      (case (HD l) of
                         #"A" => parse2 (1 + acc) (TL l)
                       | _ => parse1 (2 + acc) (TL l)
                      )

  ) ∧

  (parse2 acc s = case s of
                    [] => acc
                  | l => parse1 (0 + acc) (TL l))
End

Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL (_, s) => LENGTH s
                           | INR (_, s) => LENGTH s)’ >>
  fs[LENGTH_TL]
                           
End




             
(* Parsing a list of numbers [tailrecursive]: works. don't touch*)
Definition example_def:
  (parser1 input = case input.String of
                    "" => Success (input, "")
                  | _ =>
                      (case (HD input.String) of
                         #"A" => parser2 (Input (input.Location + 1) (TL input.String))
                       | _ => parser1 (Input (input.Location + 0) (TL input.String))
                      )
  ) ∧

  (parser2 input = case input.String of
                    "" => Success (input, "")
                  | _ => parser1 (Input (input.Location + 0) (TL input.String))
  )
End
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
  fs[LENGTH_TL]>>
                           
End



Theorem parserA_length_thm:
  ∀ input input' parsed. parserA input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED


Theorem parserA_either_thm:
  ∀ input input' parsed f. parserA input = Success(input', parsed) ⇒ parserA input ≠ Failure f
Proof
  cheat
QED

        
        
Theorem parserB_length_thm:
  ∀ input input' parsed. parserB input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED
    
Theorem parserC_length_thm:
  ∀ input input' parsed. parserC input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED

Theorem parserD_length_thm:
  ∀ input input' parsed. parserD input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED

Definition parserAB_def:
  parserAB input = parserOR parserA parserB input
End

Theorem parserAB_length_thm:
  ∀ input input' parsed. parserAB input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED

Theorem parserOR_length_thm:
  ∀ input input' p1 p2 parsed. parserOR p1 p2 input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED

Theorem parserAND_length_thm:
  ∀ input input' p1 p2 parsed. parserAND p1 p2 input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  cheat
QED        


(* Experiment: measure works, proof is not finished *)
Definition example_def:
  (parser1 input = case parserA input of
                     Success (input', parsed) => parser2 input'
                   | _ => parser1 input
  ) ∧

  (parser2 input = case parserB input of
                     Success (input', parsed) => parser1 input'
                   | _ => Success (input, "")
  ) 
End
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
                 
End


(* Experiment: measure works, proof is not finished *)
Definition example_def:
  (parser1 input = case parserOR parserA parserB input of
                     Success (input', parsed) => parser2 input'
                   | _ => parser1 input
  ) ∧

  (parser2 input = case parserAND parserC parserD input of
                     Success (input', parsed) => parser1 input'
                   | _ => Success (input, "")
  ) 
End

Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
                 
End

(* Experiment: measure works, proof is not finished *)
Definition example_def:
  (parser1 input = case parserOR parser3 (parserOR parserA parserB) input of
                     Success (input', parsed) => parser2 input'
                   | _ => parser1 input
  ) ∧

  (parser2 input = case parserAND parserC parserD input of
                     Success (input', parsed) => parser1 input'
                   | _ => Success (input, "")
  ) 
End

Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
                 
End


(*
   ∃R. WF R ∧ (∀input a. R (INL a) (INR input)) ∧
       ∀input e.
         simple_json_parser input = Failure e ⇒ R (INR input) (INL input)
   
   : proof
*)

        
             
(* Parsing a list of numbers*)
Definition example_def:
  (parser1 input = parserOR parserAB parser3 input
  ) ∧

  (parser2 input = case parser1 input of
                    Success (input', parsed) => parser1 input'
                  | _ => Success (input, "") 
  ) ∧

  (parser3 input = parserAND parserC parser2 input
  )
End
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
  fs[parserA_length_thm]>>
  fs[parserB_length_thm]>>                        
End



        

Definition jsonValue_parser_components_def:
  (jsonValue_parser_precursor input =  parserOR parserA parserB input ∧

(array_recursive_helper input =
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
                                           Success (input''', _) => Success (input''', Array parsed'')
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                                    | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))) 

End
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
  fs[LENGTH_TL]
End
(* Parsing a list of numbers *)
Definition example_def:
        
  (parser1 input = case input.String of
                    "" => Success (input, "")
                  | _ =>
                      (case (parserOR parserA parserB input) of
                         Success _ => parser2 (Input (input.Location + 1) (TL input.String))
                       | _ => parser1 (Input (input.Location + 0) (TL input.String))
                      )
  ) ∧

  (parser2 input = case input.String of
                    "" => Success (input, "")
                  | _ => parserAND parserA parser1 (Input (input.Location + 0) (TL input.String))
  )
End
Termination
  WF_REL_TAC ‘measure (λx. case x of
                             INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
  fs[LENGTH_TL]>>
  rw[SUC_LESS]>>
                           
End



EVAL“SUC_LESS”;



        

Definition parserA_def:
  parserA input = case input.String of
                     "" => Failure (ParserError input.Location "Error in parser A: Empty input")
                   | _ =>
                       (case (HD input.String) of
                          #"A" => Success ((Input (input.Location + 1) (TL input.String)), "A")
                        | _ => Failure (ParserError input.Location  "Error in parser A but did not get it")
                      )
End
        

Definition parserB_def:
  parserB input = case input.String of
                     "" => Failure (ParserError input.Location "Error in parser B: Empty input")
                   | _ =>
                       (case (HD input.String) of
                          #"B" => Success ((Input (input.Location + 1) (TL input.String)), "B")
                        | _ => Failure (ParserError input.Location  "Error in parser B but did not get it")
                      )
End


Definition parserC_def:
  parserC input = case input.String of
                     "" => Failure (ParserError input.Location "Error in parser C: Empty input")
                   | _ =>
                       (case (HD input.String) of
                          #"C" => Success ((Input (input.Location + 1) (TL input.String)), "C")
                        | _ => Failure (ParserError input.Location  "Error in parser C but did not get it")
                      )
End

Definition parserD_def:
  parserD input = case input.String of
                     "" => Failure (ParserError input.Location "Error in parser D: Empty input")
                   | _ =>
                       (case (HD input.String) of
                          #"D" => Success ((Input (input.Location + 1) (TL input.String)), "D")
                        | _ => Failure (ParserError input.Location  "Error in parser D but did not get it")
                      )
End


        
Definition parserOR_def:
  parserOR p1 p2 input = case p1 input of
                       Success s => Success s
                     |_ => p2 input
End


Definition parserAND_def:
  parserAND p1 p2 input = case (p1 input) of
                            Success (input', parsed) =>
                              (case p2 input' of
                                Success (input'', parsed') =>  Success (input'', "")
                              | Failure f => Failure f)
                          | Failure f => Failure f
End



Definition example_def:
(parser1 input = parserOR (parserOR parserA parserB) (parser3) input) ∧
           
(parser2 input = parserAND parser1 parser2 input) ∧
         
(parser3 input = case input.String of
                    "" => Success (input, "")
                  | _ => parser2 input
)
End      
Termination
  WF_REL_TAC ‘measure (λx. case x of
                           | INL input => LENGTH input.String
                           | INR input => LENGTH input.String)’ >>
  fs[LENGTH_TL]>>
                           
End

type_of“#"A"”;
type_of“HD "AAA"”;  

        
   
type_of“TL”;
EVAL“TL_def”;
        

type_of“type_size”;
type_of“obj_size”;
type_of“obj1_size”;
type_of“list_size”;
type_of“list_size LENGTH”;
type_of“LENGTH”;
type_of“λx:char. 1:num”;
type_of“list_size (λx:char. 1:num) ”;
type_of“list_size (λx:char. 1:num) "123" ”;
type_of“list_size (λx:char. 1:num) [] ”;
EVAL“list_size (λx:char. 1:num) "AB" ”;



        

Termination
  WF_REL_TAC ‘measure (λ(s,a).
       | INL (s, a) => list_size (λx:char. 1:num) s
       | INR (s, a) => list_size (λx:char. 1:num) s’>>
End


  (WF_REL_TAC `measure (\x. case x of
                  INR (x,_) => type1_size x
                | INL (x,_) => type_size x)`)

val (parse1_def, parse2_def) = tDefine "parse" ‘
  (parse1 s acc = case s of
                    [] => acc
                  | (l::ls) => parse2 ls (1 + acc + l)) ∧
  (parse2 s acc = case s of
                    [] => acc
                  | (l::ls) => parse1 ls (2 + acc + l))’
  (WF_REL_TAC ‘measure (λx. case x of
                             INL (s, _) => LENGTH s
                           | INR (s, _) => LENGTH s)’)


val example_def =
   ⊢ (∀s acc.
        parse1 s acc =
        case s of
          [] => acc
        | v2::v3 => parse2 (TL (v2::v3)) (1 + acc + HD (v2::v3))) ∧
     ∀s acc.
       parse2 s acc =
       case s of
         [] => acc
       | v2::v3 => parse1 (TL (v2::v3)) (2 + acc + HD (v2::v3)): thm

Initial goal:

∃R. WF R ∧
    (∀acc s v2 v3.
       s = v2::v3 ⇒ R (INL (TL (v2::v3),2 + acc + HD (v2::v3))) (INR (s,acc))) ∧
    ∀acc s v2 v3.
      s = v2::v3 ⇒ R (INR (TL (v2::v3),1 + acc + HD (v2::v3))) (INL (s,acc))











                
        
(* MUTUALLY RECURSIVE DEFINITION EXAMPLE *)

type_of“size”;

        

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

               
EVAL“json_to_mlstring Null”;
EVAL“json_to_mlstring (Array [])”;
EVAL“json_to_mlstring (Array [Null])”;
EVAL“json_to_mlstring (Object [])”;
EVAL“json_to_mlstring (Object [(strlit "my-key", Null)])”;
EVAL“json_to_mlstring (Bool true)”;

type_of“json_to_mlstring (Bool true)”;
type_of“json_to_mlstring”;
type_of“mlstring_list_to_string”;
type_off“app_list”;




EVAL“jsonValue_parser (json_to_string (Object [(strlit "my-key", Null)]))”;

EVAL“json_to_mlstring (Array [])”;
EVAL“json_to_mlstring (Array [Bool true; Bool false])”;
EVAL“mlstring_list_to_string(json_to_mlstring (Array [Bool true; Bool false]))”;

        



        

EVAL“json_to_mlstring (Object ([(strlit "my-key",Int 3)]))”;
EVAL“Object ([(strlit "my-key",Int 3)])”;
type_of“Object ([(strlit "my-key-1",Int 111); (strlit "my-key-2",Int 222)])”;           
EVAL“json_to_mlstring (Int 3)”;

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
type_of“Object [(strlit "my-key", Null)]”;
type_of“Array []”;

EVAL“Object [(strlit "my-key", Null)]”;
EVAL“Object []”;

EVAL“FST (HD [(strlit "my-key", Null)])”;
EVAL“SND (HD [(strlit "my-key", Null)])”;

Definition jsonObject_to_Object_def:
  jsonObject_to_Object obj = case x o
End
        


(MAP char_parser s))        
EVAL“MAP ”;

Definition inputUncons_def:
  inputUncons input =
  if (LENGTH(input.String) > 0) then
    let input' = Input (input.Location + 1) (TL input.String);
        x = HD input.String
    in SOME (x, input')
  else NONE
End

open jsonLangTheory;


     

Definition jsonvalue_to_obj_def:
  jsonvalue_to_obj x = case x of
                            
                         JsonObject ob =>
                           case LENGTH ob of
                           | 0 => Object []
                           | 1 =>
                               let key = FST (HD ob);
                                   value = SND (HD ob)
                               in  () ++ jsonvalue_to_obj (Object (TL ob))
                                        
                                         
                                                     

                           (* if more than one pair then*)
                           (if ((LENGTH ob) = 1) then
                              let
                                key = 
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

type_of“strlit”;
        
Definition jsonvalue_to_obj_def:
  jsonvalue_to_obj x = case x of
                         JsonObject ob => Object []
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




(* ---- *)
        
EVAL“extract_first_digits "123 000"”;
EVAL“(char_parser #"0").run  (Input 0 "0") ”;
type_of“extract_first_digits”;

(* parser that always fails *)
Definition fail_parser_def:
  fail_parser = Parser (λ input. Failure (ParserError input.Location input.String))
End

Definition zero_parser_def:
  zero_parser = const_parser (0:int) (char_parser #"0")
End

Theorem zero_parser_length_thm:
  ∀ input input'. zero_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  rw[zero_parser_def, const_parser_def]>>
  fs[const_parser_def]>>
  Cases_on ‘(char_parser #"0").run input’ >|
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

Definition one_parser_def:
  one_parser = const_parser (1:int) (char_parser #"1")
End

Theorem one_parser_length_thm:
  ∀ input input'. one_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  rw[one_parser_def, const_parser_def]>>
  fs[const_parser_def]>>
  Cases_on ‘(char_parser #"1").run input’ >|
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


               (p1.run input = Success(input1, parsed1) ∨
                p2.run input = Success(input2, parsed2)) ∧

Theorem alt_parser_length_thm:
  ∀ p1 p2 input.
    p1.run input = Success(_, _) ⇒
    (p1 <|> p2).run input = Success(_, _)
Proof
  rw[]>|
  fs[alt_parser_def]>>
  rw[]>>
  fs[alt_parser_def]>>
        rw[]>>
    ,
    rw[alt_parser_def]>>
    gs[alt_parser_def]>>
    Cases_on ‘p1.run input’ >|
    [
      fs[alt_parser_def]
      ,
      fs[]>>
      rw[]>>
        
            
Theorem alt_parser_length_thm:
  ∀ p1 p2 input input1' parsed1' input2' parsed2'.
    p1.run input = Success(input1', parsed1') ∨
    p2.run input = Success(input2', parsed2') ⇒
    (p1 <|> p2).run input = Success(input1', parsed1') ∨ (p1 <|> p2).run input = Success(input2', parsed2')
Proof
  rw[]>|
  [
    fs[alt_parser_def]
    ,
    rw[alt_parser_def]>>
    gs[alt_parser_def]>>
    Cases_on ‘p1.run input’ >|
    [
      fs[alt_parser_def]
      ,
      fs[]>>
      rw[]>>
        
        
                

Theorem alt_parser_length_thm:
  ∀ p1 p2 input input' parsed'. (p1 <|> p2).run input = Success(input', parsed') ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  rw[]>>
  fs[alt_parser_def]>>
  Cases_on ‘p1.run input’ >|
  [
    rw[]>>
    fs[]>>
    Case_on ‘Failure P0’ >|   

        

Definition digit_parser_def:
  digit_parser = (zero_parser <|> one_parser)
End

        

     


Theorem digit_parser_length_thm:
  ∀ input input'. digit_parser.run input = Success(input', parsed) ⇒ STRLEN(input'.String) < STRLEN(input.String)
Proof
  metis_tac[one_parser_length_thm, zero_parser_length_thm, digit_parser_def]>>
  fs[digit_parser_def]>>
  fs[alt_parser_def]>>
        fs[
  Cases_on ‘zero_parser.run input’ >|
  [
    fs[]>>
    rw[one_parser_length_thm]>>
    ,
    Cases_on ‘Success p’ >|
    [
      fs[]
    ]
    ,
    Cases_on ‘Success p'’ >|
    [
      fs[]
    ]
    ,
    Cases_on ‘Success p''’ >|
    
        
        
    rw[]>>
    rw[zero_parser_length_thm]>>

  rw[zero_parser_length_thm]>>
                       
  metis_tac[one_parser_length_thm, zero_parser_length_thm]>>
        
  rw[]>>
  fs[digit_parser_def, const_parser_def]>>
  Cases_on ‘(char_parser #"0").run input’ >|
  [
    fs[]>>
     metis_tac[char_parser_length_thm]>>

        
  fs[digit_parser_def, const_parser_def, char_parser_def ]>>

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


EVAL“THE (extract(( (const_parser (0:int) (char_parser #"0")) <|> (const_parser (1:int) (char_parser #"1")) ).run (Input 0 "0Something-Else")))”;
EVAL“THE (extract(( (const_parser (0:int) (char_parser #"0")) <|> (const_parser (1:int) (char_parser #"1")) ).run (Input 0 "1Something-Else")))”;

EVAL“THE (extract(didgit_parser.run (Input 0 "0")))”;
EVAL“THE (extract(didgit_parser.run (Input 0 "1")))”;
EVAL“THE (extract(didgit_parser.run (Input 0 "2")))”;
EVAL“THE (extract(didgit_parser.run (Input 0 "3")))”;
EVAL“THE (extract(didgit_parser.run (Input 0 "4")))”;
EVAL“THE (extract(didgit_parser.run (Input 0 "5")))”;
EVAL“THE (extract(didgit_parser.run (Input 0 "6")))”;
EVAL“THE (extract(didgit_parser.run (Input 0 "7")))”;
EVAL“THE (extract(didgit_parser.run (Input 0 "8")))”;
EVAL“THE (extract(didgit_parser.run (Input 0 "9")))”;
EVAL“didgit_parser.run (Input 0 "X")”;
EVAL“didgit_parser.run (Input 0 "")”;

         
     

EVAL“THE (extract(digit_parser.run (Input 0 "0123x")))”;
EVAL“digit_parser.run (Input 0 "0123x")”;
type_of“digit_parser.run”;
EVAL“0 + 10 ** 3 * 0 + 10 ** 2 * 1 + 10 ** 1 * 2 + 10 ** 0 * 3”;
EVAL“THE (extract(digit_parser_joiner (Success ((Input 0 "0123"), 0:int))))”;
EVAL“0 + 10 ** 0 * 2”;
EVAL“0 + 10 ** 0 * 1”;
EVAL“0 + 10 ** 0 * 0”;
EVAL“ 0 + 10 ** 1 * 1 + 10 ** 0 * 2”;
EVAL“ 0 + 10 ** 2 * 1 + 10 ** 1 * 2 + 10 ** 0 * 3”;
EVAL“ 0 + 10 ** 3 * 0 + 10 ** 2 * 1 + 10 ** 1 * 2 + 10 ** 0 * 3”;

          
Definition character_parser_def:
  character_parser c v = (λ x. if c = x then SOME v else NONE)                                              
End

Definition zero_parser_def:
  zero_parser = const_parser "" (char_parser #" ")
End

     

type_of“(character_parser #"0" (0:int))”
EVAL“(character_parser #"0" (0:int)) #"0"”;
EVAL“-1 * (THE ((character_parser #"1" (1:int)) #"1"))”;
type_of“-1 * (THE ((character_parser #"1" (1:int)) #"1"))”;     



(* assume the input is a string of digints with optional leading minus *)
Definition toInt_def:
  toInt s = if (first_is_minus s) then 0-t
End

Definition toInt_def:
  toInt s = if (first_is_minus s) then 0-t
End

        
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

(* ----- *)



(*
  This module contains a datatype for representing JSON objects, and
  related functions. A JSON object can be an array of objects, a
  string, an int, a bool or null, or it can be an object enclosed
  in {}, in which case it can be viewed as a key-value store of names
  (strings) and JSON objects.
*)
open preamble mlintTheory mlstringTheory

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
End
Termination
  WF_REL_TAC `measure (\x. case x of
                           | INL obj => obj_size obj
                           | INR p => obj2_size p)` >>
  rw []>>
End

val _ = export_theory();
type_of“obj_size (Array [])”;
EVAL“obj_size (Array [Int 1; Int 2; Int 3])”;
type_of“obj2_size”;

