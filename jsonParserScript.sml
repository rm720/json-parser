open stringTheory;
open extra_stringTheory;
open PSLPathTheory; (* CONS_def *)
open listTheory; (* LENGTH_CONS TAKE*)
open arithmeticTheory; (* SUC_ONE_ADD *)
open sexpcodeTheory; (* STRING_def*)
open source_valuesTheory; (* option_def *)
open optionTheory; (* SOME THE NONE*)
open 


(* Input: (position where parsing starts):num, (source string to parse): string *)
Datatype:
  Input = <| Location : num;
             String: string;
          |>
End

(* Parse error: (position of parse problem): num, (error message): string*)
Datatype:
  ParserError = ParserError num string
End

Datatype:
  Output = Failure ParserError | Success (Input # α)
End

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

(*
CONS_HEAD_REST
TAIL_MONO
LENGTH_TL
OPTION_MAP_DEF
*)

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

EVAL“JsonArray ([JsonBool T])”;

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

(* ------------------------------------ *)
(* Parser Functior*)      
Definition pure_parser_def:
  pure_parser x = Parser (λ input. Success (input, x))
End
        

(* Draft *)
Definition char_parser_def:
  char_parser x =
  Parser (λ input.
            case inputUncons input of
              NONE =>
                Failure (ParserError (input.Location) "E")
            | SOME (y, ys) =>
                if y = x then
                  Success (ys, x)
                else
                  Failure (ParserError (input.Location) "E"))
End

(* Draft *)
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
    (* IS SOME inputUncons input *)
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

type_of“const_parser  "d" (char_parser (CHR 34))”;

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

type_of“whitespace_parser”;
type_of“whitespace_parser.run”;
EVAL“whitespace_parser.run (Input 0 " 123")”;  

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
       
EVAL“many_whitespace_parser.run (Input 0 "      123")”;     
        

(* elevated function application *)
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

EVAL“(string_parser "null").run (Input 0 "nullk")”;  
        

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

type_of“jsonBool_parser.run”;
EVAL“jsonBool_parser.run (Input 0 "truenull")”;
EVAL“jsonBool_parser.run (Input 0 "falsenull")”;
                

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
(*----------------------------------*)

                     
        
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
(* TODO generalise and call "many" *)
Definition normal_string_parser_def:
  normal_string_parser =
  Parser (
    λ input. FOLDL (SWAP_ARGS string_parser_joiner) (Success (input, "")) (REPLICATE (LENGTH input.String) normal_char_parser)
    )
End

EVAL“CHR 34”;
EVAL“special_char_parser.run (Input 0 ([CHR 34] ++ "normal_string" ++ [CHR 34] ++ "another_normal_string"))”;
EVAL“normal_string_parser.run (Input 0 ("normal_string" ++ [CHR 34] ++ "another_normal_string"))”;                          
EVAL“(special_char_parser <&> (normal_string_parser <&> special_char_parser)).run  (Input 0 ([CHR 34] ++ "normal_string" ++ [CHR 34] ++ "another_normal_string"))”;
type_of“parser_sequenser_string”;
type_of“normal_string_parser”;
type_of“special_char_parser”;
type_of“apply_parser”;
type_of“parser_sequenser_string special_char_parser”;
type_of“special_char_parser <&> (normal_string_parser <&> special_char_parser)”;
type_of“(normal_string_parser <&> special_char_parser)”;
EVAL“"123" ++ "456"”;



Definition jsonString_parser_def:
  jsonString_parser = Parser (λ input.
                                case (special_char_parser <&> (normal_string_parser <&> special_char_parser)).run input of
                                  Success (input', parsed_string) =>  Success (input', JsonString parsed_string)
                                | Failure err => Failure err
                             )
End
        

        
Definition jsonValue_parser_def:
  jsonValue_parser = jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser
End

EVAL“jsonValue_parser.run (Input 0 "123 null")”;
EVAL“jsonValue_parser.run (Input 0 "null 123 null")”;
EVAL“jsonValue_parser.run (Input 0 "true 123 null")”;

EVAL“jsonValue_parser.run (Input 0 (([CHR 34] ++ "normal_string" ++ [CHR 34]) ++ " 123 null"))”;

EVAL“jsonValue_parser.run (Input 0 ([CHR 34] ++ "normal_string" ++ [CHR 34]))”;
EVAL“jsonValue_parser.run (Input 0 ([CHR 34] ++ "" ++ [CHR 34]))”;
EVAL“jsonValue_parser.run (Input 0 ([CHR 34] ++ "345" ++ [CHR 34]))”;
EVAL“jsonValue_parser.run (Input 0 "null")”;
EVAL“jsonValue_parser.run (Input 0 "true")”;
EVAL“jsonValue_parser.run (Input 0 "false")”;

(* List parser *)

(* Consumes a compulsory single comma *)
Definition comma_parser_def:
  comma_parser = const_parser "" (char_parser #",")
End

(* TODO: optional comma parser, for the end of the list *)

EVAL“comma_parser.run (Input 0 "qwe")”;
EVAL“(many_whitespace_parser <&> (comma_parser <&> many_whitespace_parser)).run (Input 0 "   ,   qwe")”;
        
(* consumes a compulsory single comma surrounded by optional whitespaces. E.g.: "     ,     "  *)
Definition separator_parser_def:
  separator_parser = (many_whitespace_parser <&> (comma_parser <&> many_whitespace_parser))
End

EVAL“separator_parser.run (Input 0 "   ,   qwe")”;
EVAL“separator_parser.run (Input 0 ",qwe")”;
        
Definition open_bracket_parser_def:
  open_bracket_parser = (many_whitespace_parser <&> ((const_parser "" (char_parser #"[")) <&> many_whitespace_parser))
End
        
EVAL“open_bracket_parser.run (Input 0 "   [   qwe")”;

Definition closed_bracket_parser_def:
  closed_bracket_parser = (many_whitespace_parser <&> ((const_parser "" (char_parser #"]")) <&> many_whitespace_parser))
End

Definition many_json_parser_helper_def[tailrecursive]:
  many_json_parser_helper input accumulator =

  (* Try to parse JsonValue *)
  case (jsonValue_parser.run input) of

    (* Found first JsonValue *)
    Success (input', parsed) =>
      (
      (* Append first JsonValue to the result *)
      let accumulator' = accumulator ++ [parsed]
      in

        (* Try to find a comma *)
        case separator_parser.run input' of

          (* Found comma *)       
          Success (input'', _) =>

            (* Repeat all over again *)
            many_json_parser_helper input'' accumulator'

        (* No comma *)
        | Failure _ =>

            (* Return first JsonValue and associated next input*)
            Success (input', accumulator')
      )
  (* No JsonValue *)
  | Failure _ =>
      (* Return as it was*)
      Success (input, accumulator)
End

        
Definition many_json_parser_def:
  many_json_parser = Parser (λ input. many_json_parser_helper input [])
End

(* combine the 2 above*)
Definition many_json_parser_def:
  many_json_parser = Parser (λ input.
                               let  many_json_parser_helper input accumulator =

  (* Try to parse JsonValue *)
  case (jsonValue_parser.run input) of

    (* Found first JsonValue *)
    Success (input', parsed) =>
      (
      (* Append first JsonValue to the result *)
      let accumulator' = accumulator ++ [parsed]
      in

        (* Try to find a comma *)
        case separator_parser.run input' of

          (* Found comma *)       
          Success (input'', _) =>

            (* Repeat all over again *)
            many_json_parser_helper input'' accumulator'

        (* No comma *)
        | Failure _ =>

            (* Return first JsonValue and associated next input*)
            Success (input', accumulator')
      )
  (* No JsonValue *)
  | Failure _ =>
      (* Return as it was*)
      Success (input, accumulator) in many_json_parser_helper input [])
End



        
(* combine 3 *)
Definition jsonArray_parser_def:
  jsonArray_parser = Parser (λ input.
                          
                          (* try to parse "[" *)
                          case open_bracket_parser.run input of

                            (* found "[" *)
                            Success (input', _) =>

                              let
                                          many_json_parser = Parser (λ input.
                               let  many_json_parser_helper input accumulator =

  (* Try to parse JsonValue *)
  case (jsonValue_parser.run input) of

    (* Found first JsonValue *)
    Success (input', parsed) =>
      (
      (* Append first JsonValue to the result *)
      let accumulator' = accumulator ++ [parsed]
      in

        (* Try to find a comma *)
        case separator_parser.run input' of

          (* Found comma *)       
          Success (input'', _) =>

            (* Repeat all over again *)
            many_json_parser_helper input'' accumulator'

        (* No comma *)
        | Failure _ =>

            (* Return first JsonValue and associated next input*)
            Success (input', accumulator')
      )
  (* No JsonValue *)
  | Failure _ =>
      (* Return as it was*)
      Success (input, accumulator) in many_json_parser_helper input [])
                                        in

                              (* try to parse list of jsons *)
                              (case many_json_parser.run input' of

                                 (* found list of jsons *)
                                 Success (input'', parsed'') =>

                                   (* try to parse "]" *)
                                   (case closed_bracket_parser.run input'' of

                                      (* found "]" *)
                                      Success (input''', _) => Success (input''', JsonArray parsed'')

                                    (* did not find "]"*)
                                    | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))

                               (* did not find json values *)
                               | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))

                          (* did not find "[" *)
                          | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))
                       )
End
       

Definition jsonArray_parser_def:
  jsonArray_parser = Parser (λ input.
                          
                          (* try to parse "[" *)
                          case open_bracket_parser.run input of

                            (* found "[" *)
                            Success (input', _) =>

                              (* try to parse list of jsons *)
                              (case many_json_parser.run input' of

                                 (* found list of jsons *)
                                 Success (input'', parsed'') =>

                                   (* try to parse "]" *)
                                   (case closed_bracket_parser.run input'' of

                                      (* found "]" *)
                                      Success (input''', _) => Success (input''', JsonArray parsed'')

                                    (* did not find "]"*)
                                    | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))

                               (* did not find json values *)
                               | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))

                          (* did not find "[" *)
                          | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))
                       )
End
      



       
Definition jsonValue_parser_def:
  jsonValue_parser = jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> jsonArray_parser
End



























        


        
(* TESTS *)
EVAL“many_json_parser.run (Input 0 "null , null  ,  null")”;
EVAL“many_json_parser.run (Input 0 "null , null")”;
EVAL“many_json_parser.run (Input 0 "null")”;
EVAL“many_json_parser.run (Input 0 "")”;           
EVAL“many_json_parser.run (Input 0 "null,")”;
EVAL“many_json_parser.run (Input 0 "null , null  ,  null,")”;
EVAL“many_json_parser.run (Input 0 ",null , null  ,  null")”;



Definition jsonValue_parser_def[tailrecursive]:
  jsonValue_parser = jsonBool_parser
                     <|> jsonNull_parser
                         <|> jsonNumber_parser
                             <|> jsonString_parser
                                 <|> (Parser (λ input.
                          case open_bracket_parser.run input of
                            Success (input', _) =>

                              (let  many_json_parser_helper input accumulator =
                                    case (jsonValue_parser.run input) of
                                      Success (input', parsed) =>
                                        (
                                        let accumulator' = accumulator ++ [parsed]
                                        in
                                          case separator_parser.run input' of  
                                            Success (input'', _) =>
                                              many_json_parser_helper input'' accumulator'
                                          | Failure _ =>
                                              Success (input', accumulator')
                                        )
                                    | Failure _ =>
                                        Success (input, accumulator) in)
                           
                              (let many_json_parser = Parser (λ input. many_json_parser_helper input []) in)
                              
                              (case many_json_parser.run input' of
                                 Success (input'', parsed'') =>
                                   (case closed_bracket_parser.run input'' of
                                      Success (input''', _) => Success (input''', JsonArray parsed'')
                                    | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                               | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                          | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))
                       )
  )
End



EVAL“jsonValue_parser.run (Input 0 "[null , null  ,  null ]")”;


Definition jsonValue_parser_def[tailrecursive]:
  jsonValue_parser = jsonBool_parser
                     <|> jsonNull_parser
                     <|> jsonNumber_parser
                     <|> jsonString_parser
                     <|> (Parser (λ input.
                            case open_bracket_parser.run input of
                              Success (input', _) =>
                                let
                                  fun many_json_parser_helper input accumulator =
                                    case (jsonValue_parser.run input) of
                                      Success (input', parsed) =>
                                        let
                                          val accumulator' = accumulator ++ [parsed]
                                        in
                                          case separator_parser.run input' of
                                            Success (input'', _) =>
                                              many_json_parser_helper input'' accumulator'
                                          | Failure _ =>
                                              Success (input', accumulator')
                                        end
                                    | Failure _ =>
                                        Success (input, accumulator)
                                in
                                  let
                                    val many_json_parser = Parser (λ input. many_json_parser_helper input [])
                                  in
                                    case many_json_parser.run input' of
                                      Success (input'', parsed'') =>
                                        (case closed_bracket_parser.run input'' of
                                           Success (input''', _) => Success (input''', JsonArray parsed'')
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'"))
                                  end
                                end
                            | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'")))
End




                          
        

(* dumb simple examples *)

Definition jp_def[tailrecursive]:
  (jsonValue_parser =  jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> jsonArray_parser)  /\
  (jsonArray_parser = Parser (λ input. Success (input, (JsonArray []))))
End      

EVAL“JsonArray []”;

Definition a_def:
  f = Parser (λ input. Success (input, (JsonArray []))) ∧
  g = Parser (λ input. f.run input)
Termination
  cheat
End

Definition f_def[tailrecursive]:
  (f x = g x) ∧
  (g x = h x) ∧
  (h x = f x)
End
      
        
Definition f_def:
  (jsonValue_parser = Parser (λ input. (jsonArray_parser).run input)) ∧
  (many_json_parser_helper input = jsonValue_parser.run input) ∧
  (many_json_parser = Parser (λ input. many_json_parser_helper input) ∧
  (jsonArray_parser = Parser (λ input. many_json_parser.run input))
Termination
  cheat
End


Definition a_def[tailrecursive]:
  (f x = Parser (λ input. Success (Input 0 "", ""))) ∧
  (g x = h x) ∧
  (h x = f x) ∧
  (k x = f x)
End

Definition jp_def[tailrecursive]:
  (
  many_json_parser_helper input accumulator =
  case (jsonValue_parser.run input) of
    Success (input', parsed) =>
      (
      let accumulator' = accumulator ++ [parsed]
      in
        case separator_parser.run input' of   
          Success (input'', _) =>
            many_json_parser_helper input'' accumulator'
        | Failure _ =>
            Success (input', accumulator')
      )
  | Failure _ =>
      Success (input, accumulator)
  ) ∧

  (
  many_json_parser = Parser (λ input. many_json_parser_helper input [])
  ) ∧
  (
  jsonArray_parser = Parser (λ input.
                               case open_bracket_parser.run input of
                                 Success (input', _) =>
                                   (case many_json_parser.run input' of
                                      Success (input'', parsed'') =>
                                        (case closed_bracket_parser.run input'' of
                                           Success (input''', _) => Success (input''', JsonArray parsed'')
                                         | Failure _ => Failure (ParserError input''.Location ("Expected ']', but found '" ++ input''.String ++ "'")))
                                    | Failure _ => Failure (ParserError input'.Location ("Expected json value, but found '" ++ input'.String ++ "'")))
                               | Failure _ => Failure (ParserError input.Location ("Expected '[', but found '" ++ input.String ++ "'"))
                            )
  )∧
  (jsonValue_parser = jsonBool_parser <|> jsonNull_parser <|> jsonNumber_parser <|> jsonString_parser <|> jsonArray_parser)
End






        



EVAL“list_parser.run (Input 0 "")”;
EVAL“list_parser.run (Input 0 "[")”;
EVAL“list_parser.run (Input 0 "[]")”;
EVAL“list_parser.run (Input 0 "   [   ]   ")”;
EVAL“list_parser.run (Input 0 "   [ null , null , true,      false  ]   ")”;
EVAL“list_parser.run (Input 0 "   [ null , null , true,      false,  ]   ")”;


EVAL“jsonArray_parser.run (Input 0 "   [ null , null , true,      false, [], null ]   ")”;
                     
                     


                     

EVAL“(many_parser (comma_parser)).run (Input 0 ",,,,,,,123")”;
EVAL“(jsonValue_parser <&> (many_parser (comma_parser))).run (Input 0 ",,,,,,,123")”;
type_of“jsonValue_parser”;
EVAL“”;



        





















   


type_of“whitespace_parser”;
type_of“whitespace_parser.run”;
EVAL“whitespace_parser.run (Input 0 " ")”;
type_of“(many_parser whitespace_parser)”;



        

Definition many_parser_def:
  many_parser = Parser (λ input. many_loop_helper input)
End



        

Definition many_helper_def:
  many_helper p =
  λ input. case (p.run input) of
    Success (input', _) => many_helper p input'
  | Failure _ => Success (input, "")
Termination
  WF_REL_TAC ‘measure (λ input. LENGTH(input.String))’ THEN
End

Definition helper0_def:
  helper0 x = x-1
End

Definition helper1_def:
  helper1 x =
  let r = helper0 x
  in
    if r > 0 then  helper1 r  else r
End                                  
Termination
  WF_REL_TAC `measure (λn. n)`>>
  >> rw []
End

        
        
type_of“many_helper ”;    

EVAL“separator_parser.run (Input 0 ",qwe")”;
        




        

        
Definition many_parser_def:
  many_parser (Parser p) = Parser(λ output =
                                     case input.String of
                                       [] =>  Failure (ParserError input.Location "Expected normal character, but reached end of string")
                                     | _ =>
                                         (
                                         case (normal_char_parser.run input) of
                                              Failure e => 
                                           
          next_input = Input input.Location cs;
          next_output = next_ascii next_input
        in
          case next_output of
            Failure err => Failure err
          | Success (updated_input, updated_string) =>
              Success (updated_input, (CONS next_char updated_string))
Termination
  WF_REL_TAC ‘measure LENGTH o String o FST’ THEN
  rw []
End








        

Definition separator_parser_def:
  separator_parser = const_parser "" (char_parser #",")
End

EVAL“separator_parser.run (Input 0 ",qwe")”;
EVAL“separator_parser.run (Input 0 "qwe")”;
type_of“separator_parser”;

Definition start_list_parser_def:
  start_list_parser = const_parser "" (char_parser #"[")
End
           







           

        

(* -----------------------------------------------------------------------*)
(* --------------------------------- DRAFT -------------------------------*)
(* -----------------------------------------------------------------------*)


EVAL“ jsonValue_parser.run (Input 0 ([CHR 34] ++ "normal string" ++ [CHR 34] ++ "another_normal_string"))”;
EVAL“ jsonValue_parser.run (Input 0 ("123"))”;
EVAL“ jsonValue_parser.run (Input 0 ("null"))”;
EVAL“ jsonValue_parser.run (Input 0 ("true"))”;
EVAL“ jsonValue_parser.run (Input 0 ("false"))”;

   

EVAL“ jsonString_parser.run (Input 0 ([CHR 34] ++ "normal_string" ++ [CHR 34] ++ "another_normal_string"))”;


type_of“normal_char_parser”;
type_of“normal_char_parser.run”;
type_of“normal_char_parser.run (Input 0 "qwerty")”;
EVAL“normal_char_parser.run (Input 0 "qwerty")”;
EVAL“normal_char_parser.run (Input 0 (CONS (CHR 34) "some string"))”;
EVAL“(parser_sequenser_string () ())”;
EVAL“normal_char_parser (Input 0 "qwerty")”;



EVAL“REPLICATE (LENGTH "s") normal_char_parser”;
type_of“REPLICATE (LENGTH "s") normal_char_parser”;
type_of“special_char_parser.run (Input 0 ("normal_string" ++ [CHR 34] ++ "another_normal_string"))”;
EVAL“special_char_parser.run (Input 0 ("normal_string" ++ [CHR 34] ++ "another_normal_string"))”;
EVAL“special_char_parser.run (Input 0 ([CHR 34] ++ "normal_string" ++ [CHR 34] ++ "another_normal_string"))”;

type_of“(parser_sequenser_string special_char_parser normal_string_parser).run ”;
EVAL“(parser_sequenser_string normal_string_parser special_char_parser).run  (Input 0 ([CHR 34] ++ "normal_string" ++ [CHR 34] ++ "another_normal_string"))”;
EVAL“(parser_sequenser_string normal_string_parser special_char_parser).run  (Input 0 ([CHR 34] ++ "normal_string" ++ [CHR 34] ++ "another_normal_string"))”;
EVAL“(normal_string_parser <&> special_char_parser).run  (Input 0 ([CHR 34] ++ "normal_string" ++ [CHR 34] ++ "another_normal_string"))”;

      
      
type_of“normal_string_parser.run”;
EVAL“normal_string_parser.run (Input 0 ("normal_string" ++)”;
EVAL“"qwerty" + CHR() ”;
EVAL“CHR 34”;
type_of“CHR 34”;
type_of“CONS”;
EVAL“CONS  #"0" "123"”;
EVAL“SNOC  #"0" "123"”;
EVAL“ "123" ++ [#"0"]”;
EVAL“ "normal_string" ++ [CHR 34] ++ "another_normal_string"”;
EVAL“normal_string_parser.run (Input 0 ("normal_string" ++ [CHR 34] ++ "another_normal_string"))”;
EVAL“normal_string_parser.run (Input 0 "")”;
EVAL“"" ++ [CHR 34]”;
EVAL“normal_string_parser.run (Input 0 "")”;
EVAL“normal_string_parser.run (Input 0 ("" ++ [CHR 34]))”;
EVAL“normal_string_parser.run (Input 0 ("normal_string" ++ [CHR 34] ++ "another_normal_string"))”;
   
   
Definition parser_sequenser_string_def:
  parser_sequenser_string (Parser p2) (Parser p1) =
  Parser (λ input1.
            case p1 input1 of
              Success (input2, parsed1) =>
                                (
                                case p2 input2 of
                                  Success (input3, parsed2) => Success (input3, (parsed1 ++ parsed2))
                                | Failure err => Failure err
                                )
                              | Failure err => Failure err
         )
End
      

Definition string_parser_def:
  string_parser s =
  Parser (λ input.
            case (FOLDL (SWAP_ARGS parser_joiner) (Success (input, "")) (MAP char_parser s)) of 
              Success (input1, parsed) =>
                (case input1.String of
                   "" => Success (input1, parsed)
                 | _ => Failure (ParserError input1.Location ("Expected '" ++ s ++ "', but found '" ++ input.String ++ "'"))
                )
            | Failure (ParserError location message) => Failure (ParserError location ("Expected '" ++ s ++ "', but found '" ++ input.String ++ "'"))
         )                          
End

type_of“string_parser”;
type_of“parser_joiner”;
type_of“MAP parser_sequenser_string”;
type_of“[1]*3”;
type_of“REPLICATE 3 (NUM 1)”;
EVAL“REPLICATE 3 (NUM 1)”;
EVAL“GENLIST (fn _ => NUM 1) 3”;
EVAL“REPLICATE (LENGTH "qwe") normal_char_parser”;
EVAL“LENGTH "qwe"”;



            
        

Definition parser_joiner_def:
  parser_joiner f p = λ input.
      case input of
        Success (input1, parsed1) =>
          (case p.run(input1) of
             Success (input2, parsed2)  => Success (input2, (f parsed2 parsed1))
           |  Failure err => Failure err)
      | Failure err => Failure err
End

                     

Definition prototype_parser_def:
  prototype_parser p = let f = 
        
     

Definition many_parser_def:
  many_parser (Parser p) = Parser(λ input =
                                     case (p input) of
                                       Success (next_input, parsed) => 
End
                                     

Definition many_parser_def:
  many_parser (Parser p) = Parser(λ output =
                                     case input.String of
                                       [] =>  Failure (ParserError input.Location "Expected normal character, but reached end of string")
                                     | _ =>
                                         (
                                         case (normal_char_parser.run input) of
                                              Failure e => 
                                           
          next_input = Input input.Location cs;
          next_output = next_ascii next_input
        in
          case next_output of
            Failure err => Failure err
          | Success (updated_input, updated_string) =>
              Success (updated_input, (CONS next_char updated_string))
Termination
  WF_REL_TAC ‘measure LENGTH o String o FST’ THEN
  rw []
End



                                     


Definition many_parser_def:
  many_parser p =
    let
      parser = (p <&> many_parser p) <|> pure_parser ""
    in
      fmap_parser FLAT parser
Termination
  WF_REL_TAC ‘measure (LENGTH o String o FST o SND)’ >>
  rw []
End

Definition escape_char_parser_def:
  escape_char_parser =
    char_parser #"\\" <*> parse_if "escape character" (λ c. c = #"\"" ∨ c = #"\\")
End

Definition stringLiteral_parser_def:
  stringLiteral_parser =
    char_parser #"\"" <*>
    many_parser (normal_char_parser <|> escape_char_parser) <*>
    char_parser #"\""
End







                            
                            


Define ‘fact x = if x = 0 then 1 else x * fact(x-1)’;
EVAL“fact 10”;


Definition next_ascii_helper_def:
  (next_ascii_helper s =
    case s of
    | [] => []
    | (c::cs) => (CHR (ORD c + 1))::(next_ascii_helper cs))
Termination
  WF_REL_TAC ‘measure LENGTH’ >>
  rw []
End


type_of“next_ascii”;
EVAL“next_ascii "qwerty"”;


Definition _def:
  next_ascii input =
    case input.String of
      [] => Success (input, "")
    | (c::cs) =>
        let
          next_char = CHR (ORD c + 1);
          next_input = Input input.Location cs;
          next_output = next_ascii next_input
        in
          case next_output of
            Failure err => Failure err
          | Success (updated_input, updated_string) =>
              Success (updated_input, (CONS next_char updated_string))
Termination
  WF_REL_TAC ‘measure LENGTH o String o FST’ THEN
  rw []
End

type_of“next_ascii”;
type_of“CONS”;
EVAL“SNOC #"c" "aaa"”;

type_of“FST”;
type_of“SND”;
type_of“CROSS_DEF”;
EVAL“FST ((Input 0 "qwe"), "sdf")”;
EVAL“SND ((Input 0 "qwe"), "sdf")”;
EVAL“SND (Input 0 "qwe")”;







                




        
    
type_of“many.run”;
EVAL“many.run (Input 0 "qwerty")”;



        
EVAL“normal_char_parser.run (Input 0 "some string")”;


        

EVAL“special_char_parser.run (Input 0 (CONS (CHR 34) "some string"))”;
    

type_of“char_parser (CHR 34)”;
type_of“CONS”;
EVAL“CONS (CHR 34) ""”;
type_of“(char_parser (CHR 34)).run (Input 0 (CONS (CHR 34) ""))”;
EVAL“(char_parser (CHR 34)).run (Input 0 (CONS (CHR 34) ""))”;
type_of“ const_parser "sss" (char_parser (CHR 34))”;
EVAL“(const_parser "" (char_parser (CHR 34))).run (Input 0 (CONS (CHR 34) ""))”;

type_of“λ (Input i string). const_parser "sss" (char_parser (CHR 34))”;

type_of“parser_sequenser_string”;
type_of“parser_sequenser_string ”;  

                   

        





        

Definition string_literal_parser_def:
  string_literal_parser = Parser(λ input.
                                        if 
                                         
            
type_of“jsonValue_parser.run (Input 0 "123")”;
EVAL“jsonValue_parser.run (Input 0 "123")”;
EVAL“jsonValue_parser.run (Input 0 "null")”;
EVAL“jsonValue_parser.run (Input 0 "false")”;
EVAL“jsonValue_parser.run (Input 0 "true")”;
EVAL“jsonValue_parser.run (Input 0 "1true")”;
EVAL“jsonValue_parser.run (Input 0 "t1rue")”;
EVAL“jsonValue_parser.run (Input 0 "")”;

type_of“string_psrser”;
type_of“(string_psrser "N").run”;
type_of“Input 0 "N"”;
type_of“(string_psrser "null").run (Input 0 "null")”;
EVAL“(string_psrser "null").run (Input 0 "null")”;
type_of“(char_psrser #"n").run (Input 0 "null")”;
type_of“(char_psrser #"n").run”;

EVAL“(char_psrser #"n").run (Input 0 "n")”;

EVAL“(char_psrser #"n").run (Input 0 "null")”;
                    
type_of“((string_psrser "n") <&> (string_psrser "u")).run  (Input 0 "nu")”;
EVAL“(parser_sequenser_string (string_psrser "u") (string_psrser "n")).run  (Input 0 "nu")”;

                                
EVAL“(string_parser "null").run (Input 0 "null")”;
type_of“parser_sequenser_string (char_parser #"N") (char_parser #"U")”;
EVAL“"123" ++ "456"”;
EVAL“JsonString "\"mystring\""”;




(* json_to_num *)
Definition json_to_num_def:
  json_to_num jv =
    case jv of
      JsonNumber n => n
    | _ => 0
End

EVAL“json_to_num (JsonNumber 3)”;

(* json_to_bool *)
Definition json_to_bool_def:
  json_to_bool jv =
    case jv of
      JsonBool b => b
    | _ => F
End

(* json_to_string *)
Definition json_to_string_def:
  json_to_string jv =
    case jv of
      JsonString s => s
    | _ => ""
End

(* json_to_list *)
Definition json_to_list_def:
  json_to_list jv =
    case jv of
      JsonArray lst => lst
    | _ => []
End

(* json_to_object *)
Definition json_to_object_def:
  json_to_object jv =
    case jv of
      JsonObject obj => obj
    | _ => []
End


EVAL“string_psrser”



        

EVAL“CHR 34”;
EVAL“ORD #"\""”;

type_of“ORD”;
type_of“ordn”;

type_of“#"'"”;
type_of“#"/"”;
type_of“#"\b"”;
type_of“#"\f"”;
type_of“#"\n"”;
type_of“#"\r"”;
type_of“#"\t"”;







val _ = export_theory();

