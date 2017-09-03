open Utils

type compilation_level = LUnspecified | LAst | LTypecheck | LIntermediate | LCompile
type input = (string * Lexing.lexbuf) option ref


type arguments = {
  level:   compilation_level;
  in_name: string;
  input:   Lexing.lexbuf;
  out_name: string;
  output:  out_channel;
  data:    string option
}
  
let does_typecheck    a = match a.level with LUnspecified -> assert false | LAst-> false | _ -> false
let does_intermediate a = match a.level with LUnspecified -> assert false | LIntermediate | LCompile -> true | _ -> false
let does_compile      a = match a.level with LUnspecified -> assert false | LCompile -> true | _ -> false
let does_data         a = a.data != None

let parse_args() = 

  let level  = ref LUnspecified in
  let input  = ref None in
  let output = ref None in
  let data   = ref None in

  let set_level  l ()    = match !level with LUnspecified -> level := l | _ -> failwith "Contradicatory compilation levels" in
  let set_string r s     = match !r     with None -> r     := Some s | _ -> failwith "Contradictory outputs" in
  let set_input_string s = match !input with None -> input := Some(s, Lexing.from_string s) | _ -> failwith "Contradictory inputs" in
  let set_input_file s   = match !input with None -> input := Some(s, Lexing.from_channel (open_in s)) | _ -> failwith "Contradictory inputs" in

  let spec_list = [
     "compile",      Arg.Unit (set_level LCompile),      "Compile input";
     "intermediate", Arg.Unit (set_level LIntermediate), "Intermediate tree";
     "typecheck",    Arg.Unit (set_level LTypecheck),    "Typecheck input";
     "ast",          Arg.Unit (set_level LAst),          "Only parse input";
     "string",       Arg.String set_input_string,        "String input";
     "file",         Arg.String set_input_file,          "Input file";
     "output",       Arg.String (set_string output),     "Output file";
     "data",         Arg.String (set_string data),       "Output data file";
  ] in
  let spec_variants (name, x, y) = ["-"^String.sub name 0 1, x, y; "-"^name, x, y; "--"^name, x, y] in
  let spec_list = List.flatten (List.map spec_variants spec_list) in
  Arg.parse spec_list set_input_file "Lamtez compiler";
  if !data != None then 
    (match !level with 
    | LCompile | LUnspecified -> level := LCompile 
    | _ -> failwith "need to compile to get data" (* TODO intermediate is enough *)
    );
  { level    = (match !level  with LUnspecified    -> LCompile | l -> l);
    in_name  = (match !input  with Some(name, _)   -> name     | None -> "stdin");
    input    = (match !input  with Some(_,lexbuf)  -> lexbuf   | _ -> Lexing.from_channel stdin);
    output   = (match !output with None            -> stdout   | Some f -> open_out f);
    out_name = (match !output with None            -> "stdout" | Some f -> f);
    data     = !data }

let log msg =
  let start = "\x1B[1;31m" and finish = "\x1B[0;0m" in
  print_endline ("["^start^msg^finish^"]")

let parse_file a =
  log ("Parsing "^a.in_name);
  let (ast_type_decl, ast_store_decl, ast_code) as ast = 
    try Parser.contract Lexer.read a.input with 
    | Lexer.Lexing_error p ->
      let msg = Printf.sprintf "File \"%s\", line %d, character %d: Lexing error"
        p.Lexing.pos_fname p.Lexing.pos_lnum p.Lexing.pos_cnum in
      print_endline msg;
      raise Exit
    | Parser.Error as e -> 
      print_endline("parsing: error at K."^string_of_int (Lexing.lexeme_start a.input));
      raise e
  in
  if does_typecheck a then
    log "Typechecking";
    let ctx = Standard_ctx.ctx in
    let ctx, t_store, t_code = 
      try Typecheck.typecheck_contract ctx ast with
      | Typing(loc, msg) ->
        print_endline ("\n"^Ast.string_of_loc loc^": "^msg);
        raise Exit
    in
    log ("Typechecked succesfully. resulting type = "^String_of_ast.string_of_type t_code);

    if does_intermediate a then
      log "Intermediate tree";
      let interm = Intermediate_of_ast.compile_expr ctx ast_code in
      print_endline ("Intermediate tree:\n"^String_of_intermediate.string_of_untyped_expr (fst interm));
      (* print_endline ("\nIntermediate tree:\n"^String_of_intermediate.string_of_typed_expr interm); *)

      if does_compile a then
        log "Compiling";
        let t_store = Intermediate_of_ast.compile_etype ctx t_store in
        let code = Michelson_of_intermediate.compile_contract t_store interm in
        output_string a.output code;
        log ("Contract written to "^a.out_name);
        if does_data a then
          let data_name = match a.data with Some x -> x | None -> assert false in
          let data_file = open_out data_name in
          log("Initialization data written to "^data_name);
          not_impl "init data writing"


let main () =
  try parse_file (parse_args())
  with Exit -> ()
;;

main()
