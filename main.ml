open Utils

type input = File of string | String of string

type action = Parse | Typecheck | Intermediate | Michelson

let parse_args () =
  let type_p = ref false in
  let compile_p = ref false in
  let intermediate_p = ref false in
  let inputs = ref [] in
  let output = ref None in
  let add_string s = inputs := String s :: !inputs in
  let set_output s = output := Some s in
  let spec_list = [
     "compile", Arg.Set compile_p, "Compile files";
     "typecheck", Arg.Set type_p, "Typecheck files";
     "string", Arg.String add_string, "String input";
     "output", Arg.String set_output, "Output file";
     "intermediate", Arg.Set intermediate_p, "Intermediate tree";
  ] in
  let spec_variants (name, x, y) = ["-"^String.sub name 0 1, x, y; "-"^name, x, y; "--"^name, x, y] in
  let spec_list = List.flatten (List.map spec_variants spec_list) in
  let parse_file f = inputs := File  f :: !inputs in
  Arg.parse spec_list parse_file "Lamtez compiler";
  !type_p, !compile_p, !intermediate_p, List.rev !inputs, !output

let log msg =
  let start = "\x1B[1;31m" and finish = "\x1B[0;0m" in
  print_endline ("["^start^msg^finish^"]")



let parse_file type_p compile_p intermediate_p output_spec input_spec =
  let name, lexstream = match input_spec with
    | File name -> log("Reading file "^name); name, Lexing.from_channel(open_in name)
    | String s -> log("Reading string "^s); s, Lexing.from_string(s)
  in
  log "Parsing file";
  let (ast_type_decl, ast_store_decl, ast_code) as ast = 
    try Parser.contract Lexer.read lexstream with 
    | Lexer.Lexing_error msg as e -> print_endline("Lexing error: "^msg); raise e 
    | Parser.Error as e -> 
      print_endline("parsing: error at K."^string_of_int (Lexing.lexeme_start lexstream));
      raise e
  in
  print_endline (String_of_ast.string_of_contract ast^"\n");
  if type_p || intermediate_p || compile_p then begin

    log "Typechecking";
    let ctx = Standard_ctx.ctx in
    let ctx, t_store, t_code = Typecheck.typecheck_contract ctx ast in

    log ("Typechecked with resulting type: "^String_of_ast.string_of_type t_code);
    print_endline ("\nContext:\n"^Typecheck_ctx.string_of_t ctx);
    if intermediate_p || compile_p then begin

      log "Intermediate tree";
      let interm = Intermediate_of_ast.compile_expr ctx ast_code in
      print_endline ("\nIntermediate tree:\n"^String_of_intermediate.string_of_untyped_expr (fst interm));
      (* print_endline ("\nIntermediate tree:\n"^String_of_intermediate.string_of_typed_expr interm); *)

      if compile_p then
        log "Compiling";
        let t_store = Intermediate_of_ast.compile_etype ctx t_store in
        let code = Michelson_of_intermediate.compile_contract t_store interm in

        match output_spec with
        | None -> print_endline code
        | Some name ->
          let f = open_out name in
          output_string f code;
          print_endline ("Wrote result in "^name)
    end
  end


let main () =
  let type_p, compile_p, intermediate_p, filenames, output = parse_args() in
    List.map (parse_file type_p compile_p intermediate_p output) filenames
;;

main()
