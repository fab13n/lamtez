open Utils

type input = File of string | String of string

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



let parse_file type_p compile_p intermediate_p output_spec input_spec =
  let name, lexstream = match input_spec with
    | File name -> name, Lexing.from_channel(open_in name)
    | String s -> s, Lexing.from_string(s)
  in
  print_endline ("\n"^String.make 80 '*');
  print_endline ("Contract "^name^":");
  let ast = try Parser.main Lexer.read lexstream with
  | Lexer.Lexing_error msg -> [], Tree.EString ("lexing: "^msg)
  | Parser.Error -> [], Tree.EString("parsing: error at "^
    string_of_int (Lexing.lexeme_start lexstream))
  in
  print_endline (TreePrint.string_of_program ast^"\n");
  if type_p || intermediate_p || compile_p then begin
    let ctx, t = Typing.typecheck_contract DefaultContext.ctx ast in
    print_endline ("\nResulting type: "^TreePrint.string_of_type t);
    print_endline ("\nContext:\n"^TypingContext.string_of_t ctx); 
    if intermediate_p || compile_p then begin
      let i = Interm_of_lamtez.compile_exprT ctx (snd ast) in
      print_endline ("\nIntermediate tree:\n"^Interm_of_lamtez.string_of_iTypedExpr i);
      if compile_p then
        let code = Compile.compile_contract i in
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