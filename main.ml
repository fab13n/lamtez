open Utils
open Printf

module IoA = Intermediate_of_ast
module SoI = String_of_intermediate
module SoA = String_of_ast
module MoI = Michelson_of_intermediate
module I   = Intermediate

type compilation_level = LUnspecified | LAst | LTypecheck | LIntermediate | LMichelson
type input = (string * Lexing.lexbuf) option ref

type arguments = {
  does_parse:     bool;
  does_typecheck: bool;
  does_interm:    bool;
  does_michelson: bool;
  does_store:     bool;
  does_run:       bool;
  in_ltz:         Lexing.lexbuf;
  in_ltz_name:    string;
  out_tz:         out_channel;
  out_tz_name:    string;
  in_store:       (string*Lexing.lexbuf) option;
  out_store:      string option;
  run_param:      string option;
  client:         string;
}
  

let parse_args() = 

  let level      = ref LUnspecified in (* Compilation level *)
  let input      = ref (Lexing.from_channel stdin) in (* LTZ source code *)
  let input_name = ref "stdin" in (* used for logging msgs *)
  let output     = ref None in (* code output filename, defaults to stdout *)
  let run_param  = ref None in (* opt. param to run the program, litteral string *)
  let client     = ref None in (* Tezos-client executable name *)
  let in_store   = ref None in (* store content input file name: name*lexbuf option *)
  let out_store  = ref None in (* store content output file name *)
  let emb_store  = ref false in (* do we process embedded store values? *)

  let set_level  l ()     = match !level with LUnspecified -> level := l | _ -> failwith "Contradicatory compilation levels" in
  let set_string r s      = match !r     with None -> r     := Some s | _ -> failwith "Contradictory outputs" in
  let set_input_string s  = input := Lexing.from_string s; input_name := s in
  let set_input_file s    = input := Lexing.from_channel (open_in s); input_name := s in
  let set_in_store_str  s = in_store := Some ("litteral", Lexing.from_string s) in
  let set_in_store_file n = in_store := Some (n, Lexing.from_channel (open_in n)) in
  

    let spec_list = [
     "c", "compile",        Arg.Unit (set_level LMichelson),    "Compile input to Michelson";
     "i", "intermediate",   Arg.Unit (set_level LIntermediate), "Only generate intermediate tree";
     "t", "typecheck",      Arg.Unit (set_level LTypecheck),    "Only typecheck input";
     "a", "ast",            Arg.Unit (set_level LAst),          "Only parse input";
     "s", "string",         Arg.String set_input_string,        "Input from string";
     "f", "file",           Arg.String set_input_file,          "Input from file";
     "o", "output",         Arg.String (set_string output),     "Output to file";
     "E", "embedded-store", Arg.Set    emb_store,                "Output embedded storage";
     "r", "run",            Arg.String (set_string run_param),  "Run the program";
     "F", "store-file",     Arg.String (set_in_store_file),     "Get storage value from file";
     "S", "store-string",   Arg.String (set_in_store_str),      "Get storage from string";
     "O", "store-output",   Arg.String (set_string out_store),  "Write storage data to this file";
     "C", "client",         Arg.String (set_string client),     "Set the tezos-client commnad";
     ] in
  let spec_variants (l, name, x, y) = ["-"^l, x, y; "-"^name, x, y; "--"^name, x, y] in
  let spec_list = List.flatten (List.map spec_variants spec_list) in
  Arg.parse spec_list set_input_file "Lamtez compiler";

  let does_run = ! run_param != None in
  let does_store = (!in_store, !run_param, !emb_store) <> (None, None, false) in
  let level = if !level=LUnspecified then LMichelson else !level in
  if does_store && level!= LMichelson then
    failwith "need a source file to compile store data"; (* TODO intermediate is enough *)
  let does_michelson = does_store || level=LMichelson in
  let does_interm = does_michelson || level=LIntermediate in
  let does_typecheck = does_interm || level=LTypecheck in
  let does_parse = true in
  { does_parse; does_typecheck; does_interm; does_michelson; does_store; does_run;
    in_ltz = !input;
    in_ltz_name = !input_name;
    out_tz = (match !output with None | Some "-" -> stdout | Some n -> open_out n);
    out_tz_name = (match !output with None | Some "-" -> "stdout" | Some n -> n);
    out_store = (match !out_store with None -> None | Some n -> Some n);
    in_store = !in_store;
    run_param = !run_param;
    client = (match !client with None -> "tezos-client" | Some n -> n);
  }


let log msg =
  let start = "\x1B[1;31m" and finish = "\x1B[0;0m" in
  print_endline ("["^start^msg^finish^"]")

let run_program command program storage data = 

  let args = [| command; 
                "run"; "program"; "text:"^program;
                "on"; "storage"; storage;
                "and"; "input"; data |] in

  let pid = Unix.create_process command args 
    Unix.stdin Unix.stdout Unix.stderr in
  let _, _ = Unix.waitpid [] pid in
  ()

let parse_file a =

  log ("Parsing "^a.in_ltz_name);
  let (ast_type_decl, ast_store_decl, ast_code) as ast = 
    try Parser.contract Lexer.read a.in_ltz with 
    | Lexer.Lexing_error p ->
      let msg = Printf.sprintf "File \"%s\", line %d, character %d: Lexing error"
        p.Lexing.pos_fname p.Lexing.pos_lnum p.Lexing.pos_cnum in
      print_endline msg;
      raise Exit
    | Parser.Error -> 
      let p = Lexing.lexeme_start_p a.in_ltz in
      let p = Printf.sprintf "File \"%s\", line %d, character %d: Lexing error"
        p.Lexing.pos_fname p.Lexing.pos_lnum p.Lexing.pos_cnum in
      print_endline("parsing: error at "^p);
      raise Exit
    | Not_impl msg ->
      print_endline ("\nNot implemented: "^msg);
      Printexc.print_backtrace stdout;
      raise Exit
  in

  (* Generate the fully type-checked contract. *)
  if a.does_typecheck then
    log "Typechecking";
    let ctx = Standard_ctx.ctx in
    let typed_contract = 
      try Typecheck.typecheck_contract ctx ast with
      | Typing(loc, msg) ->
        print_endline ("\n"^Ast.string_of_loc loc^": "^msg);
        raise Exit
      | Not_impl msg ->
        print_endline ("\nNot implemented: "^msg);
        Printexc.print_backtrace stdout;
        raise Exit
    in
    log ("Typechecked succesfully. code :: "^
         SoA.string_of_type typed_contract.Typecheck.param_type^" -> "^
         SoA.string_of_type typed_contract.Typecheck.result_type^"; storage :: "^
         SoA.string_of_type typed_contract.Typecheck.storage_type
         );

      (* Compile the typechecked contract into intermediate tree. *)
      if a.does_interm then
      log "Intermediate tree";
      let int_contract = IoA.compile_contract typed_contract in
      let int_code = int_contract.I.code in
       print_endline ("Intermediate tree:\n"^SoI.string_of_untyped_expr (fst int_code));
      if not a.does_michelson then
        print_endline @@ "\nIntermediate tree:\n" ^ 
                         SoI.string_of_typed_expr int_contract.I.code;

      (* Compile into Michelson source code.*)
      if a.does_michelson then
        log "Compiling";
        try
          let m_contract = MoI.compile_contract int_contract in
          output_string a.out_tz m_contract.MoI.code;
          if a.out_tz != stdout then close_out a.out_tz;
          log @@ "Contract written to "^a.out_tz_name;

          if a.does_store then
            let store_tz = match a.in_store, m_contract.MoI.storage_init with
              | None, Some content -> content
              | Some (name, lexbuf), _ -> 
                log @@ "Read store data from "^name;
                Data_of_lexbuf.store_of_lexbuf
                  typed_contract int_contract m_contract lexbuf
              | None, None -> assert false
            in

            if a.does_run then begin
              let p = match a.run_param with Some p -> p | _ -> assert false in
              let param = Data_of_lexbuf.parameter_of_lexbuf 
                typed_contract int_contract (Lexing.from_string p) in
              run_program a.client m_contract.MoI.code store_tz param 
            end;

            begin match a.out_store with None -> () | Some n ->
              log @@ "Writing stored data to "^n;
              let ch = if n="-" then stdout else open_out n in
              output_string ch store_tz
            end

      with Not_impl msg ->
        print_endline ("\nNot implemented: "^msg);
        Printexc.print_backtrace stdout;
        raise Exit

let main () =
  try parse_file (parse_args())
  with Exit -> ()
;;

main()
