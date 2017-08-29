(* Indent code in a Michelson-compliant way. *)
let indent code = 
  let lines = String.split_on_char '\n' code in
  let rec f (open_braces, indented_lines) line =
    let line = String.trim line in
    let indentation = List.hd open_braces in
    let indentation =
      if line = "" then 0
      else if String.get line 0 = '}' then indentation 
      else indentation+2 in
    let line = String.make indentation ' '^line in
    let open_braces = ref open_braces in
    String.iteri 
      ( fun i k -> match k with
      | '{' -> open_braces := i :: !open_braces
      | '}' -> open_braces := List.tl !open_braces
      |  _  -> ()
      ) line;
    (!open_braces, line::indented_lines)
  in
  let _, indented_lines = List.fold_left f ([-2], []) lines in
  String.concat "\n" (List.rev indented_lines)

let endline_regexp = Str.regexp ";? *\\(#.*\\)?\n"

(* Remove comments at ends-of-lines and replace returns with semicolons,
 * thus producing a single-line Michelson code.*)
let single_line code = 
  Str.global_replace endline_regexp "; " code
