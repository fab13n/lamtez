let _DEBUG_ = false

(* Indent code in a Michelson-compliant way. *)
let indent open_char close_char code =
  let lines = String.split_on_char '\n' code in
  let rec f (open_braces, indented_lines, prev_closing_indent) line =
    let line = String.trim line in
    let indentation = List.hd open_braces in
    let indentation = match line, String.get (line^"\x1B") 0, prev_closing_indent with
      | "", _, _ -> 0
      | _, c, _ when c = close_char -> indentation
      | _, c, Some prev_indentation when c = open_char -> prev_indentation
      | _ -> indentation + 2 in
    let prev_closing_indent =
      if line = String.make 1 close_char then Some(List.hd open_braces) else None in
    let indented_line = String.make indentation ' '^line in
    let open_braces = ref open_braces in
    String.iteri
      ( fun i k ->
        if      k = open_char  then open_braces := i :: !open_braces
        else if k = close_char then open_braces := List.tl !open_braces
        else ()
      ) indented_line;
    if _DEBUG_ then begin
      let prev_closing_indent = match prev_closing_indent with Some n -> string_of_int n | None -> "-" in
      let open_braces = String.concat ", " (List.map string_of_int !open_braces) in
      print_endline(Printf.sprintf "after line \"%s\": indentation = %d, open_braces = %s, pci = %s"
        line indentation open_braces prev_closing_indent);
    end;
    (!open_braces, indented_line::indented_lines, prev_closing_indent)
  in
  let _, indented_lines, _ = List.fold_left f ([-2], [], None) lines in
  String.concat "\n" (List.rev indented_lines)

let endline_regexp = Str.regexp ";? *\\(#.*\\)?\n"

(* Remove comments at ends-of-lines and replace returns with semicolons,
 * thus producing a single-line Michelson code.*)
let single_line code =
  Str.global_replace endline_regexp "; " code
