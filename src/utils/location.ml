(** Source code locations *)

type t =
  | Unknown
  | Known of known

and known = {
  filename: string;
  start_line: int;
  start_col: int;
  end_line: int;
  end_col: int;
}

let print loc ppf =
  match loc with
  | Unknown -> Print.print ppf "?:?"
  | Known {filename; start_line; start_col; end_line; end_col} ->
    if start_line = end_line then
      Print.print ppf "%s:%d:%d-%d" filename start_line start_col end_col
    else
      Print.print ppf "%s:%d:%d-%d:%d" filename start_line start_col end_line end_col

let unknown = Unknown

(** Dismantles a lexing position into its filename, line and column. *)
let dismantle lexpos =
  let filename = lexpos.Lexing.pos_fname
  and line = lexpos.Lexing.pos_lnum
  and col = lexpos.Lexing.pos_cnum - lexpos.Lexing.pos_bol in
  filename, line, col

let make start_lexpos end_lexpos =
  let start_filename, start_line, start_col = dismantle start_lexpos
  and end_filename, end_line, end_col = dismantle end_lexpos in
  assert (start_filename = end_filename);
  Known {filename = start_filename; start_line; start_col; end_line; end_col}

let of_lexeme lex =
  make (Lexing.lexeme_start_p lex) (Lexing.lexeme_end_p lex)
