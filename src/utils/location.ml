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

(** Type of located things. *)
type 'a located = { thing: 'a; loc: t}

let print loc ppf =
  match loc with

  | Unknown -> Format.fprintf ppf "?:?"

  | Known {filename; start_line; start_col; end_line; end_col} ->
    if start_line = end_line
    then
      Format.fprintf ppf "File \"%s\", line %d, characters %d-%d"
        filename start_line (1 + start_col) end_col
    else
      Format.fprintf ppf "File \"%s\", line %d character %d - line %d character %d"
        filename start_line (1 + start_col) end_line end_col

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

let locate x loc = { thing = x; loc }

module Json =
struct
  let location = function
    | Unknown -> Json.tag "location" "Unknown" []
    | Known {filename; start_line; start_col; end_line; end_col} ->
       Json.tag "location" "Known" [Json.String filename;
                                    Json.Int start_line;
                                    Json.Int start_col;
                                    Json.Int end_line;
                                    Json.Int end_col ]

  let located to_json {thing; loc} =
    Json.record "located" ["thing", to_json thing;
                           "loc", location loc]
end
