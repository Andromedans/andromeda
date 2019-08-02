(** Source code locations *)

type known = {
  filename: string;
  start_line: int;
  start_col: int;
  end_line: int;
  end_col: int;
}

type t =
  | Unknown
  | Known of known

(** Type of located things. *)
type 'a located = { it: 'a; at: t}

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

let mark ~at x = { it = x; at }

let union l1 l2 =
  match l1, l2 with
  | Known {filename = fn1;
           start_line = sl1; start_col = sc1;
           end_line = el1; end_col = ec1},
    Known {filename = fn2;
           start_line = sl2; start_col = sc2;
           end_line = el2; end_col = ec2} ->
     assert (fn1 = fn2);
     let (sl, sc) = if (sl1 < sl2) || (sl1 = sl2 && sc1 < sc2)
       then (sl1, sc1) else (sl2, sc2)
     and (el, ec) = if (el1 > el2) || (el1 = el2 && ec1 > ec2)
       then (el1, ec1) else (el2, ec2) in
     Known { filename = fn1;
             start_line = sl; start_col = sc;
             end_line = el; end_col = ec; }
  | Unknown, l | l, Unknown ->
     (* We should record the fact that we made this location up. *)
     l

let from_to l1 l2 =
  match l1, l2 with
  | (Known {filename = fn1; start_line; start_col; _},
     Known {filename = fn2; end_line; end_col; _}) ->
     assert (fn1 = fn2);
     Known { filename = fn1; start_line; start_col; end_line; end_col; }
  | Unknown, l | l, Unknown ->
     (* We should record the fact that we made this location up. *)
     l


module Json =
struct
  let location = function
    | Unknown -> Json.tag "Unknown" []
    | Known {filename; start_line; start_col; end_line; end_col} ->
       Json.tuple [Json.String filename;
                   Json.Int start_line;
                   Json.Int start_col;
                   Json.Int end_line;
                   Json.Int end_col ]

  let located to_json {it; at} =
    if !Config.json_location
    then Json.tuple [to_json it; location at]
    else to_json it
end
