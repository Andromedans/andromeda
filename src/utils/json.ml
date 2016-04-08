(* Even though there might be JSON libraries for OCaml, we implement our own
   because there really is not that much work to do, and not depending
   on a bunch of external libraries can be a Good Thing.
 *)


(** A simplified type for representing JSON values *)
type t =
  | String of string
  | Int of int
  | List of t list
  | Dict of (t * t) list

let of_ty ty lst =
  let lst = List.map (fun (key, value) -> (String key, value)) lst in
  Dict ((String "_ty", String ty) :: lst)

let tuple lst = List lst

let record = of_ty

let tag ty tag data = of_ty ty ["tag", String tag; "data", List data]

let rec print_json data ppf =
  match data with

  | String s -> Format.fprintf ppf "%s" (String.escaped s)

  | Int k -> Format.fprintf ppf "%d" k

  | List lst -> Format.fprintf ppf "[%t]" (Print.sequence print_json "," lst)

  | Dict lst ->
     Format.fprintf ppf "{%t}" (Print.sequence print_entry "," lst)

and print_entry (label, data) ppf =
  Format.fprintf ppf "@[<hov 2>%t@] :@ @[<hov 2>%t@]"
                 (print_json label)
                 (print_json data)

