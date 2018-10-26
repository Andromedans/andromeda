(** Source code locations

    To show the user what piece of code is causing errors, we tag each construct
    with a corresponding location in the source. This consists of the name of
    the file and starting and ending position in the file (i.e. line and column
    number).

    To keep type definitions clean, we write each definition with two mutually
    dependent types, say [ty] and [ty'], where [ty] consists of a [ty'] and a
    location, while [ty'] declares the constructors, which refer back to [ty].

    For example, annotated terms of untyped lambda calculus may be defined as
    {[
      type term = term' * Location.t
      and term' =
        | Var of string
        | App of term * term
        | Abs of string * term
    ]} *)

(** Type of locations. *)
type t

(** Type of located things. *)
type 'a located = private {thing: 'a; loc: t}

(** Print a location. *)
val print : t -> Format.formatter -> unit

(** Unknown location. *)
val unknown : t

(** Make a location from two lexing positions. *)
val make : Lexing.position -> Lexing.position -> t

(** Create a located thing. *)
val locate : 'a -> t -> 'a located

(** [union l1 l2] combines l1 and l2 to span from (min l1.beg l2.beg) to the
    end of (max l1.end l2.end). l1 and l2 have to come from the same file.
    If either l1 or l2 is Unknown, the other one is used. *)
val union : t -> t -> t

(** [from_to l1 l2] combines [l1] and [l2] to span from [l1.beg] to [l2.end]. Only
   valid if both locations come from the same file. *)
val from_to : t -> t -> t

(** Conversion to JSON *)
module Json :
sig
  (** Convert a location to JSON *)
  val location : t -> Json.t

  (** Convert a located thing to JSON *)
  val located : ('a -> Json.t) -> 'a located -> Json.t
end

