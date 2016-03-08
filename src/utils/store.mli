(** Pure references *)

module type S =
  sig
    type key

    val key_eq : key -> key -> bool

    val print_key : key -> Format.formatter -> unit

    type 'a t

    val empty : 'a t

    (** [lookup x s] returns the value bound to [x] in [s] *)
    val lookup : key -> 'a t -> 'a

    (** [fresh v s] returns a new key [x] and store [s'] such that the bindings in [s] are in [s'], and [x] is bound to [v] in [s'] *)
    val fresh : 'a -> 'a t -> key * 'a t

    (** [update x v s] when [x] is already bound in [s] returns [s'] in which it is bound to [v] *)
    val update : key -> 'a -> 'a t -> 'a t
  end

module Ref : S

module Dyn : S
