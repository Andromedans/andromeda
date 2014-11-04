type 'a cont = ('a -> 'b) -> 'b

(** A valid type *)
type ty

(** The fact that a given term has a given type *)
type judge

(** Is a given term a type, and if so, convert it to a type. *)
val is_type : Syntax.context -> Syntax.term -> judge_ty cont

(** Check that the given term has the given type. *)
val check : Syntax.context -> judge -> judge_ty -> judge cont

(** Synthesize a name. *)
val syn_name : Syntax.context -> Common.name -> judge

(** Synthesize an ascription. *)
val syn_ascribe : Syntax.context -> judge -> judge_ty -> judge

(** Synthesize an application. *)
val syn_app : Syntax.context -> judge -> judge -> judge cont

(** Synthesize a lambda. *)
val syn_lambda : Syntax.context -> Common.name -> judge_ty -> Input.term -> judge cont

(** Synthesize an application. *)
val syn_app : Syntax.context -> judge -> Input.term -> 
