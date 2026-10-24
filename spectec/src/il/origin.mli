(* Origin of generated expressions *)

(* A fresh type annotation for a slice bound i + n <= |a| that a pass
   generated, rather than a premise written in the specification. *)
val slice_bound : Util.Source.region -> Ast.typ

(* Whether a type annotation was made by [slice_bound]. *)
val is_slice_bound : Ast.typ -> bool
