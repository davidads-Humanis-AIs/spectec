(* Origin of generated expressions.

   A pass that generates a slice bound gives it a fresh type annotation, made
   here, so that later passes and the translation to AL can tell it apart from
   a premise written in the specification, whatever its region. Type
   annotations are not printed, and transformations that rebuild an
   expression keep its annotation; one that makes a new annotation drops the
   mark, which is the safe direction. Annotations are compared by physical
   identity, and held weakly. *)

open Util.Source

module Marks = Ephemeron.K1.Make (struct
  type t = Ast.typ
  let equal = ( == )
  let hash = Hashtbl.hash
end)

let slice_bounds : unit Marks.t = Marks.create 64

let slice_bound at =
  let t = Ast.BoolT $ at in
  Marks.replace slice_bounds t ();
  t

let is_slice_bound t = Marks.mem slice_bounds t
