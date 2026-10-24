# Conditions implied by an earlier trap

These tests run `remove_trapped_ifs`, one of the AL readability passes, on small
instruction lists. Each group shows a condition that follows from an earlier
trap check and is removed, next to similar ones that do not follow, or whose
removal would skip an evaluation that can fail, and are kept.

```ocaml
open Util.Source
open Al.Ast
open Al.Al_util

let ratT = Il.Ast.NumT `RatT $ no_region
let intT = Il.Ast.NumT `IntT $ no_region
let var ?(note = natT) x = varE x ~note
let list x = varE x ~note:(listT natT)
let nat i = numE (`Nat (Z.of_int i)) ~note:natT
let ( + ) e1 e2 = binE (`AddOp, e1, e2) ~note:natT
let ( * ) e1 e2 = binE (`MulOp, e1, e2) ~note:natT
let cmp op e1 e2 = binE (op, e1, e2) ~note:boolT
let len e = lenE e ~note:natT
let idx e1 e2 = accE (e1, idxP e2) ~note:natT
let slice e1 e2 e3 = accE (e1, sliceP (e2, e3)) ~note:(listT natT)
(* $nat$($rat$(e) / $rat$(d)) *)
let div e d =
  let rat e = cvtE (e, `NatT, `RatT) ~note:ratT in
  cvtE (binE (`DivOp, rat e, rat (nat d)) ~note:ratT, `RatT, `NatT) ~note:natT
let upto e k n = iterE (e, (ListN (n, Some k), [])) ~note:boolT
let trap c = ifI (c, [trapI ()], [])
let return e = returnI (Some e)
let show il = print_endline (Al.Print.string_of_instrs (Il2al.Transpile.remove_trapped_ifs il))
```

The basic case. A trap check is a fact for what comes after it:

```ocaml
# show [
    trap (cmp `GtOp (var "j" + var "n") (len (list "a")));
    ifI (cmp `EqOp (var "n") (nat 0), [return (nat 0)], [
      ifI (cmp `LtOp (var "j") (len (list "a")), [return (idx (list "a") (var "j"))], [])
    ])
  ];;
 If (((j + n) > |a|)) {
   Trap
 }
 If ((n = 0)) {
   Return 0
 }
 Else {
   Return a[j]
 }
- : unit = ()
```

A fact is dropped when its variable is bound again, also in a branch of an if
that does not trap. Here the check is kept:

```ocaml
# show [
    ifI (cmp `GtOp (var "x") (nat 0), [trapI ()], [letI (var "x", nat 1)]);
    ifI (cmp `LeOp (var "x") (nat 0), [return (nat 9)], []);
    return (nat 0)
  ];;
 If ((x > 0)) {
   Trap
 }
 Else {
   Let x = 1
 }
 If ((x <= 0)) {
   Return 9
 }
 Return 0
- : unit = ()
# show [
    ifI (cmp `GtOp (var "x") (nat 0), [trapI ()], [popI (var "x")]);
    ifI (cmp `LeOp (var "x") (nat 0), [return (nat 9)], []);
    return (nat 0)
  ];;
 If ((x > 0)) {
   Trap
 }
 Else {
   Pop x
 }
 If ((x <= 0)) {
   Return 9
 }
 Return 0
- : unit = ()
```

The same holds for a nested trap check `If c_1 { If c_2 { Trap } }`. Without the
assignment, the second check is removed; with it, it is kept:

```ocaml
# show [
    ifI (cmp `GtOp (var "y") (nat 0), [trap (cmp `GtOp (var "x") (nat 0))], []);
    ifI (cmp `GtOp (var "y") (nat 0), [
      ifI (cmp `LeOp (var "x") (nat 0), [return (nat 9)], [])
    ], []);
    return (nat 0)
  ];;
 If ((y > 0)) {
   If ((x > 0)) {
     Trap
   }
 }
 If ((y > 0)) {
   Return 9
 }
 Return 0
- : unit = ()
# show [
    ifI (cmp `GtOp (var "y") (nat 0), [trap (cmp `GtOp (var "x") (nat 0))], []);
    letI (var "x", nat 1);
    ifI (cmp `GtOp (var "y") (nat 0), [
      ifI (cmp `LeOp (var "x") (nat 0), [return (nat 9)], [])
    ], []);
    return (nat 0)
  ];;
 If ((y > 0)) {
   If ((x > 0)) {
     Trap
   }
 }
 Let x = 1
 If ((y > 0)) {
   If ((x <= 0)) {
     Return 9
   }
 }
 Return 0
- : unit = ()
```

All facts are dropped after an instruction that changes the state, also when it
is in a branch:

```ocaml
# show [
    ifI (cmp `LtOp (var "x") (len (list "a")), [trapI ()], [appendI (nat 3, list "a")]);
    ifI (cmp `GeOp (var "x") (len (list "a")), [return (nat 9)], []);
    return (nat 0)
  ];;
 If ((x < |a|)) {
   Trap
 }
 Else {
   a :+ 3
 }
 If ((x >= |a|)) {
   Return 9
 }
 Return 0
- : unit = ()
# show [
    ifI (cmp `LtOp (var "x") (idx (list "a") (nat 0)), [trapI ()],
      [replaceI (list "a", idxP (nat 0), nat 5)]);
    ifI (cmp `GeOp (var "x") (idx (list "a") (nat 0)), [return (nat 9)], []);
    return (nat 0)
  ];;
 If ((x < a[0])) {
   Trap
 }
 Else {
   a[0] := 5
 }
 If ((x >= a[0])) {
   Return 9
 }
 Return 0
- : unit = ()
```

A division by a literal is only defined if it is exact, so a check containing
one is removed only if the same division has already been evaluated, or is
evaluated next by the instructions the check guards:

```ocaml
# show [
    trap (cmp `GtOp (var "n") (var "m"));
    ifI (cmp `LeOp (div (var "n") 2) (div (var "m") 2), [return (nat 9)], []);
    return (nat 0)
  ];;
 If ((n > m)) {
   Trap
 }
 If (($nat$(($rat$(n) / $rat$(2))) <= $nat$(($rat$(m) / $rat$(2))))) {
   Return 9
 }
 Return 0
- : unit = ()
# show [
    trap (cmp `GtOp (div (var "n") 2) (var "m"));
    ifI (cmp `LeOp (div (var "n") 2) (var "m"), [return (nat 9)], []);
    return (nat 0)
  ];;
 If (($nat$(($rat$(n) / $rat$(2))) > m)) {
   Trap
 }
 Return 9
 Return 0
- : unit = ()
# let check body = [
    trap (cmp `GtOp (var "i" + div (var "n" * var "m") 8) (len (list "a")));
    ifI (cmp `EqOp (var "n") (nat 0), [return (list "a")], [
      ifI (cmp `LeOp (var "i" + div (var "m") 8) (len (list "a")), body, [])
    ])
  ] in
  show (check [
    letI (list "b", slice (list "a") (var "i") (div (var "m") 8));
    return (list "b")
  ]);
  show (check [return (list "a")]);;
 If (((i + $nat$(($rat$((n * m)) / $rat$(8)))) > |a|)) {
   Trap
 }
 If ((n = 0)) {
   Return a
 }
 Else {
   Let b = a[i : $nat$(($rat$(m) / $rat$(8)))]
   Return b
 }

 If (((i + $nat$(($rat$((n * m)) / $rat$(8)))) > |a|)) {
   Trap
 }
 If ((n = 0)) {
   Return a
 }
 Else if (((i + $nat$(($rat$(m) / $rat$(8)))) <= |a|)) {
   Return a
 }
- : unit = ()
```

The facts are not carried into an iteration that binds a variable they mention,
and only an iteration over an index (no other variables) gets the bound of its
index as a fact:

```ocaml
# show [
    trap (cmp `LeOp (var "x") (nat 0));
    ifI (iterE (cmp `GtOp (var "x") (nat 0),
           (ListN (nat 1, Some "k"), [("x", list "ys"); ("k", list "ys")])) ~note:boolT,
      [return (nat 9)], []);
    return (nat 0)
  ];;
 If ((x <= 0)) {
   Trap
 }
 If ((x > 0)^(k<1){x <- ys, k <- ys}) {
   Return 9
 }
 Return 0
- : unit = ()
# show [
    trap (cmp `LeOp (var "k") (nat 0));
    ifI (upto (cmp `GtOp (var "k") (nat 0)) "k" (var "n"), [return (nat 9)], []);
    return (nat 0)
  ];;
 If ((k <= 0)) {
   Trap
 }
 If ((k > 0)^(k<n){}) {
   Return 9
 }
 Return 0
- : unit = ()
# show [
    trap (cmp `GtOp (var "i" + var "n" * var "m") (len (list "a")));
    ifI (upto (cmp `LeOp (var "i" + var "k" * var "m" + var "m") (len (list "a"))) "k" (var "n"),
      [return (nat 9)], []);
    return (nat 0)
  ];;
 If (((i + (n * m)) > |a|)) {
   Trap
 }
 Return 9
 Return 0
- : unit = ()
```

A natural-number literal does not make the other operand a natural number:

```ocaml
# show [
    trap (cmp `EqOp (var "z" ~note:intT) (nat 0));
    ifI (cmp `GtOp (var "z" ~note:intT) (nat 0), [return (nat 9)], []);
    return (nat 0)
  ];;
 If ((z = 0)) {
   Trap
 }
 If ((z > 0)) {
   Return 9
 }
 Return 0
- : unit = ()
```

The same in an iteration, as in a packed vector load: the check is removed when
the next instruction reads the same slices, and kept when nothing does:

```ocaml
# let bound = upto (cmp `LeOp (var "i" + div (var "k" * var "m") 8 + div (var "m") 8) (len (list "a"))) "k" (var "n") in
  let reads = iterE (slice (list "a") (var "i" + div (var "k" * var "m") 8) (div (var "m") 8),
    (ListN (var "n", Some "k"), [])) ~note:(listT (listT natT)) in
  let check body = [
    trap (cmp `GtOp (var "i" + div (var "m" * var "n") 8) (len (list "a")));
    ifI (bound, body, []);
    return (list "a")
  ] in
  show (check [letI (list "bs", reads); return (list "bs")]);
  show (check [return (nat 9)]);;
 If (((i + $nat$(($rat$((m * n)) / $rat$(8)))) > |a|)) {
   Trap
 }
 Let bs = a[(i + $nat$(($rat$((k * m)) / $rat$(8)))) : $nat$(($rat$(m) / $rat$(8)))]^(k<n){}
 Return bs
 Return a

 If (((i + $nat$(($rat$((m * n)) / $rat$(8)))) > |a|)) {
   Trap
 }
 If ((((i + $nat$(($rat$((k * m)) / $rat$(8)))) + $nat$(($rat$(m) / $rat$(8)))) <= |a|)^(k<n){}) {
   Return 9
 }
 Return a
- : unit = ()
```

## Nested checks

`If c { If c' { ... } }` becomes `If c' { ... }` when c' and the earlier trap
checks imply c. This evaluates c' where it was not evaluated before, so c' must
not be able to fail:

```ocaml
# let check c' = [
    ifI (cmp `GtOp (var "n") (len (list "a")), [trap c'], []);
    ifI (cmp `LeOp (var "n") (len (list "a")), [ifI (c', [return (nat 9)], [])], []);
    return (nat 0)
  ] in
  show (check (cmp `EqOp (var "b" ~note:boolT) (boolE true ~note:boolT)));
  show (check (cmp `EqOp (div (var "x") 2) (nat 0)));
  show (check (iterE (var "b" ~note:boolT,
    (ListN (div (var "x") 2, Some "k"), [("b", list "bs"); ("k", list "ks")])) ~note:boolT));;
 If ((n > |a|)) {
   If ((b = true)) {
     Trap
   }
 }
 If ((b = true)) {
   Return 9
 }
 Return 0

 If ((n > |a|)) {
   If (($nat$(($rat$(x) / $rat$(2))) = 0)) {
     Trap
   }
 }
 If ((n <= |a|)) {
   If (($nat$(($rat$(x) / $rat$(2))) = 0)) {
     Return 9
   }
 }
 Return 0

 If ((n > |a|)) {
   If (b^(k<$nat$(($rat$(x) / $rat$(2)))){b <- bs, k <- ks}) {
     Trap
   }
 }
 If ((n <= |a|)) {
   If (b^(k<$nat$(($rat$(x) / $rat$(2)))){b <- bs, k <- ks}) {
     Return 9
   }
 }
 Return 0
- : unit = ()
```

## Slice bounds as assertions

`assert_slice_bounds` turns a bound `e1 + e2 <= |a|` without else into an
assertion when the sideconditions pass generated it for a slice, and the
instructions it guards begin by reading that slice. A generated bound carries
the pass's insertion marker, the type annotation `bound` made here:

```ocaml
# let show il = print_endline (Al.Print.string_of_instrs (Il2al.Transpile.assert_slice_bounds il)) in
  let r = {left = {file = "rule"; line = 2; column = 9}; right = {file = "rule"; line = 2; column = 17}} in
  let bound = Il.Origin.slice_bound r in
  let read x = letI (list x, accE (list "a", sliceP (nat 0, nat 1)) ~at:r ~note:(listT natT)) in
  let check body = [
    ifI (binE (`LeOp, nat 0 + nat 1, len (list "a")) ~at:r ~note:bound, body, []);
    return (nat 0)
  ] in
  show (check [read "b"; return (list "b")]);
  show (check [ifI (boolE false ~note:boolT, [read "b"; return (list "b")], [])]);
  show (check [read "unused"]);
  show (check [letI (list "a", list "c"); read "b"; return (list "b")]);
  show (check [appendI (nat 3, list "a"); read "b"; return (list "b")]);;
 Assert (((0 + 1) <= |a|))
 Let b = a[0 : 1]
 Return b
 Return 0

 If (((0 + 1) <= |a|)) {
   If (false) {
     Let b = a[0 : 1]
     Return b
   }
 }
 Return 0

 If (((0 + 1) <= |a|)) {
   Let unused = a[0 : 1]
 }
 Return 0

 If (((0 + 1) <= |a|)) {
   Let a = c
   Let b = a[0 : 1]
   Return b
 }
 Return 0

 If (((0 + 1) <= |a|)) {
   a :+ 3
   Let b = a[0 : 1]
   Return b
 }
 Return 0
- : unit = ()
```

A bound written in the rule is a condition of the rule, and stays a check even
when the same read follows. With `a = []`, this returns 0; as an assertion, it
would fail. The written bound has no marker, whatever its region: the same
region as the slice (`r`), that of the premise (`p`), or none:

```ocaml
# let show il = print_endline (Al.Print.string_of_instrs (Il2al.Transpile.assert_slice_bounds il)) in
  let r = {left = {file = "rule"; line = 2; column = 9}; right = {file = "rule"; line = 2; column = 17}} in
  let p = {left = {file = "rule"; line = 3; column = 6}; right = {file = "rule"; line = 3; column = 22}} in
  let check ~at_bound ~at_read = [
    ifI (binE (`LeOp, nat 0 + nat 1, len (list "a")) ~at:at_bound ~note:boolT, [
      letI (list "b", accE (list "a", sliceP (nat 0, nat 1)) ~at:at_read ~note:(listT natT));
      return (list "b")
    ], []);
    return (nat 0)
  ] in
  show (check ~at_bound:r ~at_read:r);
  show (check ~at_bound:p ~at_read:r);
  show (check ~at_bound:no_region ~at_read:no_region);;
 If (((0 + 1) <= |a|)) {
   Let b = a[0 : 1]
   Return b
 }
 Return 0

 If (((0 + 1) <= |a|)) {
   Let b = a[0 : 1]
   Return b
 }
 Return 0

 If (((0 + 1) <= |a|)) {
   Let b = a[0 : 1]
   Return b
 }
 Return 0
- : unit = ()
```

A generated bound also loses its marker when it comes to stand for a written
condition. Here the trap check gives `i <= j`, so the bound `j + 1 <= |a|`
implies the written `i + 1 <= |a|` and `i <= |a|`. In the first case the
written condition comes between the bound and the read, and
`remove_trapped_ifs` removes it; `keep_slice_bounds`, run on the AL of each
rule before the readability passes, drops the marker because the bound does
not guard the read directly. In the second the written condition encloses the
bound, and `remove_trapped_ifs` replaces it with the bound. Both stay checks:
with `i = j = |a| = 0`, they return 0, and an assertion would fail.

```ocaml
# let pipeline il =
    il
    |> Il2al.Transpile.keep_slice_bounds
    |> Il2al.Transpile.remove_trapped_ifs
    |> Il2al.Transpile.assert_slice_bounds in
  let show il = print_endline (Al.Print.string_of_instrs (pipeline il)) in
  let r = {left = {file = "rule"; line = 2; column = 9}; right = {file = "rule"; line = 2; column = 17}} in
  let bound () =
    binE (`LeOp, var "j" + nat 1, len (list "a")) ~at:r ~note:(Il.Origin.slice_bound r) in
  let read = [letI (list "b", slice (list "a") (var "j") (nat 1)); return (list "b")] in
  let check outer inner = [
    trap (cmp `GtOp (var "i") (var "j"));
    ifI (outer, [ifI (inner, read, [])], []);
    return (nat 0)
  ] in
  show (check (bound ()) (cmp `LeOp (var "i" + nat 1) (len (list "a"))));
  show (check (cmp `LeOp (var "i") (len (list "a"))) (bound ()));
  show [ifI (bound (), read, []); return (nat 0)];;
 If ((i > j)) {
   Trap
 }
 If (((j + 1) <= |a|)) {
   Let b = a[j : 1]
   Return b
 }
 Return 0

 If ((i > j)) {
   Trap
 }
 If (((j + 1) <= |a|)) {
   Let b = a[j : 1]
   Return b
 }
 Return 0

 Assert (((j + 1) <= |a|))
 Let b = a[j : 1]
 Return b
 Return 0
- : unit = ()
```

The rules of a reduction are merged after `keep_slice_bounds`, and merging
keeps one copy of equal conditions. A generated bound equal to a condition
written in another rule, or to its negation, could then stand for the written
one. `unmark_written_slice_bounds`, run on the AL of all rules of the group
before they are merged, drops its marker. Here the first rule reads the slice
under the generated bound, and the second has the same bound written, with
`Return 0`. With `a = []`, the merged algorithm returns 0, and an assertion
would fail. Merged in either order, by `unify_if` (two rules) or
`merge_disjoint_ifs` (three), and with the generated copy under another
condition, all stay checks:

```ocaml
# let pipeline ~unmark blocks =
    let blocks = List.map Il2al.Transpile.keep_slice_bounds blocks in
    let blocks =
      if unmark then List.map (Il2al.Transpile.unmark_written_slice_bounds blocks) blocks
      else blocks in
    blocks
    |> Il2al.Transpile.merge_blocks
    |> Il2al.Transpile.enhance_readability
    |> Il2al.Transpile.assert_slice_bounds in
  let show ?(unmark = true) blocks =
    print_endline (Al.Print.string_of_instrs (pipeline ~unmark blocks)) in
  let r = {left = {file = "rule"; line = 2; column = 9}; right = {file = "rule"; line = 2; column = 17}} in
  let bound ?(note = Il.Origin.slice_bound r) () =
    binE (`LeOp, var "j" + nat 1, len (list "a")) ~at:r ~note in
  let read = [letI (list "b", slice (list "a") (var "j") (nat 1)); return (list "b")] in
  let generated = [ifI (bound (), read, [])] in
  let written = [ifI (bound ~note:boolT (), [return (nat 0)], [])] in
  let x k = cmp `EqOp (var "x") (nat k) in
  show ~unmark:false [generated; written];
  show [generated; written];
  show [written; generated];
  show [[ifI (x 0, generated, [])]; written];
  show ~unmark:false [generated; [ifI (x 1, written, [])]; [ifI (x 2, written, [])]];
  show [generated; [ifI (x 1, written, [])]; [ifI (x 2, written, [])]];
  show [[ifI (x 1, written, [])]; generated; [ifI (x 2, written, [])]];
  show [[ifI (x 0, generated, [])]; [ifI (x 1, written, [])]; [ifI (x 2, written, [])]];;
 Assert (((j + 1) <= |a|))
 Let b = a[j : 1]
 Return b
 Return 0

 If (((j + 1) <= |a|)) {
   Let b = a[j : 1]
   Return b
   Return 0
 }

 If (((j + 1) <= |a|)) {
   Return 0
   Let b = a[j : 1]
   Return b
 }

 If (((j + 1) <= |a|)) {
   If ((x = 0)) {
     Let b = a[j : 1]
     Return b
   }
   Return 0
 }

 Assert (((j + 1) <= |a|))
 Let b = a[j : 1]
 Return b
 If ((x = 1)) {
   Return 0
 }
 If ((x = 2)) {
   Return 0
 }

 If (((j + 1) <= |a|)) {
   Let b = a[j : 1]
   Return b
   If ((x = 1)) {
     Return 0
   }
   If ((x = 2)) {
     Return 0
   }
 }

 If (((j + 1) <= |a|)) {
   If ((x = 1)) {
     Return 0
   }
   Let b = a[j : 1]
   Return b
   If ((x = 2)) {
     Return 0
   }
 }

 If (((j + 1) <= |a|)) {
   If ((x = 0)) {
     Let b = a[j : 1]
     Return b
   }
   If ((x = 1)) {
     Return 0
   }
   If ((x = 2)) {
     Return 0
   }
 }
- : unit = ()
```
