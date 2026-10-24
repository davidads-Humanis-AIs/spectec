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
