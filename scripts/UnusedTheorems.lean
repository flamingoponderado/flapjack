/-
Unused-theorem audit, driven by `scripts/report-unused-theorems.py` (run that
script, not this file directly).

A *candidate* is a theorem declared in a module under the module prefix named
by `UNUSED_THEOREMS_PREFIX` (default `Flapjack.Pancake`) that

* is not `@[hol]`-tagged,
* has no internal name (auxiliary declarations and `private` theorems are
  never candidates), and
* whose last name component is not listed in the file named by
  `UNUSED_THEOREMS_TEXT_ROOTS` (names mentioned outside Lean proofs: tests,
  documentation, scripts), and
* is not a representation witness that `scripts/check-hol-refs.py` requires
  by name (a last component starting with `hol` and containing `Witness`,
  such as `holListArrayWitness_<field>` or
  `holFmapAsFiniteSupportRelationWitness_<Carrier>`).

Every other constant declared in a `Flapjack.*` module is a *root*.  A
candidate is reported when it is not reachable from any root through the
constants mentioned in types and values (theorem proofs and opaque bodies
included).  Reachability is a forward fixed point, so a chain of theorems
used only by each other is reported as a whole.  The output is one
`module<TAB>name` line per reported theorem, sorted.

Unreachable means that no other declaration of the `Flapjack` library uses
the theorem; it does not mean the statement is uninteresting.  The script
reports, it does not decide.
-/
import Flapjack
open Lean Elab Command Flapjack

def unusedModuleOf (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

elab "#unused_theorems" : command => do
  let env ← getEnv
  let pfx := ((← IO.getEnv "UNUSED_THEOREMS_PREFIX").getD "Flapjack.Pancake").toName
  let rootLines : Array String ←
    match ← IO.getEnv "UNUSED_THEOREMS_TEXT_ROOTS" with
    | some path => IO.FS.lines path
    | none => pure #[]
  let textRoots : Std.HashSet String := rootLines.foldl (fun s l => s.insert l) {}
  let tagged : Std.HashSet Name := (HolRef.all env).foldl (fun s (n, _) => s.insert n) {}
  let mut cand : Std.HashSet Name := {}
  let mut roots : Array Name := #[]
  for (n, ci) in env.constants.toList do
    let some m := unusedModuleOf env n | continue
    unless (`Flapjack).isPrefixOf m do continue
    let isThm := match ci with | .thmInfo _ => true | _ => false
    let leaf := match n with | .str _ s => s | _ => ""
    if pfx.isPrefixOf m && isThm && !tagged.contains n && !n.isInternal
        && !textRoots.contains leaf
        && !(leaf.startsWith "hol" && (leaf.splitOn "Witness").length > 1) then
      cand := cand.insert n
    else
      roots := roots.push n
  let mut seen : Std.HashSet Name := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | continue
    let mut deps := ci.type.getUsedConstants
    if let some v := ci.value? (allowOpaque := true) then deps := deps ++ v.getUsedConstants
    for d in deps do
      unless seen.contains d do
        if let some m := unusedModuleOf env d then
          if (`Flapjack).isPrefixOf m then stack := stack.push d
  let mut out : Array String := #[]
  for n in cand.toList do
    unless seen.contains n do
      out := out.push s!"{(unusedModuleOf env n).getD .anonymous}\t{n}"
  for line in out.qsort (· < ·) do
    IO.println line

#unused_theorems
