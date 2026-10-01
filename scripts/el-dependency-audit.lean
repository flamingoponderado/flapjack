/-
Reproducible audit: list every constant defined in a `Flapjack.*` module -- in
any namespace, including `_private.*` helpers and auxiliary declarations --
whose type or value (theorem proof terms and opaque bodies included, via
`value? (allowOpaque := true)`) transitively mentions the untagged total HOL
`EL` rendering (`holEl`, `holHd`, `holHdNil`).

Reachability is a reverse-graph fixed point: the dependency edges of every
Flapjack-module constant are inverted and searched breadth-first from the held
renderings, so cycles and non-`Flapjack`-prefixed names cannot cut a path.
Constants of non-Flapjack modules (Lean core, Std, Mathlib) cannot mention the
held renderings and are not traversed. Each hit is intersected with the
`@[hol]` tags (`HolRef.all`); a tagged hit is reported with a witness path and
is an error.

Run: `lake lean scripts/el-dependency-audit.lean`

Every reported constant must be untagged (provisional) while the HOL
`listScript` provenance review (bead flapjack-pxn.18.5.15.3.38.1) is open.
-/
import Flapjack
open Lean Elab Command Flapjack

/-- Whether `n` was declared in a `Flapjack.*` module (or in this file). -/
def inFlapjackModule (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => (`Flapjack).isPrefixOf (env.header.moduleNames[idx.toNat]!)
  | none => true

elab "#el_dependency_audit" : command => do
  let env ← getEnv
  let held : Array Name := #[`Flapjack.holEl, `Flapjack.holHdNil, `Flapjack.holHd]
  for h in held do
    unless env.contains h do throwError "held rendering {h} not found"
  -- reverse edges: dependency ↦ dependents
  let mut rev : Std.HashMap Name (Array Name) := {}
  let mut nodes : Nat := 0
  for (n, ci) in env.constants.toList do
    unless inFlapjackModule env n do continue
    nodes := nodes + 1
    let deps := ci.type.getUsedConstants ++
      (match ci.value? (allowOpaque := true) with
       | some v => v.getUsedConstants
       | none => #[])
    for d in deps do
      rev := rev.insert d ((rev.getD d #[]).push n)
  -- breadth-first fixed point from the held renderings, with parent pointers
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : NameSet := held.foldl (·.insert ·) {}
  let mut queue : Array Name := held
  let mut i : Nat := 0
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    for m in rev.getD n #[] do
      unless seen.contains m do
        seen := seen.insert m
        parent := parent.insert m n
        queue := queue.push m
  let tagged : NameSet := (HolRef.all env).foldl (fun s (n, _) => s.insert n) {}
  let hits := (queue.filter (fun n => !held.contains n)).qsort
    (fun a b => a.toString < b.toString)
  let mut bad : Nat := 0
  for n in hits do
    if tagged.contains n then
      bad := bad + 1
      let mut path : Array Name := #[n]
      let mut cur := n
      while parent.contains cur do
        cur := parent.get! cur
        path := path.push cur
      logError m!"TAGGED EL-dependent: {n} via {path.toList}"
    else
      logInfo m!"EL-dependent (untagged): {n}"
  logInfo m!"total EL-dependent constants: {hits.size} of {nodes} Flapjack-module constants; {tagged.size} tagged declarations checked; {bad} tagged hits"

#el_dependency_audit
