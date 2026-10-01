/-
Reproducible audit: list every constant of every `Flapjack` module whose type
or value -- including theorem proof terms (`value? (allowOpaque := true)`) --
transitively through Flapjack constants mentions the untagged total HOL `EL`
rendering (`holEl`, `holHd`, `holHdNil`).

Run: `lake lean scripts/el-dependency-audit.lean`

Every reported constant must be untagged (provisional) while the HOL
`listScript` provenance review (bead flapjack-pxn.18.5.15.3.38.1) is open.
-/
import Flapjack
open Lean Elab Command

/-- Memoised reachability of the held renderings from `n` through Flapjack constants. -/
partial def elReaches (env : Environment) (bad : NameSet) (n : Name) :
    StateM (Std.HashMap Name Bool) Bool := do
  if let some b := (← get).get? n then return b
  if bad.contains n then
    modify (·.insert n true); return true
  if !(`Flapjack).isPrefixOf n then
    modify (·.insert n false); return false
  -- provisionally false to cut cycles
  modify (·.insert n false)
  let some ci := env.find? n | return false
  let cs := ci.type.getUsedConstants ++
    (match ci.value? (allowOpaque := true) with | some v => v.getUsedConstants | none => #[])
  let mut r := false
  for c in cs do
    if ← elReaches env bad c then
      r := true
      break
  modify (·.insert n r)
  return r

elab "#el_dependency_audit" : command => do
  let env ← getEnv
  let bad : NameSet := NameSet.empty |>.insert `Flapjack.holEl |>.insert `Flapjack.holHdNil
    |>.insert `Flapjack.holHd
  let names : Array Name := env.constants.fold (fun acc n _ =>
    if (`Flapjack).isPrefixOf n then acc.push n else acc) #[]
  let act : StateM (Std.HashMap Name Bool) (Array Name) :=
    names.foldlM (init := #[]) fun acc n => do
      if ← elReaches env bad n then return acc.push n else return acc
  let hits : Array Name := (act.run {}).1
  let sorted := hits.qsort (fun a b => a.toString < b.toString)
  for n in sorted do
    logInfo m!"EL-dependent: {n}"
  logInfo m!"total EL-dependent constants: {hits.size} of {names.size} Flapjack constants"

#el_dependency_audit
