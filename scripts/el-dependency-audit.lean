/-
Reproducible audit: list every constant of the linear-scan port modules whose
type or value (transitively through Flapjack constants) mentions the untagged
total HOL `EL` rendering (`holEl`, `holHd`, `holHdNil`).

Run: `lake lean scripts/el-dependency-audit.lean`

Every reported constant must be untagged (provisional) while the HOL
`listScript` provenance review (bead flapjack-pxn.18.5.15.3.38.1) is open.
-/
import Flapjack.Compiler.Backend.LinearScan.Proofs
import Flapjack.Compiler.Backend.LinearScan.TopLevel
import Flapjack.Translator.Monadic.MonadBase.Arrays
open Lean Meta Elab Command

partial def closure (env : Environment) (todo : List Name) (seen : NameSet) : NameSet := Id.run do
  let mut todo := todo
  let mut seen := seen
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if !(n.toString.startsWith "Flapjack") then continue
    match env.find? n with
    | some ci =>
      let cs := ci.type.getUsedConstants ++ (match ci.value? with | some v => v.getUsedConstants | none => #[])
      for c in cs do
        if !seen.contains c then todo := c :: todo
    | none => pure ()
  return seen

elab "#elaudit" : command => do
  let env ← getEnv
  let mods := ["Flapjack.Compiler.Backend.LinearScan", "Flapjack.Translator.Monadic.MonadBase.Arrays", "Flapjack.Compiler.Backend.RegAlloc.Proofs.SpInverts", "Flapjack.Misc.Sptree.Foldi", "Flapjack.Misc.Sptree.ToAList", "Flapjack.Compiler.Backend.RegAlloc.Proofs", "Flapjack.Misc.Option", "Flapjack.Misc.MiscThe"]
  let bad := [`Flapjack.holEl, `Flapjack.holHdNil, `Flapjack.holHd]
  let names : Array Name := env.constants.fold (fun acc n _ => acc.push n) #[]
  let mut out : Array Name := #[]
  for n in names do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    if !(mods.any fun m => modName.toString.startsWith m) then continue
    -- tagged?  use docstring absence heuristic: check hol attribute via `Flapjack.holRefAttr`? fall back on all theorems/defs
    let cl := closure env [n] {}
    if bad.any (fun b => cl.contains b) then
      out := out.push n
  for n in out do
    logInfo m!"EL-dependent: {n}"
  logInfo m!"total EL-dependent constants: {out.size}"
#elaudit
