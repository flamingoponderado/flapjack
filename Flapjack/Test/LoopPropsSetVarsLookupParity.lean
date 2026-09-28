import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

/-!
# Exact `loopProps$lookup_set_vars` / `lookup_set_vars_not_MEM` parity

The expected observations are direct HOL-EVAL results from
`scripts/hol-probes/loop_props_set_vars_lookup_probe.out`, generated from
`cakeml/pancake/semantics/loopPropsScript.sml:297-313` (with
`loopSemScript.sml:113-116`).  The exact width-indexed ports
`LoopSemStateFiniteExact.lookup_set_vars` and `lookup_set_vars_not_MEM` live in
`Flapjack/Pancake/Semantics/LoopProps/NestedSeqSyntaxExact.lean`.
-/

namespace Flapjack.Test.LoopPropsSetVarsLookupParity

open Flapjack

private def setVarsFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed
    ffiState := ()
    ioEvents := [] }

/-- Base locals: key 5 -> `Word 2`, key 9 -> `Word 1` (matching the probe). -/
private def setVarsBase : LoopSemStateFiniteExact 8 Unit :=
  { locals := sptInsert 5 (.word 2) (sptInsert 9 (.word 1) Spt.ln)
    globals := HolFiniteMapExact.empty
    code := Spt.ln
    memory := fun _ => .word 0
    mdomain := fun _ => true
    shMdomain := fun _ => true
    clock := 0
    be := false
    ffi := setVarsFfi
    baseAddr := 0
    topAddr := 0 }

private def set34 : LoopSemStateFiniteExact 8 Unit :=
  LoopSemStateFiniteExact.setVars [3, 4] [.word 7, .word 8] setVarsBase

private def setDup : LoopSemStateFiniteExact 8 Unit :=
  LoopSemStateFiniteExact.setVars [3, 3] [.word 7, .word 8] setVarsBase

private def setShort : LoopSemStateFiniteExact 8 Unit :=
  LoopSemStateFiniteExact.setVars [3, 4] [.word 7] setVarsBase

#guard decide (sptLookup 3 set34.locals = some (.word 7))
#guard decide (sptLookup 4 set34.locals = some (.word 8))
#guard decide (sptLookup 9 set34.locals = some (.word 1))
#guard decide (sptLookup 5 set34.locals = some (.word 2))
#guard decide (sptLookup 6 set34.locals = none)
#guard decide (sptLookup 3 setDup.locals = some (.word 7))
#guard decide (sptLookup 4 setShort.locals = none)

/-- Exact `lookup_set_vars` applied at the HOL-EVAL hit row. -/
example : sptLookup 3 set34.locals =
    match holAlookup ([3, 4].zip [.word 7, .word 8]) 3 with
    | none => sptLookup 3 setVarsBase.locals
    | some v => some v :=
  LoopSemStateFiniteExact.lookup_set_vars 3 [3, 4] [.word 7, .word 8] setVarsBase

/-- Exact `lookup_set_vars_not_MEM` at the HOL-EVAL miss row (`6 ∉ [3,4]`). -/
example : sptLookup 6 set34.locals = sptLookup 6 setVarsBase.locals :=
  LoopSemStateFiniteExact.lookup_set_vars_not_MEM 6 [3, 4] [.word 7, .word 8]
    setVarsBase (by decide)

def runChecks : IO Bool := do
  let checks :=
    [ ("loopProps lookup_set_vars hit",
        decide (sptLookup 3 set34.locals = some (.word 7))),
      ("loopProps lookup_set_vars hit2",
        decide (sptLookup 4 set34.locals = some (.word 8))),
      ("loopProps lookup_set_vars base key",
        decide (sptLookup 9 set34.locals = some (.word 1))),
      ("loopProps lookup_set_vars other key",
        decide (sptLookup 5 set34.locals = some (.word 2))),
      ("loopProps lookup_set_vars miss",
        decide (sptLookup 6 set34.locals = none)),
      ("loopProps lookup_set_vars duplicate first wins",
        decide (sptLookup 3 setDup.locals = some (.word 7))),
      ("loopProps lookup_set_vars_not_MEM short zip",
        decide (sptLookup 4 setShort.locals = none)) ]
  let results ← checks.mapM fun (name, ok) => do
    if ok then
      IO.println s!"PASS {name}"
      pure true
    else
      IO.println s!"FAIL {name}"
      pure false
  pure (results.all id)

end Flapjack.Test.LoopPropsSetVarsLookupParity