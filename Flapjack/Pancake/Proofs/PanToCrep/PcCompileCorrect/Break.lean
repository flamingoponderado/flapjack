import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect

/-!
# `pc_compile_correct` Break case over the exact carriers

The `Break` conjunct of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442`, case proved at
`pan_to_crepProofScript.sml:503-507` by
`fs [panSemTheory.evaluate_def, evaluate_def, compile_def, localised_prog_def]
>> rveq >> fs []`). Source `Break` returns `(SOME Break, s)`, `compile` maps
`Break` to `Break`, and the target `Break 0` returns `(SOME (Break 0), t)`, so
the predicate is discharged from the tagged clause equations alone.

The theorem is untagged: it is a single case of the theorem, whose assembled
form (`pcCompileCorrectAt` for every program) is not yet proved. Tracked by
`flapjack-rp26`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (ProgHOL)

/-- The `Break` case of HOL `pc_compile_correct` against `pcCompileCorrectAt`,
    mirroring `pcCompileCorrectAt_skip`. -/
theorem pcCompileCorrectAt_break {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.break : ProgHOL width) source := by
  intro res s1 t ctxt hrun _ hstate hcode hexcp hlocals _
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_break] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  refine ⟨some (.break 0), t, ?_, hstate, hcode, hexcp, ?_⟩
  · simpa [compileProgExactHOLW] using evalCrepSemHOLProgExact_break t 0
  · exact ⟨rfl, hlocals⟩

end Flapjack
