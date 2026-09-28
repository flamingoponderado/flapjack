import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect

/-!
# `pc_compile_correct` Continue case over the exact carriers

The `Continue` conjunct of HOL `pc_compile_correct`
(`cakeml/pancake/proofs/pan_to_crepProofScript.sml:442`, case proved at
`pan_to_crepProofScript.sml:509-513` by
`fs [panSemTheory.evaluate_def, evaluate_def, compile_def, localised_prog_def]
>> rveq >> fs []`). Source `Continue` returns `(SOME Continue, s)`, `compile`
maps `Continue` to `Continue`, and the target `Continue 0` returns
`(SOME (Continue 0), t)`, so the predicate is discharged from the tagged clause
equations alone.

The theorem is untagged: it is a single case of the theorem, whose assembled
form (`pcCompileCorrectAt` for every program) is not yet proved. Tracked by
`flapjack-pxn.18.4.3.97`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (ProgHOL)

/-- The `Continue` case of HOL `pc_compile_correct` against
    `pcCompileCorrectAt`, mirroring `pcCompileCorrectAt_break`. -/
theorem pcCompileCorrectAt_continue {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) :
    pcCompileCorrectAt (.continue : ProgHOL width) source := by
  intro res s1 t ctxt hrun _ hstate hcode hexcp hlocals _
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_continue] at hrun
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrun
  refine ⟨some (.continue 0), t, ?_, hstate, hcode, hexcp, ?_⟩
  · simpa [compileProgExactHOLW] using evalCrepSemHOLProgExact_continue t 0
  · exact ⟨rfl, hlocals⟩

end Flapjack
