module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.BignumHalt
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.InstallStubs
public import Flapjack.Compiler.Backend.Semantics.DataProps.AppWithLocals

@[expose] public section

/-! The `Install` assignment (`data_to_word_assignProofScript.sml`
`assign_Install`, lines 2451-2745) and its prerequisites. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.BackendProps

namespace InstallWitness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end InstallWitness

/-- The bignum guard preserves the original conditional result. The evaluator
inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "evaluate_BignumHalt"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateBignumHalt {width : Nat} [NeZero width] {C F : Type}
    (conf : Config) (l1 l2 : Nat) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat)) (reg : Nat) (w : BitVec width)
    (related : stateRel conf l1 l2 source target none locs)
    (read : target.getVar reg = some (.word w)) :
    ∃ r, WordSemStateFiniteExact.evaluate (bignumHalt reg) target =
      (if w.getLsbD 0 then (some .notEnoughSpace, r) else (none, target)) ∧
      r.ffi = source.ffi ∧ target.ffi = source.ffi := by
  obtain ⟨r, run, rffi, tffi, -⟩ := evaluateBignumHalt2 conf l1 l2 source target locs reg w related read
  exact ⟨r, run, rffi, tffi⟩

/-- A successful primitive whose result state is still space-safe is an
admitted operation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml"
  "do_app_safe_for_space_allowed_op"]
theorem doApp_safeForSpace_allowedOp {C F : Type} (op : ClosLang.Op)
    (xs : List DataSem.Value) (s : DataSem.State C F) (r : DataSem.Value) (s1 : DataSem.State C F)
    (h : DataSem.doApp op xs s = .val (r, s1) ∧ s1.safeForSpace = true) :
    DataSem.allowedOp op xs.length := by
  obtain ⟨run, safe⟩ := h
  by_contra notAllowed
  unfold DataSem.doApp at run
  split at run
  · simp only [DataSem.doInstall] at run
    repeat (first | split at run | simp only [reduceCtorEq] at run)
    all_goals (try cases run)
    all_goals simp_all
  · cases run
  · cases run
  · split at run
    · cases run
    · rename_i space spaceRun
      dsimp only at run
      have flagFalse : (DataSem.doStack op xs (DataSem.doLimSafe space op xs)).safeForSpace = false := by
        rw [DataProps.doStack_doLimSafe_safeForSpace op xs s space spaceRun]
        simp [DataProps.doAppSafe, notAllowed]
      have := DataProps.doAppAux_safeForSpace_of_false op xs _ s1 r run flagFalse
      simp [this] at safe

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
