module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MkLoc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.Clock
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! Exception destinations through word-state call and clock operations. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack
open WordSemStateFiniteExact

namespace jumpExcMap
/-- Canonical target-state roundtrip for the exception lemmas. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end jumpExcMap

/-- Calling an environment only changes the stack maximum visible to exception unwinding. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "jump_exc_call_env"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem jumpExc_callEnv {width : Nat} [NeZero width] {C F : Type}
    (args : List (WordLocW width)) (size : Option Nat) (state : WordSemStateFiniteExact width C F) :
    jumpExc (WordSemStateFiniteExact.callEnv args size state) =
      jumpExc { state with stackMax := (wordSemOptionMax state.stackMax
        (wordSemOptionAdd (wordSemStackSize state.stack) size)) } := by
  unfold jumpExc WordSemStateFiniteExact.callEnv
  split <;> simp_all

/-- Decrementing the clock preserves the destination of exception unwinding. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "jump_exc_dec_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem jumpExc_decClock {width : Nat} {outWidth : Nat} [NeZero width] [NeZero outWidth] {C F : Type}
    (state : WordSemStateFiniteExact width C F) :
    mkLoc (width := outWidth) (jumpExc (decClock state)) = mkLoc (width := outWidth) (jumpExc state) := by
  unfold jumpExc decClock
  split <;> simp_all
  split <;> simp_all [mkLoc]

/-- Taking a suffix no longer than the tail ignores the prepended frame.
This factors the `LASTN_TL` step used in the HOL exception proof. -/
private theorem lastN_cons_of_le {α : Type} (n : Nat) (x : α) (xs : List α)
    (h : n ≤ xs.length) : wordSemLastN n (x :: xs) = wordSemLastN n xs := by
  unfold wordSemLastN
  rw [List.reverse_cons, List.take_append_of_le_length (by simpa using h)]

/-- Pushing a frame without a handler preserves the exception destination,
even if the stack maximum is subsequently replaced. This factors two
conjuncts of the HOL theorem. -/
private theorem mkLoc_pushEnv_noHandler {width : Nat} {outWidth : Nat}
    [NeZero width] [NeZero outWidth] {C F : Type}
    (state : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (max : Option Nat) :
    mkLoc (width := outWidth) (jumpExc { pushEnv envs none state with stackMax := max }) =
      mkLoc (width := outWidth) (jumpExc state) := by
  unfold pushEnv
  generalize henv : wordSemEnvToList envs.2 state.permute = result
  obtain ⟨values, permute⟩ := result
  by_cases hlt : state.handler < state.stack.length
  · have hle : state.handler + 1 ≤ state.stack.length := by omega
    simp only [jumpExc, hlt, if_true, List.length_cons, Nat.lt_succ_of_lt hlt,
      lastN_cons_of_le _ _ _ hle]
    split <;> simp_all [mkLoc]
  · by_cases heq : state.handler = state.stack.length
    · simp [jumpExc, henv, heq, wordSemLastN, List.take_of_length_le, mkLoc]
    · have hnot : ¬ state.handler < state.stack.length + 1 := by omega
      simp [jumpExc, henv, hlt, hnot]

/-- Pushing a frame without a handler preserves each independently typed
exception destination, including after a stack-maximum update. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "jump_exc_push_env_NONE"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem jumpExc_pushEnv_none {width : Nat} {out1 : Nat} {out2 : Nat} {out3 : Nat}
    [NeZero width] [NeZero out1] [NeZero out2] [NeZero out3] {C F : Type}
    (state : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) (max : Option Nat) :
    mkLoc (width := out1) (jumpExc (decClock state)) = mkLoc (width := out1) (jumpExc state) ∧
    mkLoc (width := out2) (jumpExc (pushEnv envs none state)) = mkLoc (width := out2) (jumpExc state) ∧
    mkLoc (width := out3) (jumpExc { pushEnv envs none state with stackMax := max }) =
      mkLoc (width := out3) (jumpExc state) := by
  refine ⟨jumpExc_decClock state, ?_, mkLoc_pushEnv_noHandler state envs max⟩
  simpa using mkLoc_pushEnv_noHandler (outWidth := out2) state envs (pushEnv envs none state).stackMax

/-- Incrementing the clock preserves the selected unwind location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "mk_loc_jmup_exc_inc_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem mkLoc_jumpExc_incClock {width : Nat} {outWidth : Nat} [NeZero width] [NeZero outWidth] {C F : Type}
    (ck : Nat) (t : WordSemStateFiniteExact width C F) :
    mkLoc (width := outWidth) (jumpExc (gcIncClock ck t)) = mkLoc (width := outWidth) (jumpExc t) := by
  unfold jumpExc gcIncClock incClock
  split <;> simp_all
  split <;> simp_all [mkLoc]

/-- Incrementing the clock preserves whether exception unwinding fails. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "jump_exc_inc_clock_EQ_NONE"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem jumpExc_incClock_eqNone {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (s : WordSemStateFiniteExact width C F) :
    jumpExc (gcIncClock n s) = none ↔ jumpExc s = none := by
  unfold jumpExc gcIncClock incClock
  split <;> simp_all
  split <;> simp_all

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
