module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.MkLoc
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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
