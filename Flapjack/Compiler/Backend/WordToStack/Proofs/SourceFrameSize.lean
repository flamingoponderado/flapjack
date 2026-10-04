import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackLists

namespace Flapjack.WordToStackProofs
open Flapjack Flapjack.WordSemStackEq Flapjack.WordSemStateFiniteExact

namespace SourceFrameSizeWitnesses
/-- Canonical imported native WordSem state roundtrip for the existing
finite-support translation; no duplicate state carrier is declared. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end SourceFrameSizeWitnesses
open SourceFrameSizeWitnesses

/-- Full original allocation-store update commutes with pushing a plain frame,
for arbitrary native environments, state and allocation word. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem pushEnvSetStore {width : Nat} [NeZero width] {C F : Type}
    (env : Spt (WordLocW width) × Spt (WordLocW width)) (c : BitVec width)
    (s : WordSemStateFiniteExact width C F) :
    pushEnv env none (setStore .allocSize (.word c) s) =
      setStore .allocSize (.word c) (pushEnv env none s) := by
  simp [pushEnv, setStore]

/-- Full original key relation preserves source-stack size. This Word-to-Stack
source theorem has the same complete statement as the reviewed WordProps law,
whose native kernel proof is reused without an extra premise. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "s_key_eq_stack_size"
  (words_as_type_indexed_bitvec)]
theorem sourceKeyEqStackSize {width : Nat} [NeZero width]
    (stack stack' : List (WordSemStackFrame width)) (h : sKeyEq stack stack') :
    wordSemStackSize stack = wordSemStackSize stack' := sKeyEqStackSize stack stack' h

/-- Full original successful source decoder preserves optional stack size,
including absent frame-size predictions and every handler case. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "dec_stack_stack_size"
  (words_as_type_indexed_bitvec)]
theorem decStackStackSize {width : Nat} [NeZero width]
    (xs : List (WordLocW width)) (st st' : List (WordSemStackFrame width))
    (h : wordSemDecStack xs st = some st') :
    wordSemStackSize st = wordSemStackSize st' :=
  sourceKeyEqStackSize st st' (decStackStackKeyEq xs st st' h)

/-- Full original key-related pushed-frame result. The source size prediction
and tail-stack size are derived from the actual push and sole key relation;
no successful size calculation or desired post-state fact is assumed. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem sourceKeyEqPushEnvLocalsSize {width : Nat} [NeZero width] {C F : Type}
    (env : Spt (WordLocW width) × Spt (WordLocW width))
    (opt1 : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (n : Option Nat)
    (l0 l : List (Nat × WordLocW width)) (opt2 : Option (Nat × Nat × Nat))
    (stack' : List (WordSemStackFrame width))
    (h : sKeyEq (pushEnv env opt1 s).stack (.stackFrame n l0 l opt2 :: stack')) :
    n = s.localsSize ∧ wordSemStackSize s.stack = wordSemStackSize stack' := by
  cases opt1 with
  | none =>
    simp only [pushEnv, sKeyEq] at h
    have hf := (sFrameKeyEqDef2 _ _ _ _ _ _ _ _).mp h.2
    exact ⟨hf.2.2.2.symm, sourceKeyEqStackSize s.stack stack' h.1⟩
  | some info =>
    rcases info with ⟨w, prog, l1, l2⟩
    simp only [pushEnv, sKeyEq] at h
    have hf := (sFrameKeyEqDef2 _ _ _ _ _ _ _ _).mp h.2
    exact ⟨hf.2.2.2.symm, sourceKeyEqStackSize s.stack stack' h.1⟩

end Flapjack.WordToStackProofs
