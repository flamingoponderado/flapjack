module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Move
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.FromListSnoc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber

@[expose] public section

/-! Preservation of the GC state relation when passing a numeric argument. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace NumberArgWitnesses

/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end NumberArgWitnesses

/-- Appending a small numeric argument preserves the full call-environment relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_IMP_Number_arg"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_imp_numberArg {width : Nat} [NeZero width] {C F : Type} (c : Config) (l1 l2 : Nat)
    (xs : List Flapjack.Compiler.Backend.DataSem.Value) (ss : Option Nat) (s : Flapjack.Compiler.Backend.DataSem.State C F)
    (ys : List (WordLocW width)) (t : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (n : Nat)
    (premises : stateRel c l1 l2 (DataSem.callEnv xs ss s)
        (WordSemStateFiniteExact.callEnv ys ss t) none locs ∧
      n < 2 ^ width / 16 ∧ ys.length = xs.length + 1) :
    stateRel c l1 l2 (DataSem.callEnv (xs ++ [.number (Int.ofNat n)]) ss s)
      (WordSemStateFiniteExact.callEnv (ys ++ [.word (BitVec.ofNat width (4 * n))]) ss t) none locs := by
  obtain ⟨related, bound, lengths⟩ := premises
  let source := DataSem.callEnv xs ss s
  let target := WordSemStateFiniteExact.callEnv ys ss t
  have sourceEq : DataSem.callEnv (xs ++ [.number (Int.ofNat n)]) ss s =
      DataSem.setVar xs.length (.number (Int.ofNat n)) source := by
    simp [source, DataSem.callEnv, DataSem.setVar, fromList_snoc]
  have targetEq : WordSemStateFiniteExact.callEnv (ys ++ [.word (BitVec.ofNat width (4 * n))]) ss t =
      WordSemStateFiniteExact.setVar (adjustVar xs.length) (.word (BitVec.ofNat width (4 * n))) target := by
    simp [target, WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.setVar,
      fromList2_snoc, lengths, adjustVar, Nat.mul_add]
  rw [sourceEq, targetEq]
  apply stateRel_insertRoot c l1 l2 source target locs xs.length (.number (Int.ofNat n))
    (.word (BitVec.ofNat width (4 * n))) related
  change stateRel c l1 l2 source target none locs at related
  rcases related with ⟨hffi, hclock, hhandler, hgc, hcode, horacle, hgood, hshift,
    htstamp, hglobal, hzero, hpresent, hstack, hlocs, hacc, hmax, hsizes, hlocals, hlim, hmem⟩
  have small : smallInt width (Int.ofNat n) := by
    unfold smallInt
    have less : n < 2 ^ width / 8 := by omega
    simp only [Int.ofNat_eq_natCast]
    constructor
    · exact le_trans (neg_nonpos.mpr (Int.natCast_nonneg _)) (Int.natCast_nonneg _)
    · exact_mod_cast less
  have encoded : smallnum (width := width) (Int.ofNat n) = BitVec.ofNat width (4 * n) := by
    have nonneg : ¬ (Int.ofNat n < 0) := by
      rw [Int.ofNat_eq_natCast]
      exact Int.not_lt_of_ge (Int.natCast_nonneg n)
    simp only [smallnum, nonneg, ↓reduceIte]
    congr 1
  have extended := impMemoryRel_number c target.be (holThe source.tstamps) source.refs source.space
    target.store target.memory target.mdomain
    (joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals))) ++
      [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack)
    (Int.ofNat n) ⟨hgood, small, by simpa using hmem⟩
  rw [encoded] at extended
  simpa using extended
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
