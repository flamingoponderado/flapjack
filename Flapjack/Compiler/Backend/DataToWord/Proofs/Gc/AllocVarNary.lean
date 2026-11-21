module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.AllocVar
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GetVarsPerm
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CutLocals
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.SizeValues
@[expose] public section

/-! Variable allocation with an explicit source argument list. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace AllocVarNaryWitnesses
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end AllocVarNaryWitnesses

/-- Variable allocation preserves the full state relation and heap-size bound.
The evaluator inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "AllocVar_thm_nary"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem allocVar_nary {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (args : List Nat) (names : NumSet) (cut : Spt Flapjack.Compiler.Backend.DataSem.Value) (vals : List Flapjack.Compiler.Backend.DataSem.Value)
    (i limit : Nat) (q : Option (WordSemResult width)) (result : WordSemStateFiniteExact width C F)
    (related : stateRel conf l1 l2 source target none locs)
    (cutEq : DataSem.cutEnv (sptListInsert args names) source.locals = some cut)
    (readArgs : DataSem.getVars args source.locals = some vals)
    (read : target.getVar 1 = some (.word (BitVec.ofNat width (4 * i))))
    (wordBound : 4 * i < 2 ^ width)
    (run : WordSemStateFiniteExact.evaluate (allocVar conf limit (sptListInsert args names)) target = (q, result))
    (limitBound : limit < 2 ^ width / 8) :
    (q = some .notEnoughSpace → result.ffi = source.ffi ∧ optionLe result.stackMax source.stackMax ∧
      (conf.gcKind ≠ .none ∧ i < limit ∧ DataSem.noThunksInRefs source.refs →
        source.limits.heapLimit < DataSem.sizeOfHeapArgs vals (cutLocals names source) + (i + 1))) ∧
    (q ≠ some .notEnoughSpace → i < limit ∧
      stateRel conf l1 l2 {source with locals := cut, space := i + 1} result none locs ∧
      result.store.lookup (.temp 29) = target.store.lookup (.temp 29) ∧
      result.code = target.code ∧ result.codeBuffer = target.codeBuffer ∧
      result.dataBuffer = target.dataBuffer ∧ result.compileOracle = target.compileOracle ∧ q = none) := by
  have wordValue : (BitVec.ofNat width (4 * i)).toNat / 4 = i := by
    simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound]
  have general := allocVar_gen conf l1 l2 source target result locs (sptListInsert args names)
    cut (BitVec.ofNat width (4 * i)) limit q related cutEq read run limitBound
  simp only [wordValue] at general
  constructor
  · intro fail
    have failed := general.1 fail
    refine ⟨failed.1, failed.2.1, ?_⟩
    intro conditions
    have allLive : ∀ k, sptMem k (sptListInsert args names) → sptMem k source.locals := by
      unfold DataSem.cutEnv at cutEq
      split at cutEq
      · assumption
      · contradiction
    have baseLive : ∀ k, sptMem k names → sptMem k source.locals := by
      intro k mem
      apply allLive k
      change sptDomain (sptListInsert args names) k
      rw [Flapjack.Compiler.Backend.BviToData.domain_listInsert]
      exact Or.inr mem
    have cutBase : DataSem.cutEnv names source.locals = some (sptInter source.locals names) := by
      have normalized : sptMkWf (sptInter source.locals names) = sptInter source.locals names := by
        apply (sptEqThm _ _ ⟨sptWf_mkWf _, sptWfInter _ _⟩).2
        intro key
        exact sptLookup_mkWf _ _
      unfold DataSem.cutEnv
      rw [if_pos baseLive, normalized]
    have cutAll : cut = sptInter source.locals (sptListInsert args names) := by
      have normalized : sptMkWf (sptInter source.locals (sptListInsert args names)) =
          sptInter source.locals (sptListInsert args names) := by
        apply (sptEqThm _ _ ⟨sptWf_mkWf _, sptWfInter _ _⟩).2
        intro key
        exact sptLookup_mkWf _ _
      unfold DataSem.cutEnv at cutEq
      rw [if_pos allLive, normalized] at cutEq
      exact Option.some.inj cutEq.symm
    obtain ⟨dups, perm, dupsIn, valsIn⟩ := getVarsPermToListInter source.locals args names vals readArgs
    have heap := failed.2.2 conditions
    let roots := vals ++ sptToList (sptInter source.locals names) ++
      source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]
    have rootsPerm : roots.Perm (dups ++ sptToList cut ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global]) := by
      simpa [roots, cutAll, List.append_assoc] using perm.append_right (source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global])
    have dupsSubset : ∀ v ∈ dups, v ∈ sptToList cut ++ source.stack.flatMap DataSem.extractStack ++ [theGlobal source.global] := by
      intro v mem
      have hv := valsIn v (dupsIn v mem)
      simp [cutAll, hv]
    cases sizeEq : DataSem.sizeOfValues source.limits roots source.refs .ln with
    | mk n rest =>
      cases rest with
      | mk refs visited =>
        have bound := heap roots dups n refs visited ⟨rootsPerm, dupsSubset, sizeEq⟩
        have sizeArgs : DataSem.sizeOfHeapArgs vals (cutLocals names source) = n := by
          simp only [DataSem.sizeOfHeapArgs, cutLocals, cutBase, DataSem.stackToValues]
          simp only [← List.append_assoc]
          rw [sizeOfValues_global]
          simpa [roots, List.append_assoc] using congrArg Prod.fst sizeEq
        simpa [sizeArgs] using bound
  · exact general.2
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
