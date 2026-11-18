module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.CodePointer
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CallEnv
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvGetVars
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Code-pointer roots in the data-to-word garbage-collection invariant. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace codePointerMap
/-- Canonical target-state roundtrip for the code-pointer relation. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end codePointerMap

/-- A code-pointer root is represented by the matching word location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_ml_inv_CodePtr"
  (words_as_type_indexed_bitvec)]
theorem wordMlInv_codePtr {width : Nat} [NeZero width] {C F : Type}
    (heap : ValueHeap width) (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (limit next : Nat) (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (label : Nat) (word : WordLocW width)
    (rest : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (inv : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf source.refs
      ((.codePtr label, word) :: rest)) : word = .loc label 0 := by
  obtain ⟨roots, habs, addresses⟩ := inv
  obtain ⟨_, _, _, _, stack⟩ := habs
  obtain ⟨f, tf, _, _, _, _, _, _, _, values, _⟩ := stack
  cases roots with
  | nil => cases values
  | cons root roots =>
    cases values with
    | cons valueInv _ =>
      cases addresses with
      | cons address _ =>
        have equal := (valueInv_codePtr conf label source.refs root f tf heap).mp valueInv
        subst root
        simpa [wordAddr] using address.symm

/-- Equal nonempty lists include their last pair in the zipped roots. This
helper supports the source proof's final-argument reasoning. -/
private theorem lastZipMem {α β : Type} [Nonempty α] [Nonempty β]
    (xs : List α) (ys : List β) (length : xs.length = ys.length) (nonempty : xs ≠ []) :
    (holLast xs, holLast ys) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => exact (nonempty rfl).elim
  | cons x xs ih =>
    cases ys with
    | nil => simp at length
    | cons y ys =>
      cases xs with
      | nil =>
        cases ys with
        | nil => simp [holLast]
        | cons y2 ys => simp at length
      | cons x2 xs =>
        cases ys with
        | nil => simp at length
        | cons y2 ys =>
          have eqLen : (x2 :: xs).length = (y2 :: ys).length := by simpa using length
          have mem := ih (y2 :: ys) eqLen (by simp)
          simpa [holLast] using List.mem_cons_of_mem (x, y) mem

/-- The final source code-pointer argument is the matching word location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "state_rel_CodePtr"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem stateRel_codePtr {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat) (source : Flapjack.Compiler.Backend.DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat))
    (args : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width)) (label : Nat)
    (premises : stateRel conf l1 l2 source target none locs ∧
      DataSem.getVars args source.locals = some values ∧
      WordSemStateFiniteExact.getVars (args.map adjustVar) target = some words ∧
      holLast values = .codePtr label ∧ values ≠ []) :
    words ≠ [] ∧ holLast words = .loc label 0 := by
  obtain ⟨related, sourceRead, targetRead, lastEq, nonempty⟩ := premises
  have hs := getVars_imp_length args values source.locals sourceRead
  have ht := wordGetVars_imp_length (args.map adjustVar) words target targetRead
  simp only [List.length_map] at ht
  have eqLen : values.length = words.length := hs.symm.trans ht
  have wordNonempty : words ≠ [] := by
    intro empty
    simp [empty] at eqLen
    exact nonempty (by simpa using eqLen)
  refine ⟨wordNonempty, ?_⟩
  have member := lastZipMem values words eqLen nonempty
  rw [lastEq] at member
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmem⟩
  obtain ⟨heap, limit, a, sp, sp1, gens, _, hinv, _, _⟩ := hmem
  let rest := [(theGlobal source.global, holFapply target.store .globals)] ++ flatStack source.stack target.stack
  have added := wordMlInv_getVars heap target.be a sp sp1 gens limit (holThe source.tstamps)
    conf source.refs source.locals target args values words rest
    ⟨by simpa [rest] using hinv, sourceRead, targetRead⟩
  apply wordMlInv_codePtr heap target.be a sp sp1 gens limit (holThe source.tstamps)
    conf source label (holLast words) []
  apply wordMlInv_rearrange heap target.be a sp sp1 gens limit (holThe source.tstamps)
    conf source.refs _ _ ?_ added
  intro pair inNew
  simp only [List.mem_singleton] at inNew
  subst pair
  simp only [List.mem_append]
  exact Or.inl (Or.inl member)


end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
