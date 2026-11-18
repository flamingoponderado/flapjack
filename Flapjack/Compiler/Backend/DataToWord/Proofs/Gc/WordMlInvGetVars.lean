module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordMlInvLookup

@[expose] public section

/-! Root preservation for a list of corresponding local-variable reads. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace WordMlInvGetVarsPort

theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordMlInvGetVarsPort

/-- Reading corresponding source and word locals preserves the root invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_ml_inv_get_vars_IMP_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordMlInv_getVars {width : Nat} [NeZero width] {C F : Type}
    (heap : ValueHeap width) (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (limit next : Nat) (conf : Config) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (source : Spt Flapjack.Compiler.Backend.DataSem.Value) (target : WordSemStateFiniteExact width C F)
    (names : List Nat) (values : List Flapjack.Compiler.Backend.DataSem.Value) (words : List (WordLocW width))
    (envs : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (premises : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
        (joinEnv source (sptToAList (sptInter target.locals (adjustSet source))) ++ envs) ∧
      DataSem.getVars names source = some values ∧
      WordSemStateFiniteExact.getVars (names.map adjustVar) target = some words) :
    wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
      (values.zip words ++ joinEnv source (sptToAList (sptInter target.locals (adjustSet source))) ++ envs) := by
  induction names generalizing values words envs with
  | nil =>
    obtain ⟨inv, hv, hw⟩ := premises
    simp [DataSem.getVars, WordSemStateFiniteExact.getVars] at hv hw
    subst values
    subst words
    simpa using inv
  | cons key rest ih =>
    obtain ⟨inv, hv, hw⟩ := premises
    cases read : DataSem.getVar key source with
    | none => simp [DataSem.getVars, read] at hv
    | some value =>
      cases reads : DataSem.getVars rest source with
      | none => simp [DataSem.getVars, read, reads] at hv
      | some vs =>
        cases wordRead : WordSemStateFiniteExact.getVar (adjustVar key) target with
        | none => simp [WordSemStateFiniteExact.getVars, wordRead] at hw
        | some word =>
          cases wordReads : WordSemStateFiniteExact.getVars (rest.map adjustVar) target with
          | none => simp [WordSemStateFiniteExact.getVars, wordRead, wordReads] at hw
          | some ws =>
            simp [DataSem.getVars, read, reads] at hv
            simp [WordSemStateFiniteExact.getVars, wordRead, wordReads] at hw
            subst values
            subst words
            have withHead := wordMlInv_lookup heap be a sp sp1 gens limit next conf refs [] envs
              source target.locals key value word ⟨by simpa using inv, read, wordRead⟩
            have reordered : wordMlInv (heap, be, a, sp, sp1, gens) limit next conf refs
                (joinEnv source (sptToAList (sptInter target.locals (adjustSet source))) ++ (value, word) :: envs) := by
              apply wordMlInv_rearrange heap be a sp sp1 gens limit next conf refs _ _ ?_ withHead
              intro pair member
              simp only [List.mem_append, List.mem_cons] at member ⊢
              tauto
            have tail := ih vs ws ((value, word) :: envs) ⟨reordered, reads, wordReads⟩
            apply wordMlInv_rearrange heap be a sp sp1 gens limit next conf refs _ _ ?_ tail
            intro pair member
            simp only [List.zip_cons_cons, List.mem_cons, List.mem_append] at member ⊢
            tauto

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
