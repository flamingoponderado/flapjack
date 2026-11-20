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

/-- Reading corresponding single locals preserves the root invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_ml_inv_get_var_IMP_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordMlInv_getVar {width : Nat} [NeZero width] {C F : Type}
    (heap : ValueHeap width) (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (limit ts : Nat) (c : Config) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (ll : Spt Flapjack.Compiler.Backend.DataSem.Value) (t : WordSemStateFiniteExact width C F)
    (envs : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (n : Nat) (x : Flapjack.Compiler.Backend.DataSem.Value) (w : WordLocW width)
    (h : wordMlInv (heap, be, a, sp, sp1, gens) limit ts c refs
        (joinEnv ll (sptToAList (sptInter t.locals (adjustSet ll))) ++ envs) ∧
      DataSem.getVar n ll = some x ∧
      WordSemStateFiniteExact.getVar (adjustVar n) t = some w) :
    wordMlInv (heap, be, a, sp, sp1, gens) limit ts c refs
      ([(x, w)] ++ joinEnv ll (sptToAList (sptInter t.locals (adjustSet ll))) ++ envs) := by
  obtain ⟨inv, sourceRead, targetRead⟩ := h
  simpa using wordMlInv_lookup heap be a sp sp1 gens limit ts c refs [] envs
    ll t.locals n x w ⟨by simpa using inv, sourceRead, targetRead⟩

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
            have withHead := wordMlInv_getVar heap be a sp sp1 gens limit next conf refs
              source target envs key value word ⟨inv, read, wordRead⟩
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

/-- Related variable-list reads add their corresponding roots to the invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_ml_inv_get_vars_IMP"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordMlInv_getVars_state {width : Nat} [NeZero width] {C₁ F₁ C₂ F₂ : Type}
    (heap : ValueHeap width) (be : Bool) (a sp sp1 : Nat) (gens : GcCombined.GenState)
    (limit ts : Nat) (c : Config) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (s : Flapjack.Compiler.Backend.DataSem.State C₁ F₁) (t : WordSemStateFiniteExact width C₂ F₂)
    (envs : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (n : List Nat)
    (x : List Flapjack.Compiler.Backend.DataSem.Value) (w : List (WordLocW width))
    (h : wordMlInv (heap, be, a, sp, sp1, gens) limit ts c refs
      (joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++ envs) ∧
      DataSem.getVars n s.locals = some x ∧
      WordSemStateFiniteExact.getVars (n.map adjustVar) t = some w) :
    wordMlInv (heap, be, a, sp, sp1, gens) limit ts c refs
      (x.zip w ++ joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++ envs) :=
  wordMlInv_getVars heap be a sp sp1 gens limit ts c refs s.locals t n x w envs h

/-- Related single-variable reads add their corresponding root to the invariant. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "word_ml_inv_get_var_IMP" 8846
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem wordMlInv_getVar_state {width : Nat} [NeZero width] {C₁ F₁ C₂ F₂ : Type}
    (x1 : Flapjack.Compiler.Backend.DataSem.Value) (ts : Nat) (t : WordSemStateFiniteExact width C₂ F₂)
    (sp1 sp : Nat) (s : Flapjack.Compiler.Backend.DataSem.State C₁ F₁) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (n1 limit : Nat) (heap : ValueHeap width) (gens : GcCombined.GenState)
    (envs : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (c : Config) (be : Bool)
    (a : Nat) (x1' : WordLocW width)
    (h : wordMlInv (heap, be, a, sp, sp1, gens) limit ts c refs
      (joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++ envs) ∧
      DataSem.getVar n1 s.locals = some x1 ∧
      WordSemStateFiniteExact.getVar (adjustVar n1) t = some x1') :
    wordMlInv (heap, be, a, sp, sp1, gens) limit ts c refs
      ((x1, x1') :: (joinEnv s.locals (sptToAList (sptInter t.locals (adjustSet s.locals))) ++ envs)) := by
  obtain ⟨inv, dataRead, wordRead⟩ := h
  have dataReads : DataSem.getVars [n1] s.locals = some [x1] := by simp [DataSem.getVars, dataRead]
  have wordReads : WordSemStateFiniteExact.getVars ([n1].map adjustVar) t = some [x1'] := by
    simp [WordSemStateFiniteExact.getVars, wordRead]
  simpa using wordMlInv_getVars_state heap be a sp sp1 gens limit ts c refs s t envs [n1] [x1] [x1']
    ⟨inv, dataReads, wordReads⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
