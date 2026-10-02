import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsInsert
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAExpressions

namespace Flapjack.Compiler.Backend.WordAlloc

namespace SemanticRegisterWriteWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SemanticRegisterWriteWitnesses

/-- Original full SSA Get case with all six original premises and complete
existential source-permutation/result/frame/locals conclusion. Source error and
success branches are derived; no target execution or success premise is added.
The full evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectGet {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name : Nat) (store : WordStoreHOL)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.get name store : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.get name store : WordLangProgHOL (BitVec width)) source target ssa next tables := by
  have bound : name < next := by
    simpa [everyVarHOL] using h.2.2.2.1
  have sameStore : target.store = source.store := h.1.2.1
  refine ⟨target.permute, ?_⟩
  cases found : source.store.lookup store with
  | none => simp [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getStore, found]
  | some value =>
    have locals := ssaLocalsRelSetVar next ssa source.locals target.locals name value
      ⟨h.2.1, h.2.2.2.2.1, bound⟩
    simp_all [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.getStore,
      ssaCcTrans, nextVarRename, WordSemStateFiniteExact.setVar,
      Flapjack.WordAlloc.wordStateEqRel]

/-- Original full SSA LocValue case with all six original premises and complete
existential source-permutation/result/frame/locals conclusion. Source error and
success branches are derived; no target execution or success premise is added.
The full evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectLocValue {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name : Nat) (label : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.locValue name label : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.locValue name label : WordLangProgHOL (BitVec width)) source target ssa next tables := by
  have bound : name < next := by
    simpa [everyVarHOL] using h.2.2.2.1
  have sameCode : target.code = source.code := by
    rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, code, _, _, _, _, _, _, _⟩
    exact code
  refine ⟨target.permute, ?_⟩
  by_cases present : sptMem label source.code
  · have locals := ssaLocalsRelSetVar next ssa source.locals target.locals name (.loc label 0)
      ⟨h.2.1, h.2.2.2.2.1, bound⟩
    simp_all [WordSemStateFiniteExact.evaluate, ssaCcTrans, nextVarRename,
      WordSemStateFiniteExact.setVar, Flapjack.WordAlloc.wordStateEqRel]
  · simp [WordSemStateFiniteExact.evaluate, present]

/-- Original full SSA Assign case with all six original premises and complete
existential source-permutation/result/frame/locals conclusion. Source error and
success branches are derived; no target execution or success premise is added.
The full evaluator inherits reals_as_rational_cuts (SOUNDNESS item 8). -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaCcTransCorrectAssign {width : Nat} [NeZero width] {C F : Type}
    (source target : WordSemStateFiniteExact width C F)
    (ssa : Spt Nat) (next name : Nat) (expr : WordLangExpHOL (BitVec width))
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (.assign name expr : WordLangProgHOL (BitVec width)) = true ∧
      ssaMapOK next ssa ∧ ltOK tables) :
    ssaSimulation (.assign name expr : WordLangProgHOL (BitVec width)) source target ssa next tables := by
  have bound : name < next := by
    have both : decide (name < next) = true ∧ everyVarExpHOL (fun x => decide (x < next)) expr = true := by
      simpa [everyVarHOL] using h.2.2.2.1
    exact of_decide_eq_true both.1
  let permuted := {source with permute := target.permute}
  have frame : Flapjack.WordAlloc.wordStateEqRel permuted target := by
    simpa [permuted, Flapjack.WordAlloc.wordStateEqRel] using h.1
  refine ⟨target.permute, ?_⟩
  cases found : WordSemStateFiniteExact.wordExp permuted expr with
  | none =>
    have absent : WordSemStateFiniteExact.wordExp {source with permute := target.permute} expr = none := found
    simp [WordSemStateFiniteExact.evaluate, absent]
  | some value =>
    have targetEval := ssaCcTransExpCorrect permuted expr target ssa next value
      ⟨found, frame, h.2.1⟩
    have locals := ssaLocalsRelSetVar next ssa source.locals target.locals name value
      ⟨h.2.1, h.2.2.2.2.1, bound⟩
    simp_all [WordSemStateFiniteExact.evaluate, ssaCcTrans, nextVarRename,
      WordSemStateFiniteExact.setVar, Flapjack.WordAlloc.wordStateEqRel, permuted]

end Flapjack.Compiler.Backend.WordAlloc
