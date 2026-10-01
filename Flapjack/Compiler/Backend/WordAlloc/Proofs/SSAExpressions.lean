import Flapjack.Compiler.Backend.WordAlloc.SSATransInst
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Expressions
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Flapjack infrastructure identifying two reviewed constructor-for-constructor
expression renamers. This equality has no independent HOL declaration. -/
theorem ssaCcTransExp_eq_applyColourExp {width : Nat} [NeZero width]
    (ssa : Spt Nat) (expr : WordLangExpHOL (BitVec width)) :
    ssaCcTransExp ssa expr = Flapjack.WordAlloc.applyColourExp (optionLookup ssa) expr := by
  induction expr using ssaCcTransExp.induct with
  | case1 num => simp [ssaCcTransExp, Flapjack.WordAlloc.applyColourExp,
      Flapjack.WordAlloc.applyColourExpCore]
  | case2 expr ih => simp [ssaCcTransExp, Flapjack.WordAlloc.applyColourExp,
      Flapjack.WordAlloc.applyColourExpCore, ih]
  | case3 operator args ih =>
    rw [ssaCcTransExp_op]
    simp only [Flapjack.WordAlloc.applyColourExp, Flapjack.WordAlloc.applyColourExpCore]
    congr 1
    apply List.map_congr_left
    intro expr member
    exact ih expr member
  | case4 sh left right ihLeft ihRight =>
    simp [ssaCcTransExp, Flapjack.WordAlloc.applyColourExp,
      Flapjack.WordAlloc.applyColourExpCore, ihLeft, ihRight]
  | case5 expr notVar notLoad notOp notShift =>
    cases expr <;> simp_all [ssaCcTransExp, Flapjack.WordAlloc.applyColourExp,
      Flapjack.WordAlloc.applyColourExpCore]

namespace SSAExpressionWitnesses

/-- Canonical imported state roundtrip for the expression simulation. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end SSAExpressionWitnesses

/-- Full HOL SSA expression success simulation. The original source/target share
word, code, and FFI types; the only premises are source expression success,
full state equality and SSA locals correspondence. The proof factors through
constructor-identical expression colouring, with its live-local premise derived
from SSA locals correspondence rather than added to the statement. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_cc_trans_exp_correct"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs, WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem ssaCcTransExpCorrect {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F) (expr : WordLangExpHOL (BitVec width))
    (target : WordSemStateFiniteExact width C F) (ssa : Spt Nat) (next : Nat)
    (result : WordLocW width)
    (h : WordSemStateFiniteExact.wordExp source expr = some result ∧
      Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next ssa source.locals target.locals) :
    WordSemStateFiniteExact.wordExp target (ssaCcTransExp ssa expr) = some result := by
  rw [ssaCcTransExp_eq_applyColourExp]
  apply Flapjack.WordAlloc.applyColourExpLemma source expr target (optionLookup ssa) result
  refine ⟨h.1, h.2.1, ?_⟩
  intro key value present
  obtain ⟨domain, matching, _⟩ := h.2.2.2 key value present.2
  obtain ⟨register, found⟩ := (sptMem_iff_lookup key ssa).mp domain
  simpa only [optionLookup, found, Option.getD_some] using matching

end Flapjack.Compiler.Backend.WordAlloc
