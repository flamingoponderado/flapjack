import Flapjack.Compiler.Backend.Semantics.WordSem.Inst
import Flapjack.HolRef

namespace Flapjack

namespace WordSemInstConstSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by `instConst`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemInstConstSupport

namespace WordSemStateFiniteExact

/-- Exact HOL `inst_const` (`wordPropsScript.sml:935-941`): the sole
    successful-instruction premise and the clock/FFI conclusions.  Like
    `inst_const_full`, it inherits `reals_as_rational_cuts` from `inst`; it
    establishes no cross-language numerical FP correspondence. -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "inst_const"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem instConst {width : Nat} [NeZero width] {C F : Type}
    (i : WordLangInst (BitVec width)) (state next : WordSemStateFiniteExact width C F)
    (h : inst i state = some next) :
    next.clock = state.clock ∧ next.ffi = state.ffi := by
  unfold inst at h
  repeat' split at h
  all_goals (try dsimp only at h)
  all_goals (repeat' split at h)
  all_goals first
    | (simp only [reduceCtorEq] at h; done)
    | (cases h; exact ⟨rfl, rfl⟩)
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩)
    | (unfold assign at h; split at h
       · cases h
       · cases h; exact ⟨rfl, rfl⟩)
    | (rename_i heq; cases h
       unfold memStore at heq
       split at heq <;> cases heq <;> exact ⟨rfl, rfl⟩)

end WordSemStateFiniteExact

end Flapjack
