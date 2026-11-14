module

public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Relations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal

@[expose] public section

/-! Primitive-operation relation for closure free-variable removal. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- The free-variable value relation satisfies the generic primitive interface. -/
theorem valueRelSimple : simpleValRel ValueRel := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n; constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .number n
  · intro x fields tag; constructor
    · intro h; cases h with | block _ xs _ related => exact ⟨xs, rfl, related⟩
    · rintro ⟨xs, rfl, related⟩; exact .block tag xs fields related
  · intro x w; constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .word64 w
  · intro x bytes; constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .byteVector bytes
  · intro x ptr flag; constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .refPtr flag ptr
  · intro body arity env args loc x h; cases h; simp [isClos]
  · intro index funs env args loc x h; cases h; simp [isClos]

/-- Updating corresponding reference entries preserves their lookup relation. -/
theorem refLookup_update {C F : Type} (s t : State C F) (ptr : Nat)
    (left right : Ref Value) (refs : ∀ key, optionRel RefRel (s.refs.lookup key) (t.refs.lookup key))
    (related : RefRel left right) :
    ∀ key, optionRel RefRel ((s.refs.updateEq (ptr, left)).lookup key)
      ((t.refs.updateEq (ptr, right)).lookup key) := by
  intro key
  by_cases same : key = ptr
  · subst key; simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, optionRel] using related
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] using refs key

/-- The free-variable state relation satisfies the generic primitive interface. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "simple_state_rel"
  (fmap_as_finite_support := [refs, code])]
theorem stateRelSimple {C F : Type} :
    simpleStateRel ValueRel (StateRel : State C F → State C F → Prop) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t ptr ⟨missing, related⟩
    have lookup := related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr <;> simp_all [optionRel]
  · intro bytes t s ptr ⟨found, related⟩
    have lookup := related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, optionRel] at lookup
    | some value =>
      simp only [left, found, optionRel] at lookup
      cases lookup
      rfl
  · intro values t s ptr ⟨found, related⟩
    have lookup := related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, optionRel] at lookup
    | some value =>
      simp only [left, found, optionRel] at lookup
      cases lookup with
      | valueArray xs _ rel => exact ⟨xs, rfl, rel⟩
  · intro mode value t s ptr ⟨found, related⟩
    have lookup := related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, optionRel] at lookup
    | some entry =>
      simp only [left, found, optionRel] at lookup
      cases lookup with
      | thunk _ v _ rel => exact ⟨v, rfl, rel⟩
  · intro s t related
    refine ⟨related.2.2.2.2.2.2.1.symm, ?_, ?_⟩
    · intro ptr
      have lookup := related.2.2.2.2.2.2.2.2.1 ptr
      cases left : s.refs.lookup ptr <;> cases right : t.refs.lookup ptr <;>
        simp_all [optionRel]
    · exact related.2.2.2.2.2.2.2.1
  · intro ffi s t related
    rcases related with ⟨aux, codeS, codeT, maxApp, positive, clock, _, globals, refs, compiler, oracle⟩
    exact ⟨aux, codeS, codeT, maxApp, positive, clock, rfl, globals, refs, compiler, oracle⟩
  · intro bytes s t ptr related
    rcases related with ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals, refs, compiler, oracle⟩
    exact ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals,
      refLookup_update s t ptr _ _ refs (.byteArray bytes), compiler, oracle⟩
  · intro s t ptr xs ys ⟨related, values⟩
    rcases related with ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals, refs, compiler, oracle⟩
    exact ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals,
      refLookup_update s t ptr _ _ refs (.valueArray xs ys values), compiler, oracle⟩
  · intro s t ptr mode v w ⟨related, values⟩
    rcases related with ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals, refs, compiler, oracle⟩
    exact ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals,
      refLookup_update s t ptr _ _ refs (.thunk mode v w values), compiler, oracle⟩
  · intro s t xs ys ⟨related, values⟩
    rcases related with ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, _, refs, compiler, oracle⟩
    have globals : List.Forall₂ (optionRel ValueRel) xs ys := by exact values
    exact ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals, refs, compiler, oracle⟩

namespace PrimitivePort
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Primitive operations preserve free-variable-related values and states. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "do_app_lemma"
  (fmap_as_finite_support := [refs, code])]
theorem doAppLemma {C F : Type} (s t : State C F) (xs ys : List Value) (op : ClosLang.Op)
    (h : StateRel s t ∧ List.Forall₂ ValueRel xs ys) :
    match doApp op xs s with
    | .err err1 => ∃ err2, doApp op ys t = .err err2 ∧
        Flapjack.SemanticPrimitivesProps.excRel ValueRel err1 err2
    | .val (x, s1) => ∃ y t1, ValueRel x y ∧ StateRel s1 t1 ∧ doApp op ys t = .val (y, t1) := by
  exact ClosProps.PrimitiveTotal.simpleValRelDoApp ValueRel StateRel s t xs ys op
    ⟨valueRelSimple, stateRelSimple⟩ h
end PrimitivePort

end Flapjack.Compiler.Backend.ClosFvs
