module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Relations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal

@[expose] public section

/-! Primitive-operation relations for closure let-operation correctness. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosSem ClosProps

/-- The value relation satisfies the generic primitive interface. This
specialization is Lean-side infrastructure, not a standalone HOL declaration. -/
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

/-- Related states match reference lookups in either direction. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "state_rel_opt_rel_refs"
  (fmap_as_finite_support := [refs, code])]
theorem state_rel_opt_rel_refs {C F : Type} (s t : State C F) (key : Nat)
    (left right : Option (Ref Value)) :
    (StateRel s t ∧ s.refs.lookup key = left →
      ∃ right, t.refs.lookup key = right ∧ Flapjack.optionRel RefRel left right) ∧
    (StateRel s t ∧ t.refs.lookup key = right →
      ∃ left, s.refs.lookup key = left ∧ Flapjack.optionRel RefRel left right) := by
  constructor
  · rintro ⟨states, found⟩
    refine ⟨t.refs.lookup key, rfl, ?_⟩
    simpa only [found] using ClosMti.fmapRel_lookup states.2.2.2.2.2.2.2.2.1 key
  · rintro ⟨states, found⟩
    refine ⟨s.refs.lookup key, rfl, ?_⟩
    simpa only [found] using ClosMti.fmapRel_lookup states.2.2.2.2.2.2.2.2.1 key

/-- Updating corresponding references preserves the relation. This helper is
Lean-side infrastructure, not a standalone HOL declaration. -/
theorem stateRel_updateRefs {C F : Type} {s t : State C F} (related : StateRel s t)
    (key : Nat) (left right : Ref Value) (values : RefRel left right) :
    StateRel { s with refs := s.refs.updateEq (key, left) }
      { t with refs := t.refs.updateEq (key, right) } := by
  obtain ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals, refs, compiler, oracle⟩ := related
  exact ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals,
    ClosMti.fmapRel_update refs key left right values, compiler, oracle⟩

namespace PrimitivePort

/-- The closure state has the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The let-operation state relation satisfies the primitive interface. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "simple_state_rel"
  (fmap_as_finite_support := [refs, code])]
theorem stateRelSimple {C F : Type} : simpleStateRel ValueRel (StateRel : State C F → State C F → Prop) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t ptr ⟨missing, related⟩
    obtain ⟨_, rfl, lookup⟩ := (state_rel_opt_rel_refs s t ptr (s.refs.lookup ptr) (t.refs.lookup ptr)).1 ⟨related, rfl⟩
    cases left : s.refs.lookup ptr <;> simp_all [Flapjack.optionRel]
  · intro bytes t s ptr ⟨found, related⟩
    obtain ⟨_, rfl, lookup⟩ := (state_rel_opt_rel_refs s t ptr (s.refs.lookup ptr) (t.refs.lookup ptr)).1 ⟨related, rfl⟩
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, Flapjack.optionRel] at lookup
    | some value =>
      simp only [left, found, Flapjack.optionRel] at lookup
      cases lookup
      rfl
  · intro values t s ptr ⟨found, related⟩
    obtain ⟨_, rfl, lookup⟩ := (state_rel_opt_rel_refs s t ptr (s.refs.lookup ptr) (t.refs.lookup ptr)).1 ⟨related, rfl⟩
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, Flapjack.optionRel] at lookup
    | some value =>
      simp only [left, found, Flapjack.optionRel] at lookup
      cases lookup with
      | valueArray xs _ rel => exact ⟨xs, rfl, rel⟩
  · intro mode value t s ptr ⟨found, related⟩
    obtain ⟨_, rfl, lookup⟩ := (state_rel_opt_rel_refs s t ptr (s.refs.lookup ptr) (t.refs.lookup ptr)).1 ⟨related, rfl⟩
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, Flapjack.optionRel] at lookup
    | some entry =>
      simp only [left, found, Flapjack.optionRel] at lookup
      cases lookup with
      | thunk _ v _ rel => exact ⟨v, rfl, rel⟩
  · intro s t related
    refine ⟨related.2.2.2.2.2.2.1.symm, related.2.2.2.2.2.2.2.2.1.1, ?_⟩
    exact related.2.2.2.2.2.2.2.1
  · intro ffi s t related
    rcases related with ⟨aux, codeS, codeT, maxApp, positive, clock, _, globals, refs, compiler, oracle⟩
    exact ⟨aux, codeS, codeT, maxApp, positive, clock, rfl, globals, refs, compiler, oracle⟩
  · intro bytes s t ptr related
    exact stateRel_updateRefs related ptr _ _ (.byteArray bytes)
  · intro s t ptr xs ys ⟨related, values⟩
    exact stateRel_updateRefs related ptr _ _ (.valueArray xs ys values)
  · intro s t ptr mode v w ⟨related, values⟩
    exact stateRel_updateRefs related ptr _ _ (.thunk mode v w values)
  · intro s t xs ys ⟨related, values⟩
    rcases related with ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, _, refs, compiler, oracle⟩
    have globals : List.Forall₂ (Flapjack.optionRel ValueRel) xs ys := by exact values
    exact ⟨aux, codeS, codeT, maxApp, positive, clock, ffi, globals, refs, compiler, oracle⟩

/-- Primitive operations preserve related values and states. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "do_app_lemma"
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

end Flapjack.Compiler.Backend.ClosLetop
