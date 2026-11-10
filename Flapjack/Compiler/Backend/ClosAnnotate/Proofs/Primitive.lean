module

public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.StateRelation
public import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Operations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal

@[expose] public section

/-! Generic primitive-operation simulation for closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- The annotation value relation satisfies the generic primitive interface,
as needed to instantiate the original primitive-operation proof. -/
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

/-- Updating related references preserves their pointwise lookup relation.
This supports the generic HOL primitive-operation theorem. -/
private theorem refLookup_update {C F : Type} (s t : State C F) (ptr : Nat)
    (left right : Ref Value)
    (refs : ∀ key, optionRel (refRel ValueRel) (s.refs.lookup key) (t.refs.lookup key))
    (related : refRel ValueRel left right) :
    ∀ key, optionRel (refRel ValueRel) ((s.refs.updateEq (ptr, left)).lookup key)
      ((t.refs.updateEq (ptr, right)).lookup key) := by
  intro key
  by_cases same : key = ptr
  · subst key; simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, optionRel] using related
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] using refs key

/-- Annotation-related states satisfy the generic primitive interface,
as required by the original primitive-operation proof. -/
theorem stateRelSimple {C F : Type} : simpleStateRel ValueRel (StateRel (C := C) (F := F)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t ptr ⟨missing, related⟩
    have lookup := related.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr <;> simp_all [optionRel]
  · intro bytes t s ptr ⟨found, related⟩
    have lookup := related.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, optionRel] at lookup
    | some value =>
      simp only [left, found, optionRel] at lookup
      cases value <;> simp_all [refRel]
  · intro values t s ptr ⟨found, related⟩
    have lookup := related.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, optionRel] at lookup
    | some value =>
      simp only [left, found, optionRel] at lookup
      cases value <;> simp_all [refRel]
  · intro mode value t s ptr ⟨found, related⟩
    have lookup := related.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, optionRel] at lookup
    | some entry =>
      simp only [left, found, optionRel] at lookup
      cases entry <;> simp_all [refRel]
  · intro s t related
    refine ⟨related.2.1, ?_, related.2.2.2.2.2.1⟩
    intro ptr
    have lookup := related.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr <;> cases right : t.refs.lookup ptr <;>
      simp_all [optionRel]
  · intro ffi s t related
    rcases related with ⟨clock, _, maxApp, oracle, compiler, globals, refs, code⟩
    exact ⟨clock, rfl, maxApp, oracle, compiler, globals, refs, code⟩
  · intro bytes s t ptr related
    rcases related with ⟨clock, ffi, maxApp, oracle, compiler, globals, refs, code⟩
    exact ⟨clock, ffi, maxApp, oracle, compiler, globals,
      refLookup_update s t ptr _ _ refs (by simp [refRel]), code⟩
  · intro s t ptr xs ys ⟨related, values⟩
    rcases related with ⟨clock, ffi, maxApp, oracle, compiler, globals, refs, code⟩
    exact ⟨clock, ffi, maxApp, oracle, compiler, globals,
      refLookup_update s t ptr _ _ refs (by simpa [refRel] using values), code⟩
  · intro s t ptr mode v w ⟨related, values⟩
    rcases related with ⟨clock, ffi, maxApp, oracle, compiler, globals, refs, code⟩
    exact ⟨clock, ffi, maxApp, oracle, compiler, globals,
      refLookup_update s t ptr _ _ refs (by simpa [refRel] using values), code⟩
  · intro s t xs ys ⟨related, values⟩
    rcases related with ⟨clock, ffi, maxApp, oracle, compiler, _, refs, code⟩
    exact ⟨clock, ffi, maxApp, oracle, compiler, values, refs, code⟩

/-- The generic primitive theorem supplies the evaluator's simulation
interface. This Flapjack-specific adapter is used by the annotation proof. -/
theorem primitiveSimulation_generic {C F : Type} (op : ClosLang.Op) :
    PrimitiveSimulation (C := C) (F := F) op := by
  intro values nextValues source target valuesRel states
  have sim := ClosProps.PrimitiveTotal.simpleValRelDoApp ValueRel StateRel source target
    values nextValues op ⟨valueRelSimple, stateRelSimple⟩ ⟨states, valuesRel⟩
  cases run : doApp op values source with
  | err error =>
    rw [run] at sim
    obtain ⟨nextError, nextRun, errors⟩ := sim
    exact ⟨.err nextError, nextRun, by simpa [AppResultRel, ResultRel,
      Flapjack.SemanticPrimitivesProps.resultRel] using errors⟩
  | val pair =>
    obtain ⟨value, state⟩ := pair
    rw [run] at sim
    obtain ⟨nextValue, nextState, vals, states, nextRun⟩ := sim
    exact ⟨.val (nextValue, nextState), nextRun, by simpa [AppResultRel] using And.intro vals states⟩

end Flapjack.Compiler.Backend.ClosAnnotate
