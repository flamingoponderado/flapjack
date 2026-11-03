import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationDecode
import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveTotal

/-! Primitive-operation infrastructure for the known-function simulation. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation
open ClosSem ClosProps

/-- The optimizer's state relation satisfies the general primitive-operation
state interface. This is Flapjack proof infrastructure. -/
theorem stateRelSimple {C F : Type} (c : Config) (g : Spt ValApprox) :
    simpleStateRel (ValueRel c g) (StateRel (C := C) (F := F) c g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t ptr ⟨missing, related⟩
    have lookup := ClosMti.fmapRel_lookup related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr <;> simp_all [ClosMti.OptionRel]
  · intro bytes t s ptr ⟨found, related⟩
    have lookup := ClosMti.fmapRel_lookup related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, ClosMti.OptionRel] at lookup
    | some value =>
      simp only [left, found, ClosMti.OptionRel] at lookup
      cases lookup
      rfl
  · intro values t s ptr ⟨found, related⟩
    have lookup := ClosMti.fmapRel_lookup related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, ClosMti.OptionRel] at lookup
    | some value =>
      simp only [left, found, ClosMti.OptionRel] at lookup
      cases lookup with
      | valueArray xs _ rel => exact ⟨xs, rfl, rel⟩
  · intro mode value t s ptr ⟨found, related⟩
    have lookup := ClosMti.fmapRel_lookup related.2.2.2.2.2.2.2.2.1 ptr
    cases left : s.refs.lookup ptr with
    | none => simp [left, found, ClosMti.OptionRel] at lookup
    | some entry =>
      simp only [left, found, ClosMti.OptionRel] at lookup
      cases lookup with
      | thunk _ v _ rel => exact ⟨v, rfl, rel⟩
  · intro s t related
    exact ⟨related.2.2.2.2.2.1, related.2.2.2.2.2.2.2.2.1.1,
      related.2.2.2.2.2.2.2.1⟩
  · intro ffi s t related
    rcases related with ⟨aux, free, codeS, codeT, clock, _, maxApp, globals, refs, compiler, oracle⟩
    exact ⟨aux, free, codeS, codeT, clock, rfl, maxApp, globals, refs, compiler, oracle⟩
  · intro bytes s t ptr related
    rcases related with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals, refs, compiler, oracle⟩
    exact ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals,
      ClosMti.fmapRel_update refs ptr _ _ (.byteArray bytes), compiler, oracle⟩
  · intro s t ptr xs ys ⟨related, values⟩
    rcases related with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals, refs, compiler, oracle⟩
    exact ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals,
      ClosMti.fmapRel_update refs ptr _ _ (.valueArray xs ys values), compiler, oracle⟩
  · intro s t ptr mode v w ⟨related, values⟩
    rcases related with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals, refs, compiler, oracle⟩
    exact ⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals,
      ClosMti.fmapRel_update refs ptr _ _ (.thunk mode v w values), compiler, oracle⟩
  · intro s t xs ys ⟨related, values⟩
    rcases related with ⟨aux, free, codeS, codeT, clock, ffi, maxApp, _, refs, compiler, oracle⟩
    exact ⟨aux, free, codeS, codeT, clock, ffi, maxApp, values, refs, compiler, oracle⟩

namespace PrimitiveSimulation

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Primitive operations preserve the known-function simulation relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "do_app_lemma"
  (fmap_as_finite_support := [refs, code])]
theorem doAppLemma {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (xs ys : List Value) (op : ClosLang.Op)
    (h : StateRel c g s t ∧ List.Forall₂ (ValueRel c g) xs ys) :
    match doApp op xs s with
    | .err err1 => ∃ err2, doApp op ys t = .err err2 ∧ Flapjack.SemanticPrimitivesProps.excRel (ValueRel c g) err1 err2
    | .val (x, s1) => ∃ y t1, ValueRel c g x y ∧ StateRel c g s1 t1 ∧ doApp op ys t = .val (y, t1) := by
  have result := ClosProps.PrimitiveTotal.simpleValRelDoApp (ValueRel c g) (StateRel c g) s t xs ys op
    ⟨valueRelSimple c g, stateRelSimple c g⟩ h
  cases run : doApp op xs s with
  | err error => simpa [run] using result
  | val pair => cases pair; simpa [run] using result

end PrimitiveSimulation

end Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation
