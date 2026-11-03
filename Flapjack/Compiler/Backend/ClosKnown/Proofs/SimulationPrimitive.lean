import Flapjack.Compiler.Backend.ClosKnown.Proofs.SimulationDecode
import Flapjack.Compiler.Backend.ClosKnown.Proofs.StateRelation

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

end Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation
