module

public import Flapjack.Misc.ListLookupRel
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.ClosKnown.Compile
public import Flapjack.Compiler.Backend.ClosMti.Proofs.StateRelation
public import Flapjack.Compiler.Backend.BackendProps.StateCompiler

@[expose] public section


/-! State relation for known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation
open ClosSem ClosProps BackendProps

/-- The closure state uses canonical finite-map fields. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Source and target states agree on runtime fields, related globals and
references, and the incremental compiler and oracle transformations. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [refs, code])]
noncomputable def StateRel {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) : Prop :=
  (∀ n, (s.compileOracle n).2.2 = []) ∧
  (∀ n, fvMax 0 (s.compileOracle n).2.1) ∧
  s.code = HolFiniteMapExact.empty ∧ t.code = HolFiniteMapExact.empty ∧
  s.clock = t.clock ∧ s.ffi = t.ffi ∧ s.maxApp = t.maxApp ∧
  List.Forall₂ (optionRel (ValueRel c g)) s.globals t.globals ∧
  ClosMti.fmapRel (RefRel c g) s.refs t.refs ∧
  s.compile = stateCc (compileInc c) t.compile ∧
  t.compileOracle = stateCo (compileInc c) s.compileOracle

/-- Updating the current inline factor leaves the source incremental compiler
unchanged because it resets that factor. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "compile_inc_upd_inline_factor"]
theorem compileIncUpdateInlineFactor {α : Type} (c : Config) (k : Nat) :
    @compileInc α { c with inlineFactor := k } = @compileInc α c := by
  funext g program
  simp [compileInc, resetInlineFactor]

/-- State relation is independent of the current inline factor. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_rel_upd_inline_factor"
  (fmap_as_finite_support := [refs, code])]
theorem stateRelUpdateInlineFactor {C F : Type} (c : Config) (k : Nat) :
    (fun (g : Spt ValApprox) (s : State (Spt ValApprox × C) F) (t : State C F) =>
      StateRel { c with inlineFactor := k } g s t) =
    (fun (g : Spt ValApprox) (s : State (Spt ValApprox × C) F) (t : State C F) =>
      StateRel c g s t) := by
  funext g s t
  simp [StateRel, valueRelUpdateInlineFactor, refRelUpdateInlineFactor, compileIncUpdateInlineFactor]

/-- Extending the approximation tree preserves the state relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_rel_subspt"
  (fmap_as_finite_support := [refs, code])]
theorem stateRelSubspt {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (g' : Spt ValApprox)
    (h : StateRel c g s t ∧ sptSubspt g g') : StateRel c g' s t := by
  obtain ⟨⟨aux, free, codeS, codeT, clock, ffi, maxApp, globals, refs, compiler, oracle⟩, sub⟩ := h
  refine ⟨aux, free, codeS, codeT, clock, ffi, maxApp, ?_, ?_, compiler, oracle⟩
  · apply List.Forall₂.imp ?_ globals
    intro left right rel
    cases left <;> cases right <;> simp_all [optionRel]
    exact valueRelSubspt c g _ _ g' ⟨rel, sub⟩
  · obtain ⟨domain, entries⟩ := refs
    refine ⟨domain, ?_⟩
    intro key value found
    obtain ⟨other, foundOther, related⟩ := entries key value found
    exact ⟨other, foundOther, refRelSubspt c g value other g' ⟨related, sub⟩⟩

/-- A mapped source global has a related target global at the same index. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "state_rel_get_global_IMP"
  (fmap_as_finite_support := [refs, code])]
theorem stateRelGetGlobal {C F : Type} (c : Config) (g : Spt ValApprox)
    (s : State (Spt ValApprox × C) F) (t : State C F) (n : Nat) (v1 : ClosSem.Value)
    (h : StateRel c g s t ∧ getGlobal n s.globals = some (some v1)) :
    ∃ v2, getGlobal n t.globals = some (some v2) ∧ ValueRel c g v1 v2 := by
  obtain ⟨next, found, related⟩ := Flapjack.forall₂_lookup h.1.2.2.2.2.2.2.2.1 n (some v1) h.2
  cases next with
  | none => simp [optionRel] at related
  | some v2 => exact ⟨v2, found, related⟩

end Flapjack.Compiler.Backend.ClosKnown.Relations.StateRelation
