import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocalsGetVar

namespace Flapjack.Compiler.Backend.WordAlloc

namespace LocalsGetVarsWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LocalsGetVarsWitnesses

/-- Full original native SSA get_vars transport, with only the original
locals relation and successful source list-read premises. Target list-read
success is proved. Source and target code/FFI hosts remain independently
arbitrary, as confirmed by the full original carrier capture. The proof uses
the actual native recursive getVars clauses and original single-register
transport; it adds no target-success or source-domain premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem ssaLocalsRelGetVars {width : Nat} [NeZero width] {C₁ F₁ C₂ F₂ : Type}
    (names : List Nat) (values : List (WordLocW width)) (next : Nat) (ssa : Spt Nat)
    (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂)
    (h : ssaLocalsRel next ssa source.locals target.locals ∧
      WordSemStateFiniteExact.getVars names source = some values) :
    WordSemStateFiniteExact.getVars (names.map (optionLookup ssa)) target = some values := by
  induction names generalizing values with
  | nil => simpa only [List.map_nil, WordSemStateFiniteExact.getVars] using h.2
  | cons name names ih =>
      cases head : WordSemStateFiniteExact.getVar name source with
      | none => simp [WordSemStateFiniteExact.getVars, head] at h
      | some value =>
          cases tail : WordSemStateFiniteExact.getVars names source with
          | none => simp [WordSemStateFiniteExact.getVars, head, tail] at h
          | some suffix =>
              have renamed := ssaLocalsRelGetVar next ssa source target name value ⟨h.1, head⟩
              have renamedTail := ih suffix ⟨h.1, tail⟩
              simpa only [List.map_cons, WordSemStateFiniteExact.getVars, renamed,
                renamedTail, head, tail] using h.2

end Flapjack.Compiler.Backend.WordAlloc
