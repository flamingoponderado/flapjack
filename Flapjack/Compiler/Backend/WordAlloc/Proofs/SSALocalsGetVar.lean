import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALocals
import Flapjack.Compiler.Backend.WordAlloc.SSASetup
import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors

namespace Flapjack.Compiler.Backend.WordAlloc

namespace LocalsGetVarWitnesses

/-- Canonical imported native WordSem finite-map roundtrip. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end LocalsGetVarWitnesses

/-- Full original native SSA get_var transport. Only the original locals
relation and successful source read are assumed; target read success is proved.
Source/target code and FFI hosts remain independently arbitrary, as confirmed
by the complete original type replay. Opaque THE is observed only after the
original locals relation supplies the source map domain. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "ssa_locals_rel_get_var"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store]) (words_as_type_indexed_bitvec)]
theorem ssaLocalsRelGetVar {width : Nat} [NeZero width] {C₁ F₁ C₂ F₂ : Type}
    (next : Nat) (ssa : Spt Nat) (source : WordSemStateFiniteExact width C₁ F₁)
    (target : WordSemStateFiniteExact width C₂ F₂) (name : Nat) (value : WordLocW width)
    (h : ssaLocalsRel next ssa source.locals target.locals ∧
      WordSemStateFiniteExact.getVar name source = some value) :
    WordSemStateFiniteExact.getVar (optionLookup ssa name) target = some value := by
  have sourceLookup : sptLookup name source.locals = some value := h.2
  obtain ⟨domain, lookup, _⟩ := h.1.2 name value sourceLookup
  obtain ⟨register, found⟩ := (sptMem_iff_lookup name ssa).mp domain
  simpa only [WordSemStateFiniteExact.getVar, optionLookup, found, Option.getD_some] using lookup

end Flapjack.Compiler.Backend.WordAlloc
