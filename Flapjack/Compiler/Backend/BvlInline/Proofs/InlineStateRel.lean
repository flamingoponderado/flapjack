import Flapjack.Compiler.Backend.BvlInline.Program
import Flapjack.Compiler.Backend.BvlInline.Proofs.ExpRel
import Flapjack.Compiler.Backend.Semantics.BvlSem.State

/-! State and compiler relations for BVL call inlining. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open BvlSem

namespace InlineCarrier
/-- The canonical BVL reference-map state representation roundtrips. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InlineCarrier

/-- Adapt a compiler callback to transform dynamically installed code and
retain the resulting inlining cache in its configuration. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "in_cc_def"]
def inCc {C A B D : Type} (limit : Nat)
    (compiler : C → List (Nat × Nat × Bvl.Exp) → Option (A × B × D)) :
    (Spt (Nat × Bvl.Exp) × C) → List (Nat × Nat × Bvl.Exp) →
      Option (A × B × (Spt (Nat × Bvl.Exp) × D)) :=
  fun (cache, config) program =>
    let (cache', program') := tickCompileProg limit cache program
    match compiler config program' with
    | none => none
    | some (code, data, config') => some (code, data, (cache', config'))

/-- Adapt an oracle by inlining each stored program with its cache. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "in_co_def"]
def inCo {I C : Type} (limit : Nat)
    (oracle : I → (Spt (Nat × Bvl.Exp) × C) × List (Nat × Nat × Bvl.Exp)) :
    I → C × List (Nat × Nat × Bvl.Exp) :=
  fun index =>
    let ((cache, config), program) := oracle index
    let (_, program') := tickCompileProg limit cache program
    (config, program')

/-- Relate original and inlined BVL states, including all future compilation
oracle entries and the correspondence between installed code bodies. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "in_state_rel_def"
  (fmap_as_finite_support := [refs])]
def inStateRel {C F : Type} (limit : Nat)
    (source : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F) : Prop :=
  target.globals = source.globals ∧
  target.refs = source.refs ∧
  target.clock = source.clock ∧
  target.ffi = source.ffi ∧
  target.compileOracle = (fun n =>
    let ((cache, config), program) := source.compileOracle n
    let (_, program') := tickCompileProg limit cache program
    (config, program')) ∧
  sptSubspt (source.compileOracle 0).1.1 target.code ∧
  source.compile = inCc limit target.compile ∧
  sptDomain target.code = sptDomain source.code ∧
  ∀ name arity body, sptLookup name source.code = some (arity, body) →
    ∃ body', sptLookup name target.code = some (arity, body') ∧
      ExpRel source.code [body] [body']

/-- Inlining-related states share the runtime fields. This is a projection
of the source relation, not a separate HOL declaration. -/
theorem inStateRel_fields {C F : Type} (limit : Nat)
    (source : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target) :
    target.globals = source.globals ∧ target.refs = source.refs ∧
      target.clock = source.clock ∧ target.ffi = source.ffi :=
  ⟨related.1, related.2.1, related.2.2.1, related.2.2.2.1⟩

/-- The oracle field uses the original inlining adapter. This is a projection
of the source relation, not a separate HOL declaration. -/
theorem inStateRel_oracle {C F : Type} (limit : Nat)
    (source : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
    (related : inStateRel limit source target) :
    target.compileOracle = inCo limit source.compileOracle :=
  related.2.2.2.2.1

end Flapjack.Compiler.Backend.BvlInline.Proofs
