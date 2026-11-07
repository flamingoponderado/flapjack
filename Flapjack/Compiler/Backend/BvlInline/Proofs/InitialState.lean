import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineFull

/-! Initial states for BVL tick inlining. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps Flapjack.SemanticPrimitivesHOL

namespace InlineInitialCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InlineInitialCarrier

/-- The initial code trees and compiler/oracle adapters satisfy the inlining
relation when the oracle's first cache is the compiler's initial result.
This is an intermediate construction in the HOL initial-state proof, not a
standalone HOL declaration. -/
theorem initialState_inStateRel {C F : Type} (limit clock : Nat) (ffi : HolFfiState F)
    (program : List (Nat × Nat × Bvl.Exp))
    (oracle : CompileOracle (Spt (Nat × Bvl.Exp) × C)) (compiler : Compiler C)
    (distinct : (program.map Prod.fst).Nodup)
    (cacheEq : (oracle 0).1.1 = (tickCompileProg limit .ln program).1) :
    inStateRel limit
      (initialState ffi (sptFromAList program) oracle (inCc limit compiler) clock)
      (initialState ffi (sptFromAList (tickCompileProg limit .ln program).2)
        (inCo limit oracle) compiler clock) := by
  let result := tickCompileProg limit .ln program
  have names : result.2.map Prod.fst = program.map Prod.fst := by
    exact mapFstTickInlineAll limit .ln program
  have range : sptSubspt result.1 (sptFromAList result.2) := by
    have emptySub : sptSubspt (.ln : Spt (Nat × Bvl.Exp)) .ln := by
      intro key member
      simp at member
    have emptyDomain : (fun key => sptDomain (.ln : Spt (Nat × Bvl.Exp)) key ∧
        key ∈ program.map Prod.fst) = (fun _ : Nat => False) := by
      funext key
      simp [sptDomain]
    have h := tickCompileProgResRange program limit result.2 .ln .ln result.1
      ⟨by change result = (result.1, result.2); exact (Prod.eta result).symm,
        distinct, emptySub, emptyDomain⟩
    simpa [sptUnion] using h
  have entries : ∀ name arity body, (name, arity, body) ∈ program →
      sptLookup name (sptFromAList program) = some (arity, body) := by
    intro name arity body member
    rw [sptLookup_sptFromAList]
    exact sptAListLookup_of_mem_nodup program distinct name arity body member
  have compatible : CacheRelated (.ln : Spt (Nat × Bvl.Exp)) (sptFromAList program) := by
    intro name arity body found
    simp at found
  have codeRel : ∀ name arity body, sptLookup name (sptFromAList program) = some (arity, body) →
      ∃ body', sptLookup name (sptFromAList result.2) = some (arity, body') ∧
        ExpRel (sptFromAList program) [body] [body'] := by
    intro name arity body found
    rw [sptLookup_sptFromAList] at found ⊢
    exact tickCompileProg_related_of_entries limit program (sptFromAList program) .ln
      entries compatible name arity body found
  have domains : sptDomain (sptFromAList result.2) = sptDomain (sptFromAList program) := by
    funext name
    apply propext
    rw [fromAList_domain_names result.2 name, fromAList_domain_names program name, names]
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, domains, codeRel⟩
  simpa [initialState, cacheEq] using range

/-- The initial-call simulation with the original compiler and oracle
adapters. Its local HOL proof is replayed with inferred types in the probe. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_initial_state"
  (fmap_as_finite_support := [refs])]
theorem evaluateInitialState {C F : Type} (limit start clock : Nat)
    (env : List BvlSem.Value) (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : CompileOracle (Spt (Nat × Bvl.Exp) × C)) (targetCompiler : Compiler C)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (h : evaluateTuple ([.call 0 (some start) []], env,
        initialState ffi (sptFromAList program) oracle (inCc limit targetCompiler) clock) = (result, final) ∧
      (oracle 0).1.1 = (tickCompileProg limit .ln program).1 ∧
      (program.map Prod.fst).Nodup ∧ result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.call 0 (some start) []], env,
        initialState ffi (sptFromAList (tickCompileProg limit .ln program).2)
          (inCo limit oracle) targetCompiler clock) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  rcases h with ⟨run, cacheEq, distinct, valid⟩
  let source := initialState ffi (sptFromAList program) oracle (inCc limit targetCompiler) clock
  let target := initialState ffi (sptFromAList (tickCompileProg limit .ln program).2)
    (inCo limit oracle) targetCompiler clock
  have rel : inStateRel limit source target :=
    initialState_inStateRel limit clock ffi program oracle targetCompiler distinct cacheEq
  exact evaluateInline [.call 0 (some start) []] env source result target final
    [.call 0 (some start) []] limit ⟨rel, expRelRefl source.code _, run, valid⟩

/-- The initial-call simulation exposes equal final FFI states. Its local HOL
proof is replayed with inferred types in the probe. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "in_evaluate_Call"
  (fmap_as_finite_support := [refs])]
theorem inEvaluateCall {C F : Type} (limit start clock : Nat)
    (env : List BvlSem.Value) (ffi : HolFfiState F) (program : List (Nat × Nat × Bvl.Exp))
    (oracle : CompileOracle (Spt (Nat × Bvl.Exp) × C)) (compiler : Compiler C)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (h : evaluateTuple ([.call 0 (some start) []], env,
        initialState ffi (sptFromAList program) oracle (inCc limit compiler) clock) = (result, final) ∧
      (oracle 0).1.1 = (tickCompileProg limit .ln program).1 ∧
      (program.map Prod.fst).Nodup ∧ result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.call 0 (some start) []], env,
        initialState ffi (sptFromAList (tickCompileProg limit .ln program).2)
          (inCo limit oracle) compiler clock) = (result, targetFinal) ∧
      final.ffi = targetFinal.ffi := by
  rcases h with ⟨run, cacheEq, distinct, valid⟩
  obtain ⟨targetFinal, targetRun, rel⟩ :=
    evaluateInitialState limit start clock env ffi program oracle compiler result final
      ⟨run, cacheEq, distinct, valid⟩
  exact ⟨targetFinal, targetRun, rel.2.2.2.1.symm⟩

end Flapjack.Compiler.Backend.BvlInline.Proofs
