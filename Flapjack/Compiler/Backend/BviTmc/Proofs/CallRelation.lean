import Flapjack.Compiler.Backend.BviTmc.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.BvlSem.Call

/-! Function lookup under the TMC code and value relations. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem BviSem

namespace CallWitness
theorem holFmapAsFiniteSupportRelationWitness_BviState {C F : Type} :
    (∀ s : BviStateBroad C F, (BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviState C F, BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end CallWitness

/-- A successful direct or indirect source call resolves to related target
arguments and either the same body or its wrapper and worker. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "find_code_rel"
  (fmap_as_finite_support_relation := [BviState.refs, f])]
theorem findCode_rel {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (values relatedValues : List Value) (source : BviState (Nat × C) F) (target : BviState C F)
    (dest : Option Nat) (args : List Value) (body : Bvi.Exp)
    (found : findCode dest values source.code = some (args, body))
    (valuesRelated : List.Forall₂ (valueRel f) values relatedValues) (statesRelated : stateRel f source target) :
    noMutcons body ∧ ∃ args' body' loc,
      findCode dest relatedValues target.code = some (args', body') ∧ envRel false f args args' ∧
      args.length = args'.length ∧
      (body ≠ body' → ∃ workerLoc, optimisedCode loc workerLoc source.code target.code ∧
        rewriteWrapperSource loc workerLoc args.length body = some body') := by
  have codes := stateRel_codeRel f source target statesRelated
  have lengths := valuesRelated.length_eq
  cases dest with
  | some loc =>
    cases lookup : sptLookup loc source.code with
    | none => simp [findCode, lookup] at found
    | some entry =>
      obtain ⟨arity, sourceBody⟩ := entry
      by_cases arityEq : values.length = arity
      · simp [findCode, lookup, arityEq] at found
        obtain ⟨rfl, rfl⟩ := found
        obtain ⟨safe, worker, targetBody, targetLookup, changed⟩ :=
          codeRel_cases loc arity sourceBody source.code target.code lookup codes
        refine ⟨safe, relatedValues, targetBody, loc, ?_, listRel_envRel f values relatedValues valuesRelated,
          lengths, ?_⟩
        · simp [findCode, targetLookup, ← lengths, arityEq]
        · intro different
          obtain ⟨optimised, wrapper⟩ := changed different
          exact ⟨worker, optimised, by simpa [arityEq] using wrapper⟩
      · simp [findCode, lookup, arityEq] at found
  | none =>
    cases values with
    | nil => simp [findCode] at found
    | cons first rest =>
      have nonempty : first :: rest ≠ [] := by simp
      have lastRel := listRel_last (valueRel f) (first :: rest) relatedValues valuesRelated nonempty
      cases last : holLast (first :: rest) with
      | number n => simp [findCode, last] at found
      | word64 w => simp [findCode, last] at found
      | block tag fields => simp [findCode, last] at found
      | refPtr flag ptr => simp [findCode, last] at found
      | codePtr loc =>
        rw [last] at lastRel
        generalize targetLast : holLast relatedValues = endValue at lastRel
        cases lastRel with
        | codePtr _ =>
          cases lookup : sptLookup loc source.code with
          | none => simp [findCode, last, lookup] at found
          | some entry =>
            obtain ⟨arity, sourceBody⟩ := entry
            by_cases arityEq : (first :: rest).length = arity + 1
            · have arityRest : rest.length = arity := by simpa using arityEq
              simp [findCode, last, lookup, arityRest] at found
              obtain ⟨rfl, rfl⟩ := found
              obtain ⟨safe, worker, targetBody, targetLookup, changed⟩ :=
                codeRel_cases loc arity sourceBody source.code target.code lookup codes
              have targetNonempty : relatedValues ≠ [] := by
                intro empty
                simp [empty] at lengths
              have lastTarget : holLast relatedValues = .codePtr loc := targetLast
              have frontRel := listRel_front (valueRel f) (first :: rest) relatedValues valuesRelated
              have frontLengths := frontRel.length_eq
              refine ⟨safe, relatedValues.dropLast, targetBody, loc, ?_,
                listRel_envRel f _ _ frontRel, frontLengths, ?_⟩
              · simp [findCode, targetNonempty, lastTarget, targetLookup, ← lengths, arityEq]
              · intro different
                obtain ⟨optimised, wrapper⟩ := changed different
                have frontLength : (first :: rest).dropLast.length = arity := by
                  simp only [List.length_dropLast]
                  omega
                exact ⟨worker, optimised, by simpa [frontLength] using wrapper⟩
            · simp [findCode, last, lookup] at found
              exfalso
              apply arityEq
              simpa using found.1

end Flapjack.Compiler.Backend.BviTmc
