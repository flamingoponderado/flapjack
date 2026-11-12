module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.IncrementalAddresses
public import Flapjack.Compiler.Backend.ClosCall.Compile
import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMembership
@[expose] public section

/-! Exact label and numbering facts for incremental closure compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosProps

/-- Incremental compilation emits precisely the shifted entry and code labels. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "MAP_FST_compile_inc"]
theorem mapFst_compileInc (maxApp : Nat) (p : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) :
    (compileInc maxApp p).map Prod.fst =
      (((List.range (max 1 (extractNameSource p.1).2.length)).map
          ((extractNameSource p.1).1 + ·)) ++ p.2.map Prod.fst ++
        (codeLocations ((chainExps (extractNameSource p.1).1 (extractNameSource p.1).2 ++ p.2).map
          (fun t => t.2.2))).reverse).map (numStubs maxApp + ·) := by
  unfold compileInc
  cases h : extractNameSource p.1 with
  | mk start es =>
    rw [map_fst_compileProg]
    simp [List.map_append, mapFst_chainExps_any, List.append_assoc]

/-- Singleton numbering agrees with expression numbering in both directions. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "renumber_code_locs_sing"]
theorem renumberCodeLocs_sing :
    (∀ n es n' es', es.length = 1 →
      (ClosNumber.renumberList n es = (n', es') ↔
        es'.length = 1 ∧ ClosNumber.renumber n (Flapjack.holHd es) =
          (n', Flapjack.holHd es'))) ∧
    (∀ n e n' e', ClosNumber.renumber n e = (n', e') ↔
      ClosNumber.renumberList n [e] = (n', [e'])) := by
  have single (n : Nat) (e : ClosLang.Exp) :
      ClosNumber.renumberList n [e] =
        ((ClosNumber.renumber n e).1, [(ClosNumber.renumber n e).2]) := by
    simp [ClosNumber.renumberList]
  constructor
  · intro n es n' es' len
    cases es with
    | nil => simp at len
    | cons e rest =>
      cases rest with
      | cons x xs => simp at len
      | nil =>
        cases es' with
        | nil => simp [single]
        | cons e' rest =>
          cases rest with
          | cons x xs => simp [single]
          | nil => simp [single, Flapjack.holHd, Prod.ext_iff]
  · intro n e n' e'
    simp [single, Prod.ext_iff]

/-- Direct-call conversion introduces no locations outside its initial code. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "set_code_locs_FST_calls_SUBSET"]
theorem setCodeLocs_fstCalls_subset (x : List ClosLang.Exp) (y : ClosCall.State) :
    {k | k ∈ codeLocations (ClosCall.calls x y).1} ⊆
      {k | k ∈ codeLocations x} ∪ {k | k ∈ codeLocations (y.2.map (fun t => t.2.2))} := by
  intro k hk
  have run : ClosCall.calls x y = ((ClosCall.calls x y).1, (ClosCall.calls x y).2) := by
    cases ClosCall.calls x y; rfl
  exact ClosCall.calls_codeLocations_mem x y _ _ run k (Or.inl hk)
end Flapjack.Compiler.Backend.ClosToBvl
