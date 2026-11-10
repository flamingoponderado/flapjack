module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateGrowth
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelsOriginal

@[expose] public section

/-! Direct-call conversion extends well-formed compiler states. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- Under the original freshness conditions, direct-call conversion extends
the sparse state and preserves every existing auxiliary-code lookup. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_subg"]
theorem calls_subg (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g) ∧ (g0.2.map Prod.fst).Nodup ∧
      (codeLocations xs).Nodup ∧
      (∀ label, ¬ (label ∈ Nat.succ '' {x | x ∈ codeLocations xs} ∧
        label ∈ g0.2.map Prod.fst))) : stateExtends g0 g := by
  have distinct := calls_allDistinct xs g0 ys g h
  have sparse := calls_subspt xs g0 ys g h.1
  have suffix := calls_suffix xs g0 ys g h.1
  obtain ⟨added, eq⟩ := suffix
  have distinctAppend : ((added.map Prod.fst) ++ (g0.2.map Prod.fst)).Nodup := by
    rw [← List.map_append, eq]
    exact distinct
  have disjoint := (List.nodup_append.mp distinctAppend).2.2
  refine ⟨sparse, ?_, distinct⟩
  intro key value found
  have oldMember : key ∈ g0.2.map Prod.fst := by
    exact List.mem_map.mpr ⟨(key, value), holALookup_member _ _ _ found, rfl⟩
  have missing : holALookup added key = none := by
    cases lookup : holALookup added key with
    | none => rfl
    | some v =>
      have newMember : key ∈ added.map Prod.fst :=
        List.mem_map.mpr ⟨(key, v), holALookup_member _ _ _ lookup, rfl⟩
      exact False.elim (disjoint key newMember key oldMember rfl)
  rw [← eq, holALookup_append, missing]
  exact found

end Flapjack.Compiler.Backend.ClosCall
