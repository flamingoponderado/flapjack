module

public import Flapjack.Compiler.Inference.EnvRel.Relation
public import Flapjack.Compiler.Inference.InferProps.Lift

@[expose] public section

/-! Module lifting preserves the inference/declarative environment relation. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.TypeSoundInvariants
  Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferProps
  Flapjack.Basis.Pure.MlString

/-- Module lifting preserves the environment relation, expanded one level to
    expose its fixed empty maps. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "env_rel_lift"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem envRelLift (tenv : TypeEnv) (ienv : Env) (mn : MlString)
    (h : ienvOk (fun _ => False) ienv ∧ tenvOk tenv ∧
      (∀ path, nsLookupMod ienv.infV path = none ↔ nsLookupMod tenv.v path = none) ∧
      envRelSoundModel HolFiniteMapExact.holEmpty ienv tenv .empty ∧
      envRelCompleteModel HolFiniteMapExact.holEmpty ienv tenv .empty) :
    ienvOk (fun _ => False) (liftIenv mn ienv) ∧ tenvOk (tenvLift mn tenv) ∧
      (∀ path, nsLookupMod (liftIenv mn ienv).infV path = none ↔
        nsLookupMod (tenvLift mn tenv).v path = none) ∧
      envRelSoundModel HolFiniteMapExact.holEmpty (liftIenv mn ienv) (tenvLift mn tenv) .empty ∧
      envRelCompleteModel HolFiniteMapExact.holEmpty (liftIenv mn ienv) (tenvLift mn tenv) .empty := by
  change envRelModel tenv ienv at h
  change envRelModel (tenvLift mn tenv) (liftIenv mn ienv)
  obtain ⟨ienvOk, htenv, mods, sound, complete⟩ := h
  refine ⟨ienvOkLift mn ienv _ ienvOk, ?_, ?_, ?_, ?_⟩
  · simpa [tenvOk, tenvLift, tenvValOk, tenvCtorOk, tenvAbbrevOk, nsAll_nsLift] using htenv
  · intro path
    cases path with
    | nil => simp [liftIenv, tenvLift, nsLookupMod_nsLift]
    | cons head rest =>
      by_cases same : mn = head
      · subst head
        simpa [liftIenv, tenvLift, nsLookupMod_nsLift] using mods rest
      · simp [liftIenv, tenvLift, nsLookupMod_nsLift, same]
  · refine ⟨?_, ?_, ?_⟩
    · simp [liftIenv, tenvLift, sound.1]
    · simp [liftIenv, tenvLift, sound.2.1]
    · intro id ts found
      cases id with
      | short name => simp [liftIenv, nsLookup_nsLift] at found
      | long head rest =>
        by_cases same : mn = head
        · subst head
          have old : nsLookup ienv.infV rest = some ts := by
            simpa [liftIenv, nsLookup_nsLift] using found
          obtain ⟨tvs, t, checked, lookup, approx⟩ := sound.2.2 rest ts old
          refine ⟨tvs, t, checked, ?_, approx⟩
          simpa [lookupVar, lookupVarEEmpty, tenvLift, nsLookup_nsLift] using lookup
        · simp [liftIenv, nsLookup_nsLift, same] at found
  · refine ⟨?_, ?_, ?_⟩
    · simp [liftIenv, tenvLift, complete.1]
    · simp [liftIenv, tenvLift, complete.2.1]
    · intro id tvs t found
      cases id with
      | short name => simp [lookupVar, lookupVarEEmpty, tenvLift, nsLookup_nsLift] at found
      | long head rest =>
        by_cases same : mn = head
        · subst head
          have old : lookupVar rest .empty tenv = some (tvs, t) := by
            simpa [lookupVar, lookupVarEEmpty, tenvLift, nsLookup_nsLift] using found
          obtain ⟨checked, tvs2, t2, lookup, approx⟩ := complete.2.2 rest tvs t old
          refine ⟨checked, tvs2, t2, ?_, approx⟩
          simpa [liftIenv, nsLookup_nsLift] using lookup
        · simp [lookupVar, lookupVarEEmpty, tenvLift, nsLookup_nsLift, same] at found

end Flapjack.Compiler.Inference.EnvRel
