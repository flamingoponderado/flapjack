module

public import Flapjack.Compiler.Inference.EnvRel.Approx
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.TypeSoundInvariants
public import Flapjack.NamespaceProps.MapLookup

@[expose] public section

/-! Source-shaped inference/declarative environment relations. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferProps
  Flapjack.TypeSoundInvariants

/-- Source-shaped soundness relation. Untagged because scheme approximation
    uses a normalizer whose off-well-formedness choice is not source-reviewed. -/
noncomputable def envRelSoundModel (s : HolFiniteMapExact Nat InferT)
    (ienv : Env) (tenv : TypeEnv) (tenvE : TenvValExp) : Prop :=
  ienv.infT = tenv.t ∧ ienv.infC = tenv.c ∧
    ∀ x ts, nsLookup ienv.infV x = some ts →
      ∃ tvs t, checkFreevars (tvs + numTvs tenvE) [] t = true ∧
        lookupVar x tenvE tenv = some (tvs, t) ∧
        tschemeApproxModel (numTvs tenvE) s ts (tvs, unconvertT t)

/-- Source-shaped completeness relation, with the same normalizer boundary. -/
noncomputable def envRelCompleteModel (s : HolFiniteMapExact Nat InferT)
    (ienv : Env) (tenv : TypeEnv) (tenvE : TenvValExp) : Prop :=
  ienv.infT = tenv.t ∧ ienv.infC = tenv.c ∧
    ∀ x tvs t, lookupVar x tenvE tenv = some (tvs, t) →
      (∃ n, checkFreevars n [] t = true) ∧
      ∃ tvs2 t2, nsLookup ienv.infV x = some (tvs2, t2) ∧
        tschemeApproxModel (numTvs tenvE) s (tvs, unconvertT t) (tvs2, t2)

/-- Source-shaped top-level environment relation. The two general relations
    above remain untagged pending source review of the normalizer boundary. -/
noncomputable def envRelModel (tenv : TypeEnv) (ienv : Env) : Prop :=
  ienvOk (fun _ => False) ienv ∧ tenvOk tenv ∧
    (∀ x, nsLookupMod ienv.infV x = none ↔ nsLookupMod tenv.v x = none) ∧
    envRelSoundModel HolFiniteMapExact.holEmpty ienv tenv .empty ∧
    envRelCompleteModel HolFiniteMapExact.holEmpty ienv tenv .empty

/-- Inference-to-declarative conversion in the source-shaped model. This
    remains untagged because `convertT` has an unspecified source case for
    unification variables; checked environments exclude that case. -/
noncomputable def ienvToTenvModel (ienv : Env) : TypeEnv :=
  ⟨nsMap (fun entry => (entry.1, convertT entry.2)) ienv.infV, ienv.infC, ienv.infT⟩

/-- A closed inference environment relates to its converted declarative
    environment; the relation is expanded to expose the fixed empty maps. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "env_rel_ienv_to_tenv"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem envRelIenvToTenv (ienv : Env) (h : ienvOk (fun _ => False) ienv) :
    ienvOk (fun _ => False) ienv ∧ tenvOk (ienvToTenvModel ienv) ∧
      (∀ path, nsLookupMod ienv.infV path = none ↔ nsLookupMod (ienvToTenvModel ienv).v path = none) ∧
      envRelSoundModel HolFiniteMapExact.holEmpty ienv (ienvToTenvModel ienv) .empty ∧
      envRelCompleteModel HolFiniteMapExact.holEmpty ienv (ienvToTenvModel ienv) .empty := by
  change envRelModel (ienvToTenvModel ienv) ienv
  classical
  have decEq : Classical.typeDecidableEq Flapjack.Basis.Pure.MlString.MlString =
      Flapjack.Basis.Pure.MlString.instDecidableEqMlString := by
    funext a b
    exact Subsingleton.elim _ _
  have valueOk := h.1
  unfold ienvValOk nsAll at valueOk
  change ∀ id v, @nsLookup _ _ _ (Classical.typeDecidableEq _) (Classical.typeDecidableEq _)
    ienv.infV id = some v → checkT v.1 (fun _ => False) v.2 at valueOk
  rw [decEq] at valueOk
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, h.2.1, h.2.2⟩
    unfold tenvValOk
    change @nsAll _ _ _ (Classical.typeDecidableEq _) (Classical.typeDecidableEq _)
      (fun _ entry => checkFreevars entry.1 [] entry.2 = true)
      (nsMap (fun entry => (entry.1, convertT entry.2)) ienv.infV)
    rw [decEq, nsAll_nsMap]
    intro id entry found
    exact checkTToCheckFreevars entry.1 entry.2 (valueOk id entry found)
  · intro path
    change nsLookupMod ienv.infV path = none ↔
      nsLookupMod (nsMap (fun entry => (entry.1, convertT entry.2)) ienv.infV) path = none
    rw [nsLookupMod_nsMap]
    cases nsLookupMod ienv.infV path <;> simp
  · refine ⟨rfl, rfl, ?_⟩
    intro id ⟨tvs, t⟩ found
    have valid := valueOk id (tvs, t) found
    refine ⟨tvs, convertT t, ?_, ?_, ?_⟩
    · simpa [numTvs] using checkTToCheckFreevars tvs t valid
    · simp [lookupVar, lookupVarEEmpty, ienvToTenvModel, nsLookup_nsMap, found]
    · rw [checkTEmptyUnconvertConvertId t tvs valid]
      exact tschemeApproxModelRefl 0 HolFiniteMapExact.holEmpty tvs t
  · refine ⟨rfl, rfl, ?_⟩
    intro id tvs t found
    have found' : (nsLookup ienv.infV id).map (fun entry => (entry.1, convertT entry.2)) = some (tvs, t) := by
      simpa [lookupVar, lookupVarEEmpty, ienvToTenvModel, nsLookup_nsMap] using found
    cases src : nsLookup ienv.infV id with
    | none => simp [src] at found'
    | some entry =>
      obtain ⟨n, ty⟩ := entry
      simp [src] at found'
      obtain ⟨rfl, rfl⟩ := found'
      have valid := valueOk id (n, ty) src
      refine ⟨⟨n, checkTToCheckFreevars n ty valid⟩, n, ty, rfl, ?_⟩
      rw [checkTEmptyUnconvertConvertId ty n valid]
      exact tschemeApproxModelRefl 0 HolFiniteMapExact.holEmpty n ty

/-- A well-formed declarative environment relates to its inference conversion;
    the relation is expanded one level to expose its fixed empty maps. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "env_rel_tenv_to_ienv"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem envRelTenvToIenv (tenv : TypeEnv) (h : tenvOk tenv) :
    ienvOk (fun _ => False) (tenvToIenv tenv) ∧ tenvOk tenv ∧
      (∀ path, nsLookupMod (tenvToIenv tenv).infV path = none ↔ nsLookupMod tenv.v path = none) ∧
      envRelSoundModel HolFiniteMapExact.holEmpty (tenvToIenv tenv) tenv .empty ∧
      envRelCompleteModel HolFiniteMapExact.holEmpty (tenvToIenv tenv) tenv .empty := by
  classical
  have decEq : Classical.typeDecidableEq Flapjack.Basis.Pure.MlString.MlString =
      Flapjack.Basis.Pure.MlString.instDecidableEqMlString := by
    funext a b
    exact Subsingleton.elim _ _
  have valueOk : tenvValOk tenv.v := h.1
  unfold tenvValOk nsAll at valueOk
  change ∀ id v, @nsLookup _ _ _ (Classical.typeDecidableEq _) (Classical.typeDecidableEq _)
    tenv.v id = some v → checkFreevars v.1 [] v.2 = true at valueOk
  rw [decEq] at valueOk
  refine ⟨?_, h, ?_, ?_, ?_⟩
  · refine ⟨?_, h.2.1, h.2.2⟩
    unfold ienvValOk
    change @nsAll _ _ _ (Classical.typeDecidableEq _) (Classical.typeDecidableEq _)
      (fun _ entry => checkT entry.1 (fun _ => False) entry.2)
      (nsMap (fun entry => (entry.1, unconvertT entry.2)) tenv.v)
    rw [decEq]
    change nsAll (fun _ entry => checkT entry.1 (fun _ => False) entry.2)
      (nsMap (fun entry => (entry.1, unconvertT entry.2)) tenv.v)
    rw [nsAll_nsMap]
    intro id entry found
    exact checkFreevarsToCheckT entry.2 entry.1 (valueOk id entry found)
  · intro path
    change nsLookupMod (nsMap (fun entry => (entry.1, unconvertT entry.2)) tenv.v) path = none ↔ _
    rw [nsLookupMod_nsMap]
    cases nsLookupMod tenv.v path <;> simp
  · refine ⟨rfl, rfl, ?_⟩
    intro id ts found
    change nsLookup (nsMap (fun entry => (entry.1, unconvertT entry.2)) tenv.v) id = some ts at found
    rw [nsLookup_nsMap] at found
    cases hn : nsLookup tenv.v id with
    | none => simp [hn] at found
    | some entry =>
      obtain ⟨n, t⟩ := entry
      simp [hn] at found
      subst ts
      have valid := valueOk id (n, t) hn
      refine ⟨n, t, ?_, ?_, ?_⟩
      · simpa [numTvs] using valid
      · simpa [lookupVar, lookupVarEEmpty] using hn
      · exact tschemeApproxModelRefl 0 HolFiniteMapExact.holEmpty n (unconvertT t)
  · refine ⟨rfl, rfl, ?_⟩
    intro id tvs t found
    have hn : nsLookup tenv.v id = some (tvs, t) := by
      simpa [lookupVar, lookupVarEEmpty] using found
    have valid := valueOk id (tvs, t) hn
    refine ⟨⟨tvs, valid⟩, tvs, unconvertT t, ?_, ?_⟩
    · change nsLookup (nsMap (fun entry => (entry.1, unconvertT entry.2)) tenv.v) id = _
      rw [nsLookup_nsMap, hn]
      rfl
    · exact tschemeApproxModelRefl 0 HolFiniteMapExact.holEmpty tvs (unconvertT t)

end Flapjack.Compiler.Inference.EnvRel
