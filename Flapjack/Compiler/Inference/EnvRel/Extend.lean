module

public import Flapjack.Compiler.Inference.EnvRel.Relation
public import Flapjack.Compiler.Inference.InferProps.Extend
public import Flapjack.TypeSysProps.Environment
public import Flapjack.NamespaceProps.Append

@[expose] public section

/-! Declaration extension preserves related environments. -/
namespace Flapjack.Compiler.Inference.EnvRel
open Flapjack.NamespaceHOL Flapjack.TypeSystemHOL Flapjack.TypeSoundInvariants
  Flapjack.Compiler.Inference.Infer Flapjack.Compiler.Inference.InferProps
  Flapjack.TypeSysProps

/-- Related environments have the same value and module lookup domains. -/
private theorem envRelDomains (tenv : TypeEnv) (ienv : Env) (h : envRelModel tenv ienv) :
    nsDom ienv.infV = nsDom tenv.v ∧ nsDomMod ienv.infV = nsDomMod tenv.v := by
  constructor
  · funext id
    apply propext
    change (∃ v, nsLookup ienv.infV id = some v) ↔ (∃ v, nsLookup tenv.v id = some v)
    constructor
    · rintro ⟨v, found⟩
      obtain ⟨n, t, _, lookup, _⟩ := h.2.2.2.1.2.2 id v found
      exact ⟨(n, t), by simpa [lookupVar, lookupVarEEmpty] using lookup⟩
    · rintro ⟨⟨n, t⟩, found⟩
      have lookup : lookupVar id .empty tenv = some (n, t) := by
        simpa [lookupVar, lookupVarEEmpty] using found
      obtain ⟨_, n', t', existsLookup, _⟩ := h.2.2.2.2.2.2 id n t lookup
      exact ⟨(n', t'), existsLookup⟩
  · funext path
    apply propext
    change (∃ e, nsLookupMod ienv.infV path = some e) ↔
      (∃ e, nsLookupMod tenv.v path = some e)
    have missing := h.2.2.1 path
    cases hi : nsLookupMod ienv.infV path <;> cases ht : nsLookupMod tenv.v path <;>
      simp_all

/-- Extension preserves the environment relation, unfolded one level to
    expose its fixed empty substitutions. -/
@[hol "cakeml/compiler/inference/proofs/envRelScript.sml" "env_rel_extend"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty])]
theorem envRelExtend (tenv1 : TypeEnv) (ienv1 : Env) (tenv2 : TypeEnv) (ienv2 : Env)
    (h : (ienvOk (fun _ => False) ienv1 ∧ tenvOk tenv1 ∧
        (∀ path, nsLookupMod ienv1.infV path = none ↔ nsLookupMod tenv1.v path = none) ∧
        envRelSoundModel HolFiniteMapExact.holEmpty ienv1 tenv1 .empty ∧
        envRelCompleteModel HolFiniteMapExact.holEmpty ienv1 tenv1 .empty) ∧
      (ienvOk (fun _ => False) ienv2 ∧ tenvOk tenv2 ∧
        (∀ path, nsLookupMod ienv2.infV path = none ↔ nsLookupMod tenv2.v path = none) ∧
        envRelSoundModel HolFiniteMapExact.holEmpty ienv2 tenv2 .empty ∧
        envRelCompleteModel HolFiniteMapExact.holEmpty ienv2 tenv2 .empty)) :
    ienvOk (fun _ => False) (extendDecIenv ienv1 ienv2) ∧
      tenvOk (extendDecTenv tenv1 tenv2) ∧
      (∀ path, nsLookupMod (extendDecIenv ienv1 ienv2).infV path = none ↔
        nsLookupMod (extendDecTenv tenv1 tenv2).v path = none) ∧
      envRelSoundModel HolFiniteMapExact.holEmpty (extendDecIenv ienv1 ienv2) (extendDecTenv tenv1 tenv2) .empty ∧
      envRelCompleteModel HolFiniteMapExact.holEmpty (extendDecIenv ienv1 ienv2) (extendDecTenv tenv1 tenv2) .empty := by
  change envRelModel tenv1 ienv1 ∧ envRelModel tenv2 ienv2 at h
  change envRelModel (extendDecTenv tenv1 tenv2) (extendDecIenv ienv1 ienv2)
  have d1 := envRelDomains tenv1 ienv1 h.1
  have d2 := envRelDomains tenv2 ienv2 h.2
  obtain ⟨_, moduleDomains⟩ := nsDom_nsAppend_equal ienv1.infV ienv2.infV tenv1.v tenv2.v
    ⟨d1.1, d2.1, d1.2, d2.2⟩
  refine ⟨ienvOkExtendDecIenv ienv1 ienv2 _ ⟨h.1.1, h.2.1⟩,
    extendDecTenvOk tenv1 tenv2 ⟨h.1.2.1, h.2.2.1⟩, ?_, ?_, ?_⟩
  · intro path
    have dm := congrFun moduleDomains path
    change (∃ e, nsLookupMod (nsAppend ienv1.infV ienv2.infV) path = some e) =
      (∃ e, nsLookupMod (nsAppend tenv1.v tenv2.v) path = some e) at dm
    change nsLookupMod (nsAppend ienv1.infV ienv2.infV) path = none ↔
      nsLookupMod (nsAppend tenv1.v tenv2.v) path = none
    cases hi : nsLookupMod (nsAppend ienv1.infV ienv2.infV) path <;>
      cases ht : nsLookupMod (nsAppend tenv1.v tenv2.v) path <;> simp_all
  · refine ⟨?_, ?_, ?_⟩
    · simp [extendDecIenv, extendDecTenv, h.1.2.2.2.1.1, h.2.2.2.2.1.1]
    · simp [extendDecIenv, extendDecTenv, h.1.2.2.2.1.2.1, h.2.2.2.2.1.2.1]
    · intro id ts found
      change nsLookup (nsAppend ienv1.infV ienv2.infV) id = some ts at found
      let rel : (Nat × InferT) → (Nat × SemanticT) → Prop := fun iv dv =>
        checkFreevars dv.1 [] dv.2 = true ∧
          tschemeApproxModel 0 HolFiniteMapExact.holEmpty iv (dv.1, unconvertT dv.2)
      have fromFirst : ∀ v, nsLookup ienv1.infV id = some v →
          ∃ w, nsLookup tenv1.v id = some w ∧ rel v w := by
        intro v hv
        obtain ⟨n, t, check, lookup, approx⟩ := h.1.2.2.2.1.2.2 id v hv
        exact ⟨(n, t), by simpa [lookupVar, lookupVarEEmpty] using lookup, by simpa [rel, numTvs] using And.intro check approx⟩
      have fromSecond : ∀ v, nsLookup ienv2.infV id = some v →
          ∃ w, nsLookup tenv2.v id = some w ∧ rel v w := by
        intro v hv
        obtain ⟨n, t, check, lookup, approx⟩ := h.2.2.2.2.1.2.2 id v hv
        exact ⟨(n, t), by simpa [lookupVar, lookupVarEEmpty] using lookup, by simpa [rel, numTvs] using And.intro check approx⟩
      obtain ⟨⟨n, t⟩, lookup, check, approx⟩ :=
        nsLookup_append_transfer tenv1.v tenv2.v ienv1.infV ienv2.infV d1.1.symm d1.2.symm id ts rel fromFirst fromSecond found
      exact ⟨n, t, by simpa [numTvs] using check,
        by simpa [lookupVar, lookupVarEEmpty, extendDecTenv] using lookup, approx⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp [extendDecIenv, extendDecTenv, h.1.2.2.2.2.1, h.2.2.2.2.2.1]
    · simp [extendDecIenv, extendDecTenv, h.1.2.2.2.2.2.1, h.2.2.2.2.2.2.1]
    · intro id tvs t found
      have lookup : nsLookup (nsAppend tenv1.v tenv2.v) id = some (tvs, t) := by
        simpa [lookupVar, lookupVarEEmpty, extendDecTenv] using found
      let rel : (Nat × SemanticT) → (Nat × InferT) → Prop := fun dv iv =>
        (∃ n, checkFreevars n [] dv.2 = true) ∧
          tschemeApproxModel 0 HolFiniteMapExact.holEmpty (dv.1, unconvertT dv.2) iv
      have fromFirst : ∀ v, nsLookup tenv1.v id = some v →
          ∃ w, nsLookup ienv1.infV id = some w ∧ rel v w := by
        intro ⟨n, ty⟩ hv
        have hv' : lookupVar id .empty tenv1 = some (n, ty) := by simpa [lookupVar, lookupVarEEmpty] using hv
        obtain ⟨check, n', t', found, approx⟩ := h.1.2.2.2.2.2.2 id n ty hv'
        exact ⟨(n', t'), found, by simpa [rel, numTvs] using And.intro check approx⟩
      have fromSecond : ∀ v, nsLookup tenv2.v id = some v →
          ∃ w, nsLookup ienv2.infV id = some w ∧ rel v w := by
        intro ⟨n, ty⟩ hv
        have hv' : lookupVar id .empty tenv2 = some (n, ty) := by simpa [lookupVar, lookupVarEEmpty] using hv
        obtain ⟨check, n', t', found, approx⟩ := h.2.2.2.2.2.2.2 id n ty hv'
        exact ⟨(n', t'), found, by simpa [rel, numTvs] using And.intro check approx⟩
      obtain ⟨⟨n, ty⟩, found', check, approx⟩ :=
        nsLookup_append_transfer ienv1.infV ienv2.infV tenv1.v tenv2.v d1.1 d1.2 id (tvs, t) rel fromFirst fromSecond lookup
      exact ⟨check, n, ty, by simpa [extendDecIenv] using found', approx⟩

end Flapjack.Compiler.Inference.EnvRel
