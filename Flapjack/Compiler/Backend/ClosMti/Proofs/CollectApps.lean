import Flapjack.Compiler.Backend.ClosMti.Proofs.CollectArgs

/-! Source-shaped application collection invariants for the multi-argument pass. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang

/-- Rebuild unary applications in the source's argument order. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "mk_Apps_def"]
def mkApps (e : Exp) : List (BackendCommon.Tra × Exp) → Exp
  | [] => e
  | (t, arg) :: ts => .app t none (mkApps e ts) [arg]

/-- The collector preserves its initial argument prefix. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_apps_acc"]
theorem collectAppsPrefix (maxApp : Nat) (acc : List Exp) (e : Exp) (result : List Exp) (rest : Exp)
    (run : collectApps maxApp acc e = (result, rest)) : ∃ other, result = acc ++ other := by
  fun_induction collectApps maxApp acc e <;> simp_all
  case case1 =>
    rename_i initial trace body args step ih
    obtain ⟨other, eq⟩ := ih
    exact ⟨args ++ other, by simpa [List.append_assoc] using eq⟩

/-- Collecting applications preserves the pre-multi-argument invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_apps_no_mti"]
theorem collectAppsNoMti (maxApp : Nat) (acc : List Exp) (e : Exp) (result : List Exp) (rest : Exp)
    (run : collectApps maxApp acc e = (result, rest)) (safe : ClosProps.noMti e)
    (accSafe : ∀ x ∈ acc, ClosProps.noMti x) :
    (∀ x ∈ result, ClosProps.noMti x) ∧ ClosProps.noMti rest := by
  fun_induction collectApps maxApp acc e
  case case1 =>
    rename_i initial trace body more step ih
    simp only [ClosProps.noMti] at safe
    apply ih run safe.2.2.2
    intro x member
    rcases List.mem_append.mp member with left | right
    · exact accSafe x left
    · exact (ClosProps.noMtiList_iff more).mp safe.2.2.1 x right
  all_goals simp_all

/-- Prefixing the accumulator and increasing its limit by the prefix length
preserves every collector decision and prefixes the resulting arguments. -/
theorem collectAppsPrepend (e : Exp) (maxApp : Nat) (before acc : List Exp) :
    collectApps (maxApp + before.length) (before ++ acc) e =
      let (result, rest) := collectApps maxApp acc e
      (before ++ result, rest) := by
  cases e with
  | app t loc body more =>
    cases loc with
    | some loc => simp [collectApps]
    | none =>
      by_cases fits : acc.length + more.length ≤ maxApp
      · have fits' : (before ++ acc).length + more.length ≤ maxApp + before.length := by
          simp only [List.length_append]; omega
        simp only [collectApps, fits, fits', ite_true]
        simpa [List.append_assoc] using collectAppsPrepend body maxApp before (acc ++ more)
      · have fails' : ¬ before.length + acc.length + more.length ≤ maxApp + before.length := by
          omega
        simp [collectApps, fits, fails']
  | _ => simp [collectApps]
termination_by sizeOf e

/-- Removing an initial accumulator preserves the corresponding output suffix. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_apps_cons_lemma"]
theorem collectAppsConsLemma (e : Exp) (m : Nat) (ys other : List Exp) (rest : Exp) :
    collectApps (m + ys.length) ys e = (ys ++ other, rest) ↔
      collectApps m [] e = (other, rest) := by
  have h := collectAppsPrepend e m ys []
  simp only [List.append_nil] at h
  rw [h]
  cases run : collectApps m [] e with
  | mk result final => simp

/-- A nonzero limit allows an existing leading argument to be removed. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_apps_cons"]
theorem collectAppsCons (e : Exp) (m : Nat) (x : Exp) (other : List Exp) (rest : Exp)
    (run : collectApps m [x] e = (x :: other, rest)) (positive : m ≠ 0) :
    collectApps (m - 1) [] e = (other, rest) := by
  apply (collectAppsConsLemma e (m - 1) [x] other rest).mp
  have mEq : m - 1 + 1 = m := by omega
  simpa [mEq] using run

/-- On unary source syntax, collected arguments reconstruct the original
nested applications and respect the configured application limit. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "collect_apps_IMP_mk_Apps"]
theorem collectAppsRebuild (e : Exp) (maxApp : Nat) (_acc other : List Exp) (rest : Exp)
    (run : collectApps maxApp [] e = (other, rest)) (safe : ClosProps.noMti e) :
    ∃ ts : List BackendCommon.Tra,
      e = mkApps rest (ts.zip other) ∧ other.length = ts.length ∧ other.length ≤ maxApp := by
  cases e with
  | app t loc body args =>
    simp only [ClosProps.noMti] at safe
    obtain ⟨arity, locEq, _, bodySafe⟩ := safe
    subst loc
    cases args with
    | nil => simp at arity
    | cons x xs =>
      cases xs with
      | cons y ys => simp at arity
      | nil =>
        by_cases zero : maxApp = 0
        · subst maxApp
          simp [collectApps] at run
          obtain ⟨rfl, rfl⟩ := run
          exact ⟨[], by simp [mkApps]⟩
        · have positive : 1 ≤ maxApp := by omega
          have inner : collectApps maxApp [x] body = (other, rest) := by
            simpa [collectApps, positive] using run
          obtain ⟨suffix, eq⟩ := collectAppsPrefix maxApp [x] body other rest inner
          subst other
          have smaller := collectAppsCons body maxApp x suffix rest inner zero
          obtain ⟨ts, bodyEq, lengthEq, limit⟩ :=
            collectAppsRebuild body (maxApp - 1) [] suffix rest smaller bodySafe
          refine ⟨t :: ts, ?_, ?_, ?_⟩
          · simp [mkApps, bodyEq]
          · simp only [List.singleton_append, List.length_cons]; omega
          · simp only [List.singleton_append, List.length_cons]; omega
  | _ =>
    simp [collectApps] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨[], by simp [mkApps]⟩
termination_by sizeOf e

end Flapjack.Compiler.Backend.ClosMti
