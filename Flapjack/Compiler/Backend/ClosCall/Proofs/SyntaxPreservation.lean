module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateSyntax
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StubInvariants
public import Flapjack.Compiler.Backend.ClosCall.Compile

@[expose] public section

/-! Direct-call preservation of closure syntax. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

mutual
/-- Flapjack structural induction over the executed singleton traversal. -/
private theorem noLabelsSingle (e : Exp) (s : State)
    (h : noLabels e ∧ stateSyntax noLabels s) :
    noLabels (callsSing e s).1 ∧ stateSyntax noLabels (callsSing e s).2 := by
  cases e with
  | var tr n => simpa [callsSing, noLabels] using h.2
  | raise tr body | tick tr body =>
    have ih := noLabelsSingle body s ⟨by simpa [noLabels] using h.1, h.2⟩
    cases hr : callsSing body s with
    | mk out st => simpa [callsSing, hr, noLabels] using ih
  | ifThenElse tr a b c =>
    simp only [noLabels] at h
    cases ha : callsSing a s with
    | mk oa sa =>
      have h1 := noLabelsSingle a s ⟨h.1.1, h.2⟩
      simp only [ha] at h1
      cases hb : callsSing b sa with
      | mk ob sb =>
        have h2 := noLabelsSingle b sa ⟨h.1.2.1, h1.2⟩
        simp only [hb] at h2
        cases hc : callsSing c sb with
        | mk oc sc =>
          have h3 := noLabelsSingle c sb ⟨h.1.2.2, h2.2⟩
          simp only [hc] at h3
          simpa [callsSing, ha, hb, hc, noLabels] using
            And.intro (And.intro h1.1 (And.intro h2.1 h3.1)) h3.2
  | «let» tr args body =>
    simp only [noLabels] at h
    cases ha : callsSingList args s with
    | mk oa sa =>
      have h1 := noLabelsMany args s ⟨h.1.1, h.2⟩
      simp only [ha] at h1
      cases hb : callsSing body sa with
      | mk ob sb =>
        have h2 := noLabelsSingle body sa ⟨h.1.2, h1.2⟩
        simp only [hb] at h2
        simpa [callsSing, ha, hb, noLabels] using And.intro (And.intro h1.1 h2.1) h2.2
  | handle tr body handler =>
    simp only [noLabels] at h
    cases ha : callsSing body s with
    | mk oa sa =>
      have h1 := noLabelsSingle body s ⟨h.1.1, h.2⟩
      simp only [ha] at h1
      cases hb : callsSing handler sa with
      | mk ob sb =>
        have h2 := noLabelsSingle handler sa ⟨h.1.2, h1.2⟩
        simp only [hb] at h2
        simpa [callsSing, ha, hb, noLabels] using And.intro (And.intro h1.1 h2.1) h2.2
  | call tr ticks dest args =>
    have ih := noLabelsMany args s ⟨by simpa [noLabels] using h.1, h.2⟩
    cases hr : callsSingList args s with
    | mk out st => simpa [callsSing, hr, noLabels] using ih
  | op tr op args =>
    simp only [noLabels] at h
    have ih := noLabelsMany args s ⟨h.1.2, h.2⟩
    cases hr : callsSingList args s with
    | mk out st =>
      simp only [hr] at ih
      simpa [callsSing, hr, noLabels, h.1.1] using ih
  | app tr loc body args =>
    simp only [noLabels] at h
    cases ha : callsSingList args s with
    | mk oa sa =>
      have h1 := noLabelsMany args s ⟨h.1.2, h.2⟩
      simp only [ha] at h1
      cases hb : callsSing body sa with
      | mk ob sb =>
        have h2 := noLabelsSingle body sa ⟨h.1.1, h1.2⟩
        simp only [hb] at h2
        simp only [callsSing, ha, hb]
        cases loc with
        | none => simpa [noLabels] using And.intro (And.intro h2.1 h1.1) h2.2
        | some loc =>
          have hv := noLabels_variables BackendCommon.Tra.none 2 oa.length
          cases hl : (sptLookup loc sb.1).isSome <;> cases hp : ClosLang.pure body <;>
            simp_all [noLabels, noLabelsList_iff, or_imp]
  | fn name loc vs arity body =>
    simp only [noLabels] at h
    let fresh := insertEachSource (loc.getD 0) 1 s
    have haux : stateSyntax noLabels fresh := by
      simpa [fresh, stateSyntax_insertEach] using h.2
    cases hf : callsSing body fresh with
    | mk out st =>
      have ih := noLabelsSingle body fresh ⟨h.1, haux⟩
      simp only [hf] at ih
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · have hv := noLabels_variables BackendCommon.Tra.none 1 arity
        simpa [noLabels, noLabelsList_iff, stateSyntax] using And.intro hv ih
      · cases hr : callsSing body s with
        | mk out st =>
          have ih := noLabelsSingle body s ⟨h.1, h.2⟩
          simp only [hr] at ih
          simpa [hr, noLabels] using ih
  | letrec names loc vs fns body =>
    simp only [noLabels, noLabelsFuns_eq_map] at h
    let fresh := insertEachSource (loc.getD 0) fns.length s
    have haux : stateSyntax noLabels fresh := by
      simpa [fresh, stateSyntax_insertEach] using h.2
    cases hf : callsSingList (fns.map Prod.snd) fresh with
    | mk bodies st =>
      have ihF := noLabelsMany (fns.map Prod.snd) fresh ⟨h.1.1, haux⟩
      simp only [hf] at ihF
      have hlen : bodies.length = fns.length := by
        have len := callsSingList_length (fns.map Prod.snd) fresh
        simpa [hf] using len
      have hzip : ((fns.map Prod.fst).zip bodies).map Prod.snd = bodies := by
        simp [List.map_snd_zip, hlen]
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · have hcode : stateSyntax noLabels
            (codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) st) := by
          apply (stateSyntax_codeList noLabels _ _ _).2
          exact ⟨ihF.2, by rw [hzip]; exact (noLabelsList_iff _).mp ihF.1⟩
        cases hb : callsSing body
            (codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) st) with
        | mk out final =>
          have ihB := noLabelsSingle body _ ⟨h.1.2, hcode⟩
          simp only [hb] at ihB
          have stubs := noLabels_callsList BackendCommon.Tra.none 1 (loc.getD 0) fns
          have hstubs := (noLabelsList_iff _).mpr stubs
          simp [noLabels, noLabelsFuns_eq_map, hstubs, ihB.1, ihB.2]
      · cases hg : callsSingList (fns.map Prod.snd) s with
        | mk bodies st =>
          have ihG := noLabelsMany (fns.map Prod.snd) s ⟨h.1.1, h.2⟩
          simp only [hg] at ihG
          have hlen : bodies.length = fns.length := by
            have len := callsSingList_length (fns.map Prod.snd) s
            simpa [hg] using len
          have hzip : ((fns.map Prod.fst).zip bodies).map Prod.snd = bodies := by
            simp [List.map_snd_zip, hlen]
          cases hb : callsSing body st with
          | mk out final =>
            have ihB := noLabelsSingle body st ⟨h.1.2, ihG.2⟩
            simp only [hb] at ihB
            simp [noLabels, noLabelsFuns_eq_map, hzip, ihG.1, ihB.1, ihB.2]
termination_by sizeOf e
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  all_goals try have bound := sizeOf_map_snd_le fns
  all_goals omega

/-- Flapjack structural induction over the executed list traversal. -/
private theorem noLabelsMany (es : List Exp) (s : State)
    (h : noLabelsList es ∧ stateSyntax noLabels s) :
    noLabelsList (callsSingList es s).1 ∧ stateSyntax noLabels (callsSingList es s).2 := by
  cases es with
  | nil => simpa [callsSingList, noLabelsList] using h.2
  | cons e es =>
    simp only [noLabelsList] at h
    cases he : callsSing e s with
    | mk out mid =>
      cases hs : callsSingList es mid with
      | mk outs final =>
        have h1 := noLabelsSingle e s ⟨h.1.1, h.2⟩
        have h2 := noLabelsMany es mid ⟨h.1.2, by simpa [he] using h1.2⟩
        simpa [callsSingList, he, hs, noLabelsList] using
          And.intro (And.intro (by simpa [he] using h1.1) (by simpa [hs] using h2.1))
            (by simpa [hs] using h2.2)
termination_by sizeOf es
decreasing_by all_goals subst_vars; all_goals simp_wf <;> omega
end

/-- Direct-call conversion preserves label absence in output and accumulated code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_no_Labels"]
theorem callsNoLabels (xs : List Exp) (g : State) (ys : List Exp) (g1 : State)
    (run : calls xs g = (ys, g1)) (hstate : stateSyntax noLabels g)
    (hxs : ∀ e ∈ xs, noLabels e) :
    (∀ e ∈ ys, noLabels e) ∧ stateSyntax noLabels g1 := by
  have result := noLabelsMany xs g ⟨(noLabelsList_iff _).mpr hxs, hstate⟩
  change callsSingList xs g = (ys, g1) at run
  rw [run] at result
  exact ⟨(noLabelsList_iff _).mp result.1, result.2⟩

end Flapjack.Compiler.Backend.ClosCall
