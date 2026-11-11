module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateSyntax
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StubInvariants
public import Flapjack.Compiler.Backend.ClosCall.Compile

@[expose] public section

/-! Direct-call preservation of application-arity bounds. -/

namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

mutual
/-- Flapjack structural induction for the application bound on a singleton traversal. -/
private theorem aritySingle (limit : Nat) (e : Exp) (s : State)
    (h : obeysMaxApp limit e ∧ stateSyntax (obeysMaxApp limit) s) :
    obeysMaxApp limit (callsSing e s).1 ∧ stateSyntax (obeysMaxApp limit) (callsSing e s).2 := by
  cases e with
  | var tr n => simpa [callsSing, obeysMaxApp] using h.2
  | raise tr body | tick tr body =>
    have ih := aritySingle limit body s ⟨by simpa [obeysMaxApp] using h.1, h.2⟩
    cases hr : callsSing body s with
    | mk out st => simpa [callsSing, hr, obeysMaxApp] using ih
  | ifThenElse tr a b c =>
    simp only [obeysMaxApp] at h
    cases ha : callsSing a s with
    | mk oa sa =>
      have h1 := aritySingle limit a s ⟨h.1.1, h.2⟩
      simp only [ha] at h1
      cases hb : callsSing b sa with
      | mk ob sb =>
        have h2 := aritySingle limit b sa ⟨h.1.2.1, h1.2⟩
        simp only [hb] at h2
        cases hc : callsSing c sb with
        | mk oc sc =>
          have h3 := aritySingle limit c sb ⟨h.1.2.2, h2.2⟩
          simp only [hc] at h3
          simpa [callsSing, ha, hb, hc, obeysMaxApp] using
            And.intro (And.intro h1.1 (And.intro h2.1 h3.1)) h3.2
  | «let» tr args body =>
    simp only [obeysMaxApp] at h
    cases ha : callsSingList args s with
    | mk oa sa =>
      have h1 := arityMany limit args s ⟨h.1.1, h.2⟩
      simp only [ha] at h1
      cases hb : callsSing body sa with
      | mk ob sb =>
        have h2 := aritySingle limit body sa ⟨h.1.2, h1.2⟩
        simp only [hb] at h2
        simpa [callsSing, ha, hb, obeysMaxApp] using And.intro (And.intro h1.1 h2.1) h2.2
  | handle tr body handler =>
    simp only [obeysMaxApp] at h
    cases ha : callsSing body s with
    | mk oa sa =>
      have h1 := aritySingle limit body s ⟨h.1.1, h.2⟩
      simp only [ha] at h1
      cases hb : callsSing handler sa with
      | mk ob sb =>
        have h2 := aritySingle limit handler sa ⟨h.1.2, h1.2⟩
        simp only [hb] at h2
        simpa [callsSing, ha, hb, obeysMaxApp] using And.intro (And.intro h1.1 h2.1) h2.2
  | call tr ticks dest args | op tr dest args =>
    have ih := arityMany limit args s ⟨by simpa [obeysMaxApp] using h.1, h.2⟩
    cases hr : callsSingList args s with
    | mk out st => simpa [callsSing, hr, obeysMaxApp] using ih
  | app tr loc body args =>
    simp only [obeysMaxApp] at h
    cases ha : callsSingList args s with
    | mk oa sa =>
      have h1 := arityMany limit args s ⟨h.1.2.2, h.2⟩
      simp only [ha] at h1
      have hlen : oa.length = args.length := by
        have len := callsSingList_length args s
        simpa [ha] using len
      have hbound : oa.length ≤ limit := by simpa [hlen] using h.1.1
      cases hb : callsSing body sa with
      | mk ob sb =>
        have h2 := aritySingle limit body sa ⟨h.1.2.1, h1.2⟩
        simp only [hb] at h2
        simp only [callsSing, ha, hb]
        cases loc with
        | none => simpa [obeysMaxApp] using And.intro (And.intro hbound (And.intro h2.1 h1.1)) h2.2
        | some loc =>
          have hv := obeysMaxApp_variables limit BackendCommon.Tra.none 2 oa.length
          cases hl : (sptLookup loc sb.1).isSome <;> cases hp : ClosLang.pure body <;>
            simp_all [obeysMaxApp, obeysMaxAppList_iff, or_imp]
  | fn name loc vs arity body =>
    simp only [obeysMaxApp] at h
    let fresh := insertEachSource (loc.getD 0) 1 s
    have haux : stateSyntax (obeysMaxApp limit) fresh := by
      simpa [fresh, stateSyntax_insertEach] using h.2
    cases hf : callsSing body fresh with
    | mk out st =>
      have ih := aritySingle limit body fresh ⟨h.1, haux⟩
      simp only [hf] at ih
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · have hv := obeysMaxApp_variables limit BackendCommon.Tra.none 1 arity
        simpa [obeysMaxApp, obeysMaxAppList_iff, stateSyntax] using And.intro hv ih
      · cases hr : callsSing body s with
        | mk out st =>
          have ih := aritySingle limit body s ⟨h.1, h.2⟩
          simp only [hr] at ih
          simpa [hr, obeysMaxApp] using ih
  | letrec names loc vs fns body =>
    simp only [obeysMaxApp, obeysMaxAppFuns_eq_map] at h
    let fresh := insertEachSource (loc.getD 0) fns.length s
    have haux : stateSyntax (obeysMaxApp limit) fresh := by
      simpa [fresh, stateSyntax_insertEach] using h.2
    cases hf : callsSingList (fns.map Prod.snd) fresh with
    | mk bodies st =>
      have ihF := arityMany limit (fns.map Prod.snd) fresh ⟨h.1.1, haux⟩
      simp only [hf] at ihF
      have hlen : bodies.length = fns.length := by
        have len := callsSingList_length (fns.map Prod.snd) fresh
        simpa [hf] using len
      have hzip : ((fns.map Prod.fst).zip bodies).map Prod.snd = bodies := by
        simp [List.map_snd_zip, hlen]
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · have hcode : stateSyntax (obeysMaxApp limit)
            (codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) st) := by
          apply (stateSyntax_codeList (obeysMaxApp limit) _ _ _).2
          exact ⟨ihF.2, by rw [hzip]; exact (obeysMaxAppList_iff limit _).mp ihF.1⟩
        cases hb : callsSing body
            (codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) st) with
        | mk out final =>
          have ihB := aritySingle limit body _ ⟨h.1.2, hcode⟩
          simp only [hb] at ihB
          have stubs := obeysMaxApp_callsList limit BackendCommon.Tra.none 1 (loc.getD 0) fns
          have hstubs := (obeysMaxAppList_iff limit _).mpr stubs
          simp [obeysMaxApp, obeysMaxAppFuns_eq_map, hstubs, ihB.1, ihB.2]
      · cases hg : callsSingList (fns.map Prod.snd) s with
        | mk bodies st =>
          have ihG := arityMany limit (fns.map Prod.snd) s ⟨h.1.1, h.2⟩
          simp only [hg] at ihG
          have hlen : bodies.length = fns.length := by
            have len := callsSingList_length (fns.map Prod.snd) s
            simpa [hg] using len
          have hzip : ((fns.map Prod.fst).zip bodies).map Prod.snd = bodies := by
            simp [List.map_snd_zip, hlen]
          cases hb : callsSing body st with
          | mk out final =>
            have ihB := aritySingle limit body st ⟨h.1.2, ihG.2⟩
            simp only [hb] at ihB
            simp [obeysMaxApp, obeysMaxAppFuns_eq_map, hzip, ihG.1, ihB.1, ihB.2]
termination_by sizeOf e
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  all_goals try have bound := sizeOf_map_snd_le fns
  all_goals omega

/-- Flapjack structural induction for the application bound on a list traversal. -/
private theorem arityMany (limit : Nat) (es : List Exp) (s : State)
    (h : obeysMaxAppList limit es ∧ stateSyntax (obeysMaxApp limit) s) :
    obeysMaxAppList limit (callsSingList es s).1 ∧ stateSyntax (obeysMaxApp limit) (callsSingList es s).2 := by
  cases es with
  | nil => simpa [callsSingList, obeysMaxAppList] using h.2
  | cons e es =>
    simp only [obeysMaxAppList] at h
    cases he : callsSing e s with
    | mk out mid =>
      cases hs : callsSingList es mid with
      | mk outs final =>
        have h1 := aritySingle limit e s ⟨h.1.1, h.2⟩
        have h2 := arityMany limit es mid ⟨h.1.2, by simpa [he] using h1.2⟩
        simpa [callsSingList, he, hs, obeysMaxAppList] using
          And.intro (And.intro (by simpa [he] using h1.1) (by simpa [hs] using h2.1))
            (by simpa [hs] using h2.2)
termination_by sizeOf es
decreasing_by all_goals subst_vars; all_goals simp_wf <;> omega
end


/-- Direct-call conversion preserves application bounds in output and code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_obeys_max_app"]
theorem callsObeysMaxApp (limit : Nat) (xs : List Exp) (g : State) (ys : List Exp) (g1 : State)
    (run : calls xs g = (ys, g1)) (hstate : stateSyntax (obeysMaxApp limit) g)
    (hxs : ∀ e ∈ xs, obeysMaxApp limit e) :
    (∀ e ∈ ys, obeysMaxApp limit e) ∧ stateSyntax (obeysMaxApp limit) g1 := by
  have result := arityMany limit xs g ⟨(obeysMaxAppList_iff limit _).mpr hxs, hstate⟩
  change callsSingList xs g = (ys, g1) at run
  rw [run] at result
  exact ⟨(obeysMaxAppList_iff limit _).mp result.1, result.2⟩

end Flapjack.Compiler.Backend.ClosCall
