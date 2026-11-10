module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.InsertDomain
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeList
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Misc.Sptree.Subspt

@[expose] public section

/-! Preservation of known locations by direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang

private theorem sizeOf_map_snd_le (xs : List (Nat × Exp)) :
    sizeOf (xs.map Prod.snd) ≤ sizeOf xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases x; simp_wf; omega

private theorem refl (s : State) : sptSubspt s.1 s.1 :=
  fun _ h => ⟨h, rfl⟩

private theorem trans {s t u : State} (h : sptSubspt s.1 t.1)
    (h' : sptSubspt t.1 u.1) : sptSubspt s.1 u.1 :=
  sptSubsptTrans _ _ _ ⟨h, h'⟩

mutual
private theorem growth_expr (e : Exp) (s : State) :
    sptSubspt s.1 (callsSing e s).2.1 := by
  cases e with
  | var tr n => simpa [callsSing] using refl s
  | raise tr e | tick tr e =>
    have ih := growth_expr e s
    cases run : callsSing e s with
    | mk out next => simpa [callsSing, run] using ih
  | ifThenElse tr x y z =>
    cases hx : callsSing x s with
    | mk ox sx =>
      cases hy : callsSing y sx with
      | mk oy sy =>
        cases hz : callsSing z sy with
        | mk oz sz =>
          have h₁ := growth_expr x s
          have h₂ := growth_expr y sx
          have h₃ := growth_expr z sy
          simp only [hx] at h₁
          simp only [hy] at h₂
          simp only [hz] at h₃
          simpa [callsSing, hx, hy, hz] using trans (trans h₁ h₂) h₃
  | «let» tr args body =>
    cases hx : callsSingList args s with
    | mk ox sx =>
      cases hy : callsSing body sx with
      | mk oy sy =>
        have h₁ := growth_list args s
        have h₂ := growth_expr body sx
        simp only [hx] at h₁
        simp only [hy] at h₂
        simpa [callsSing, hx, hy] using trans h₁ h₂
  | handle tr x y =>
    cases hx : callsSing x s with
    | mk ox sx =>
      cases hy : callsSing y sx with
      | mk oy sy =>
        have h₁ := growth_expr x s
        have h₂ := growth_expr y sx
        simp only [hx] at h₁
        simp only [hy] at h₂
        simpa [callsSing, hx, hy] using trans h₁ h₂
  | call tr ticks dest args | op tr dest args =>
    have ih := growth_list args s
    cases run : callsSingList args s with
    | mk out next => simpa [callsSing, run] using ih
  | app tr loc body args =>
    cases hx : callsSingList args s with
    | mk ox sx =>
      cases hy : callsSing body sx with
      | mk oy sy =>
        have h₁ := growth_list args s
        have h₂ := growth_expr body sx
        simp only [hx] at h₁
        simp only [hy] at h₂
        have combined := trans h₁ h₂
        cases loc with
        | none => simpa [callsSing, hx, hy] using combined
        | some loc =>
          simp only [callsSing, hx, hy]
          cases (sptLookup loc sy.1).isSome <;> cases ClosLang.pure body <;>
            simpa using combined
  | fn name loc vars arity body =>
    let fresh := insertEachSource (loc.getD 0) 1 s
    cases hf : callsSing body fresh with
    | mk out st =>
      have ih := growth_expr body fresh
      simp only [hf] at ih
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · exact trans (insertEach_subspt _ _ s) ih
      · have ih := growth_expr body s
        cases hr : callsSing body s with
        | mk out next => simpa [hr] using ih
  | letrec names loc vars fns body =>
    let fresh := insertEachSource (loc.getD 0) fns.length s
    cases hf : callsSingList (fns.map Prod.snd) fresh with
    | mk bodies st =>
      have ihF := growth_list (fns.map Prod.snd) fresh
      simp only [hf] at ihF
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · let emitted := codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) st
        have emitGrowth : sptSubspt st.1 emitted.1 := by
          simpa [emitted, codeListSource_fst] using refl st
        have ihBody := growth_expr body emitted
        cases hb : callsSing body emitted with
        | mk out final =>
          simp only [hb] at ihBody
          change sptSubspt s.1 final.1
          exact trans (trans (trans (insertEach_subspt _ _ s) ihF) emitGrowth) ihBody
      · cases hg : callsSingList (fns.map Prod.snd) s with
        | mk bodies st =>
          have ihG := growth_list (fns.map Prod.snd) s
          simp only [hg] at ihG ⊢
          cases hb : callsSing body st with
          | mk out final =>
            have ihBody := growth_expr body st
            simp only [hb] at ihBody ⊢
            exact trans ihG ihBody
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have bound := sizeOf_map_snd_le fns
  all_goals omega

private theorem growth_list (es : List Exp) (s : State) :
    sptSubspt s.1 (callsSingList es s).2.1 := by
  cases es with
  | nil => simpa [callsSingList] using refl s
  | cons e es =>
    cases he : callsSing e s with
    | mk out mid =>
      cases hs : callsSingList es mid with
      | mk outs final =>
        have h₁ := growth_expr e s
        have h₂ := growth_list es mid
        simp only [he] at h₁
        simp only [hs] at h₂
        simpa [callsSingList, he, hs] using trans h₁ h₂
termination_by sizeOf es
decreasing_by all_goals simp_wf <;> omega
end

/-- Direct-call conversion preserves all previously known locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_subspt"]
theorem calls_subspt (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g)) : sptSubspt g0.1 g.1 := by
  have result := growth_list xs g0
  change callsSingList xs g0 = (ys, g) at h
  simpa [h] using result

end Flapjack.Compiler.Backend.ClosCall
