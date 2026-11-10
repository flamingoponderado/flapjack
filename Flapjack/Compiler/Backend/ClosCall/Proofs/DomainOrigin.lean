module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.InsertDomain
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Suffix
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Misc.Sptree.Subspt

@[expose] public section

/-! Origins of locations added by direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang

private def DomainGrows (s t : State) : Prop :=
  s.2 <:+ t.2 ∧ ∀ loc, sptDomain t.1 loc →
    sptDomain s.1 loc ∨ ∃ label ∈ t.2.map Prod.fst, loc = Nat.pred label

private theorem refl (s : State) : DomainGrows s s :=
  ⟨List.suffix_refl _, fun _ h => Or.inl h⟩

private theorem trans {s t u : State} (h : DomainGrows s t) (h' : DomainGrows t u) : DomainGrows s u := by
  refine ⟨h.1.trans h'.1, ?_⟩
  intro loc present
  rcases h'.2 loc present with middle | new
  · rcases h.2 loc middle with old | ⟨label, member, eq⟩
    · exact Or.inl old
    · right
      obtain ⟨added, appendEq⟩ := h'.1
      refine ⟨label, ?_, eq⟩
      rw [← appendEq, List.map_append]
      exact List.mem_append_right _ member
  · exact Or.inr new

mutual
private theorem growth_expr (e : Exp) (s : State) :
    DomainGrows s (callsSing e s).2 := by
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
      · have oldSuffix : s.2 <:+ st.2 := by
          simpa [fresh, insertEach_snd] using ih.1
        refine ⟨oldSuffix.trans (List.suffix_cons _ _), ?_⟩
        intro x present
        rcases ih.2 x present with initial | ⟨label, member, eq⟩
        · dsimp [fresh] at initial
          rw [domain_insertEach] at initial
          rcases initial with generated | old
          · right
            simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_range] at generated
            obtain ⟨i, bound, equal⟩ := generated
            refine ⟨loc.getD 0 + 1, ?_, ?_⟩
            · simp
            · simp only [Nat.add_one, Nat.pred_succ]
              omega
          · exact Or.inl old
        · right
          refine ⟨label, ?_, eq⟩
          simp only [List.map_cons, List.mem_cons]
          exact Or.inr member
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
        have emitGrowth : DomainGrows s emitted := by
          have oldSuffix : s.2 <:+ st.2 := by
            simpa [fresh, insertEach_snd] using ihF.1
          refine ⟨oldSuffix.trans (codeListSource_suffix _ _ _), ?_⟩
          intro x present
          have stPresent : sptDomain st.1 x := by
            simpa [emitted, codeListSource_fst] using present
          rcases ihF.2 x stPresent with initial | ⟨label, member, eq⟩
          · dsimp [fresh] at initial
            rw [domain_insertEach] at initial
            rcases initial with generated | old
            · right
              simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_range] at generated
              obtain ⟨i, bound, equal⟩ := generated
              have len := callsSingList_length (fns.map Prod.snd) (insertEachSource (loc.getD 0) fns.length s)
              rw [hf] at len
              simp only [List.length_map] at len
              have zipBound : i < ((fns.map Prod.fst).zip bodies).length := by
                simp only [List.length_zip, List.length_map]
                omega
              refine ⟨loc.getD 0 + 2 * i + 1, ?_, ?_⟩
              · simp only [emitted, codeListSource_labels, List.mem_append, List.mem_reverse,
                  List.mem_map, List.mem_range]
                left
                exact ⟨i, zipBound, by omega⟩
              · simp only [Nat.add_one, Nat.pred_succ]
                omega
            · exact Or.inl old
          · right
            refine ⟨label, ?_, eq⟩
            simp only [emitted, codeListSource_labels, List.mem_append, List.mem_reverse]
            exact Or.inr member
        have ihBody := growth_expr body emitted
        cases hb : callsSing body emitted with
        | mk out final =>
          simp only [hb] at ihBody
          change DomainGrows s final
          exact trans emitGrowth ihBody
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
    DomainGrows s (callsSingList es s).2 := by
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


/-- Every final location was initially known or is the predecessor of an
emitted auxiliary label. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_domain"]
theorem calls_domain (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g)) :
    Set.Subset (sptDomain g.1) (Set.union (sptDomain g0.1)
      (Set.image Nat.pred { label | label ∈ g.2.map Prod.fst })) := by
  have growth := growth_list xs g0
  change callsSingList xs g0 = (ys, g) at h
  rw [h] at growth
  intro loc present
  rcases growth.2 loc present with old | ⟨label, member, eq⟩
  · exact Or.inl old
  · exact Or.inr ⟨label, member, eq.symm⟩

end Flapjack.Compiler.Backend.ClosCall
