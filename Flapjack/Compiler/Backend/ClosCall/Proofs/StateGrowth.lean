module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.InsertDomain
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Suffix
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Misc.Sptree.Subspt

@[expose] public section

/-! Preservation of known locations by direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang

private def Grows (s t : State) : Prop :=
  sptSubspt s.1 t.1 ∧ s.2 <:+ t.2 ∧
    ∀ label ∈ t.2.map Prod.fst,
      (∃ loc, sptDomain t.1 loc ∧ label = Nat.succ loc) ∨ label ∈ s.2.map Prod.fst

private theorem refl (s : State) : Grows s s :=
  ⟨fun _ h => ⟨h, rfl⟩, List.suffix_refl _, fun _ h => Or.inr h⟩

private theorem trans {s t u : State} (h : Grows s t) (h' : Grows t u) : Grows s u := by
  refine ⟨sptSubsptTrans _ _ _ ⟨h.1, h'.1⟩, h.2.1.trans h'.2.1, ?_⟩
  intro label member
  rcases h'.2.2 label member with new | middle
  · exact Or.inl new
  · rcases h.2.2 label middle with ⟨loc, known, eq⟩ | old
    · exact Or.inl ⟨loc, (h'.1 loc known).1, eq⟩
    · exact Or.inr old

private theorem insert_growth (loc count : Nat) (s : State) :
    Grows s (insertEachSource loc count s) := by
  refine ⟨insertEach_subspt loc count s, by simp [insertEach_snd], ?_⟩
  intro label member
  right
  simpa [insertEach_snd] using member

mutual
private theorem growth_expr (e : Exp) (s : State) :
    Grows s (callsSing e s).2 := by
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
      · have extended := trans (insert_growth _ _ s) ih
        refine ⟨extended.1, extended.2.1.trans (List.suffix_cons _ _), ?_⟩
        intro label member
        simp only [List.map_cons, List.mem_cons] at member
        rcases member with same | old
        · left
          refine ⟨loc.getD 0, ?_, ?_⟩
          · have inFresh : sptDomain fresh.1 (loc.getD 0) := by
              dsimp [fresh]
              rw [domain_insertEach]
              exact Or.inl (by simp)
            exact (ih.1 _ inFresh).1
          · simpa [Nat.succ_eq_add_one] using same
        · exact extended.2.2 label old
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
        have emitGrowth : Grows st emitted := by
          refine ⟨by simpa [emitted, codeListSource_fst] using (refl st).1,
            codeListSource_suffix _ _ _, ?_⟩
          intro label member
          simp only [emitted, codeListSource_labels, List.mem_append, List.mem_reverse,
            List.mem_map, List.mem_range] at member
          rcases member with ⟨i, bound, eq⟩ | old
          · left
            refine ⟨loc.getD 0 + 2 * i, ?_, ?_⟩
            · have inFresh : sptDomain fresh.1 (loc.getD 0 + 2 * i) := by
                dsimp [fresh]
                rw [domain_insertEach]
                left
                simp only [Set.mem_ofPred_eq, List.mem_map, List.mem_range]
                refine ⟨i, ?_, ?_⟩
                · simp only [List.length_zip, List.length_map] at bound
                  omega
                · omega
              change sptDomain (codeListSource _ _ st).1 _
              rw [codeListSource_fst]
              exact (ihF.1 _ inFresh).1
            · omega
          · exact Or.inr (List.mem_map.mpr old)
        have ihBody := growth_expr body emitted
        cases hb : callsSing body emitted with
        | mk out final =>
          simp only [hb] at ihBody
          change Grows s final
          exact trans (trans (trans (insert_growth _ _ s) ihF) emitGrowth) ihBody
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
    Grows s (callsSingList es s).2 := by
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
  simpa [h] using result.1

/-- Direct-call conversion retains the old auxiliary code as a suffix. -/

@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_IS_SUFFIX"]
theorem calls_suffix (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g)) : g0.2 <:+ g.2 := by
  have result := growth_list xs g0
  change callsSingList xs g0 = (ys, g) at h
  simpa [h] using result.2.1

/-- Direct-call conversion preserves old locations and code labels; every new
label is the successor of a location in the final state. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_code_subset"]
theorem calls_codeSubset (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g)) :
    Set.image Nat.succ (sptDomain g0.1) ⊆ Set.image Nat.succ (sptDomain g.1) ∧
    { label | label ∈ g0.2.map Prod.fst } ⊆ { label | label ∈ g.2.map Prod.fst } ∧
    { label | label ∈ g.2.map Prod.fst } ⊆
      Set.image Nat.succ (sptDomain g.1) ∪ { label | label ∈ g0.2.map Prod.fst } := by
  have growth := growth_list xs g0
  change callsSingList xs g0 = (ys, g) at h
  rw [h] at growth
  refine ⟨?_, ?_, ?_⟩
  · rintro label ⟨loc, known, rfl⟩
    exact ⟨loc, (growth.1 loc known).1, rfl⟩
  · intro label member
    obtain ⟨added, eq⟩ := growth.2.1
    rw [← eq, List.map_append]
    exact List.mem_append_right _ member
  · intro label member
    rcases growth.2.2 label member with ⟨loc, known, eq⟩ | old
    · exact Or.inl ⟨loc, known, eq.symm⟩
    · exact Or.inr old

end Flapjack.Compiler.Backend.ClosCall
