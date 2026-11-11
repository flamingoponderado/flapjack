module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.InsertDomain
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Suffix
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Flapjack.Misc.Sptree.Subspt
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLocations

@[expose] public section

/-! Preservation of known locations by direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

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

private def FullGrows (s t : State) : Prop :=
  Grows s t ∧ ∀ loc, sptDomain t.1 loc →
    sptDomain s.1 loc ∨ ∃ label ∈ t.2.map Prod.fst, loc = Nat.pred label

private theorem fullRefl (s : State) : FullGrows s s :=
  ⟨refl s, fun _ h => Or.inl h⟩

private theorem fullTrans {s t u : State} (h : FullGrows s t) (h' : FullGrows t u) : FullGrows s u := by
  refine ⟨trans h.1 h'.1, ?_⟩
  intro loc present
  rcases h'.2 loc present with middle | new
  · rcases h.2 loc middle with old | ⟨label, member, eq⟩
    · exact Or.inl old
    · right
      obtain ⟨added, appendEq⟩ := h'.1.2.1
      refine ⟨label, ?_, eq⟩
      rw [← appendEq, List.map_append]
      exact List.mem_append_right _ member
  · exact Or.inr new

private def DomainBound (initial final : State) (locations : List Nat) : Prop :=
  ∀ k, sptDomain final.1 k → sptDomain initial.1 k ∨ k ∈ locations

private theorem domainBound_refl (s : State) (locations : List Nat) : DomainBound s s locations :=
  fun _ h => Or.inl h

private theorem domainBound_mono {s t : State} {small large : List Nat}
    (h : DomainBound s t small) (sub : ∀ k ∈ small, k ∈ large) : DomainBound s t large := by
  intro k found
  rcases h k found with old | new
  · exact Or.inl old
  · exact Or.inr (sub k new)

private theorem domainBound_append {s t u : State} {xs ys : List Nat}
    (h₁ : DomainBound s t xs) (h₂ : DomainBound t u ys) : DomainBound s u (xs ++ ys) := by
  intro k found
  rcases h₂ k found with intermediate | new
  · rcases h₁ k intermediate with old | new
    · exact Or.inl old
    · exact Or.inr (List.mem_append_left _ new)
  · exact Or.inr (List.mem_append_right _ new)

private theorem domainBound_insert (s : State) (loc n : Nat) :
    DomainBound s (insertEachSource loc n s) ((List.range n).map (fun i => loc + 2 * i)) := by
  intro k found
  rw [domain_insertEach] at found
  rcases found with generated | old
  · right
    simp only [Set.mem_ofPred_eq, List.mem_map] at generated ⊢
    obtain ⟨i, hi, eq⟩ := generated
    exact ⟨i, hi, by omega⟩
  · exact Or.inl old

private def IndexedGrows (s t : State) (locations : List Nat) : Prop :=
  FullGrows s t ∧ DomainBound s t locations

private theorem indexedRefl (s : State) (locations : List Nat) : IndexedGrows s s locations :=
  ⟨fullRefl s, domainBound_refl s locations⟩

private theorem indexedTrans {s t u : State} {xs ys : List Nat}
    (h : IndexedGrows s t xs) (h' : IndexedGrows t u ys) : IndexedGrows s u (xs ++ ys) :=
  ⟨fullTrans h.1 h'.1, domainBound_append h.2 h'.2⟩

private theorem indexedMono {s t : State} {small large : List Nat}
    (h : IndexedGrows s t small) (sub : ∀ k ∈ small, k ∈ large) : IndexedGrows s t large :=
  ⟨h.1, domainBound_mono h.2 sub⟩

mutual
private theorem growth_expr (e : Exp) (s : State) :
    IndexedGrows s (callsSing e s).2 (codeLocationsExp e) := by
  cases e with
  | var tr n => simpa [callsSing] using indexedRefl s _
  | raise tr e | tick tr e =>
    have ih := growth_expr e s
    cases run : callsSing e s with
    | mk out next => simpa [callsSing, run, codeLocationsExp] using ih
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
          simpa [callsSing, hx, hy, hz, codeLocationsExp] using indexedTrans (indexedTrans h₁ h₂) h₃
  | «let» tr args body =>
    cases hx : callsSingList args s with
    | mk ox sx =>
      cases hy : callsSing body sx with
      | mk oy sy =>
        have h₁ := growth_list args s
        have h₂ := growth_expr body sx
        simp only [hx] at h₁
        simp only [hy] at h₂
        simpa [callsSing, hx, hy, codeLocationsExp] using indexedTrans h₁ h₂
  | handle tr x y =>
    cases hx : callsSing x s with
    | mk ox sx =>
      cases hy : callsSing y sx with
      | mk oy sy =>
        have h₁ := growth_expr x s
        have h₂ := growth_expr y sx
        simp only [hx] at h₁
        simp only [hy] at h₂
        simpa [callsSing, hx, hy, codeLocationsExp] using indexedTrans h₁ h₂
  | call tr ticks dest args | op tr dest args =>
    have ih := growth_list args s
    cases run : callsSingList args s with
    | mk out next => simpa [callsSing, run, codeLocationsExp] using ih
  | app tr loc body args =>
    cases hx : callsSingList args s with
    | mk ox sx =>
      cases hy : callsSing body sx with
      | mk oy sy =>
        have h₁ := growth_list args s
        have h₂ := growth_expr body sx
        simp only [hx] at h₁
        simp only [hy] at h₂
        have combined := indexedTrans h₁ h₂
        cases loc with
        | none =>
          simp only [callsSing, hx, hy]
          apply indexedMono combined
          simp [codeLocationsExp, List.mem_append, or_comm]
        | some loc =>
          simp only [callsSing, hx, hy]
          cases (sptLookup loc sy.1).isSome <;> cases ClosLang.pure body <;>
            simp only [Bool.false_eq_true, ↓reduceIte] <;>
            apply indexedMono combined <;>
            simp [codeLocationsExp, List.mem_append, or_comm]
  | fn name loc vars arity body =>
    let fresh := insertEachSource (loc.getD 0) 1 s
    cases hf : callsSing body fresh with
    | mk out st =>
      have ih := growth_expr body fresh
      simp only [hf] at ih
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · constructor
        · constructor
          · have extended := trans (insert_growth _ _ s) ih.1.1
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
                exact (ih.1.1.1 _ inFresh).1
              · simpa [Nat.succ_eq_add_one] using same
            · exact extended.2.2 label old
          · intro x present
            rcases ih.1.2 x present with initial | ⟨label, member, eq⟩
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
        · have combined := domainBound_append (domainBound_insert s (loc.getD 0) 1) ih.2
          apply domainBound_mono combined
          simp [codeLocationsExp, List.mem_append, or_comm]
      · have ih := growth_expr body s
        cases hr : callsSing body s with
        | mk out next =>
          simp only [hr] at ih ⊢
          apply indexedMono ih
          intro k member
          simp [codeLocationsExp, member]
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
              exact (ihF.1.1.1 _ inFresh).1
            · omega
          · exact Or.inr (List.mem_map.mpr old)
        have fullEmit : FullGrows s emitted := by
          refine ⟨trans (trans (insert_growth _ _ s) ihF.1.1) emitGrowth, ?_⟩
          intro x present
          have stPresent : sptDomain st.1 x := by
            simpa [emitted, codeListSource_fst] using present
          rcases ihF.1.2 x stPresent with initial | ⟨label, member, eq⟩
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
          change IndexedGrows s final _
          constructor
          · exact fullTrans fullEmit ihBody.1
          · have emitBound : DomainBound st emitted [] := by
              simp [DomainBound, emitted, codeListSource_fst]
            have all := domainBound_append
              (domainBound_append (domainBound_append (domainBound_insert s (loc.getD 0) fns.length) ihF.2)
                emitBound) ihBody.2
            apply domainBound_mono all
            simp [codeLocationsExp, codeLocationsFuns_map, List.mem_append, or_comm, or_left_comm, or_assoc]
      · cases hg : callsSingList (fns.map Prod.snd) s with
        | mk bodies st =>
          have ihG := growth_list (fns.map Prod.snd) s
          simp only [hg] at ihG ⊢
          cases hb : callsSing body st with
          | mk out final =>
            have ihBody := growth_expr body st
            simp only [hb] at ihBody ⊢
            apply indexedMono (indexedTrans ihG ihBody)
            simp only [codeLocationsExp, codeLocationsFuns_map, List.mem_append]
            aesop

termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have bound := sizeOf_map_snd_le fns
  all_goals omega

private theorem growth_list (es : List Exp) (s : State) :
    IndexedGrows s (callsSingList es s).2 (codeLocations es) := by
  cases es with
  | nil => simpa [callsSingList] using indexedRefl s (codeLocations [])
  | cons e es =>
    cases he : callsSing e s with
    | mk out mid =>
      cases hs : callsSingList es mid with
      | mk outs final =>
        have h₁ := growth_expr e s
        have h₂ := growth_list es mid
        simp only [he] at h₁
        simp only [hs] at h₂
        simpa [callsSingList, he, hs, codeLocations] using indexedTrans h₁ h₂
termination_by sizeOf es
decreasing_by all_goals simp_wf <;> omega
end

/-- Direct-call conversion preserves all previously known locations. -/

@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_subspt"]
theorem calls_subspt (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g)) : sptSubspt g0.1 g.1 := by
  have result := growth_list xs g0
  change callsSingList xs g0 = (ys, g) at h
  simpa [h] using result.1.1.1

/-- Direct-call conversion retains the old auxiliary code as a suffix. -/

@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_IS_SUFFIX"]
theorem calls_suffix (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (h : calls xs g0 = (ys, g)) : g0.2 <:+ g.2 := by
  have result := growth_list xs g0
  change callsSingList xs g0 = (ys, g) at h
  simpa [h] using result.1.1.2.1

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
  have growth := growth.1.1
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
  rcases growth.1.2 loc present with old | ⟨label, member, eq⟩
  · exact Or.inl old
  · exact Or.inr ⟨label, member, eq.symm⟩

/-- A direct-call traversal adds only locations occurring in its input. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_domain_locs"]
theorem calls_domainLocations (xs : List Exp) (g : State) (ys : List Exp) (g2 : State)
    (h : calls xs g = (ys, g2)) :
    Set.Subset (sptDomain g2.1) (Set.union (sptDomain g.1) {x | x ∈ codeLocations xs}) := by
  have bound := (growth_list xs g).2
  change callsSingList xs g = (ys, g2) at h
  rw [h] at bound
  exact bound


end Flapjack.Compiler.Backend.ClosCall
