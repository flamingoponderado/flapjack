module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.Syntactic

@[expose] public section

/-! Label preservation for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang ClosProps
private theorem mapM_noLabels (f : Exp → Option Exp) (source target : List Exp)
    (pointwise : ∀ e result, f e = some result → noLabels e → noLabels result)
    (run : source.mapM f = some target) (valid : noLabelsList source) : noLabelsList target := by
  have rel := mapM_rel f (fun e result => noLabels e → noLabels result) pointwise source target run
  clear run
  induction rel with
  | nil => simp [noLabelsList]
  | cons first rest ih =>
    simp only [noLabelsList] at valid ⊢
    exact ⟨first valid.1, ih valid.2⟩

private theorem mapM_funs_noLabels (f : Nat × Exp → Option (Nat × Exp))
    (source target : List (Nat × Exp))
    (pointwise : ∀ entry result, f entry = some result → noLabels entry.2 → noLabels result.2)
    (run : source.mapM f = some target) (valid : noLabelsFuns source) : noLabelsFuns target := by
  have rel := mapM_rel f (fun entry result => noLabels entry.2 → noLabels result.2) pointwise source target run
  clear run
  induction rel with
  | nil => simp [noLabelsFuns]
  | @cons a b xs ys first rest ih =>
    cases a
    cases b
    simp only [noLabelsFuns] at valid ⊢
    exact ⟨first valid.1, ih valid.2⟩

private theorem fuel_noLabels (fuel maxApp : Nat) (expression result : Exp)
    (run : introMultiFuel fuel maxApp expression = some result) (valid : noLabels expression) :
    noLabels result := by
  induction fuel generalizing expression result with
  | zero => simp [introMultiFuel] at run
  | succ fuel ih =>
    have listStep (source target : List Exp)
        (run : source.mapM (introMultiFuel fuel maxApp) = some target)
        (valid : noLabelsList source) : noLabelsList target :=
      mapM_noLabels _ source target (fun e result run valid => ih e result run valid) run valid
    have funsStep : ∀ source target, source.mapM (collectEntry maxApp fuel) = some target →
        noLabelsFuns source → noLabelsFuns target := by
      intro source target run valid
      apply mapM_funs_noLabels (collectEntry maxApp fuel) source target _ run valid
      intro entry result run valid
      cases entry with
      | mk arity body =>
        cases found : collectArgs maxApp arity body with
        | mk count rest =>
          cases step : introMultiFuel fuel maxApp rest with
          | none => simp [collectEntry, found, step] at run
          | some body' =>
            have equal : (count, body') = result := by simpa [collectEntry, found, step] using run
            subst result
            exact ih rest body' step
              (collectArgs_noLabels maxApp arity body count rest ⟨found, valid⟩)
    exact introMultiFuel_step (fuel := fuel) (maxApp := maxApp)
      (R := fun e r => noLabels e → noLabels r)
      (RList := fun xs ys => noLabelsList xs → noLabelsList ys)
      (RFuns := fun fs fs' => noLabelsFuns fs → noLabelsFuns fs')
      (fun _ _ h => h)
      (by
        intro t c c' y y' z z' hc hy hz h
        simp only [noLabels] at h ⊢
        exact ⟨hc h.1, hy h.2.1, hz h.2.2⟩)
      (by
        intro t xs xs' b b' hs hb h
        simp only [noLabels] at h ⊢
        exact ⟨hs h.1, hb h.2⟩)
      (by
        intro t b b' hb h
        simp only [noLabels] at h ⊢
        exact hb h)
      (by
        intro t b b' h h' hb hh h
        simp only [noLabels] at h ⊢
        exact ⟨hb h.1, hh h.2⟩)
      (by
        intro t b b' hb h
        simp only [noLabels] at h ⊢
        exact hb h)
      (by
        intro t k l xs xs' hs h
        simp only [noLabels] at h ⊢
        exact hs h)
      (by
        intro t l b b' xs xs' hb hs h
        simp only [noLabels] at h ⊢
        exact ⟨hb h.1, hs h.2⟩)
      (by
        intro t args head argsC headC head' args' collected hlen hhead hargs h
        simp only [noLabels] at h ⊢
        have cv := collectApps_noLabels maxApp args head argsC headC
          ⟨collected, (noLabelsList_iff args).mp h.2, h.1⟩
        exact ⟨hhead cv.2, hargs ((noLabelsList_iff argsC).mpr cv.1)⟩)
      (by
        intro t l v a b b' hb h
        simp only [noLabels] at h ⊢
        exact hb h)
      (by
        intro t v a b b' hb h
        simp only [noLabels] at h ⊢
        exact hb h)
      (by
        intro t a b c rest b' collected hrest h
        simp only [noLabels] at h ⊢
        exact hrest (collectArgs_noLabels maxApp a b c rest ⟨collected, h⟩))
      (by
        intro t fs fs' b b' hfs hb h
        simp only [noLabels] at h ⊢
        exact ⟨hfs h.1, hb h.2⟩)
      (by
        intro t l v fs b b' hb h
        simp only [noLabels] at h ⊢
        exact ⟨h.1, hb h.2⟩)
      (by
        intro t v fs b b' hb h
        simp only [noLabels] at h ⊢
        exact ⟨h.1, hb h.2⟩)
      (by
        intro t o xs xs' hs h
        simp only [noLabels] at h ⊢
        exact ⟨h.1, hs h.2⟩)
      listStep funsStep ih run valid

/-- Multi-argument introduction preserves label-free source expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "intro_multi_no_Labels"]
theorem intro_multi_noLabels (maxApp : Nat) (expressions : List Exp)
    (valid : ∀ expression ∈ expressions, noLabels expression) :
    ∀ expression ∈ introList maxApp expressions, noLabels expression := by
  intro expression member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp (by simpa [introList] using member)
  have run := introExp_bounded 0 maxApp source
  obtain ⟨fuel, success⟩ := introMultiBounded_origin 0 maxApp source (introExp maxApp source) run
  exact fuel_noLabels fuel maxApp source (introExp maxApp source) success (valid source sourceMember)
end Flapjack.Compiler.Backend.ClosMti
