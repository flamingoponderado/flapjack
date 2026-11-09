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
    cases expression with
    | var trace index => simp [introMultiFuel] at run; subst result; exact valid
    | raise trace body =>
      cases step : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, step] at run
      | some next =>
        have equal : .raise trace next = result := by simpa [introMultiFuel, step] using run
        subst result
        simp only [noLabels] at valid ⊢
        exact ih body next step valid
    | tick trace body =>
      cases step : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, step] at run
      | some next =>
        have equal : .tick trace next = result := by simpa [introMultiFuel, step] using run
        subst result
        simp only [noLabels] at valid ⊢
        exact ih body next step valid
    | ifThenElse trace condition yes no =>
      cases hc : introMultiFuel fuel maxApp condition with
      | none => simp [introMultiFuel, hc] at run
      | some condition' =>
        cases hy : introMultiFuel fuel maxApp yes with
        | none => simp [introMultiFuel, hc, hy] at run
        | some yes' =>
          cases hn : introMultiFuel fuel maxApp no with
          | none => simp [introMultiFuel, hc, hy, hn] at run
          | some no' =>
            have equal : .ifThenElse trace condition' yes' no' = result := by
              simpa [introMultiFuel, hc, hy, hn] using run
            subst result
            simp only [noLabels] at valid ⊢
            exact ⟨ih condition condition' hc valid.1, ih yes yes' hy valid.2.1, ih no no' hn valid.2.2⟩
    | handle trace body handler =>
      cases hb : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, hb] at run
      | some body' =>
        cases hh : introMultiFuel fuel maxApp handler with
        | none => simp [introMultiFuel, hb, hh] at run
        | some handler' =>
          have equal : .handle trace body' handler' = result := by simpa [introMultiFuel, hb, hh] using run
          subst result
          simp only [noLabels] at valid ⊢
          exact ⟨ih body body' hb valid.1, ih handler handler' hh valid.2⟩
    | «let» trace bindings body =>
      cases hs : bindings.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some bindings' =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hs, hb] at run
        | some body' =>
          have equal : .let trace bindings' body' = result := by simpa [introMultiFuel, hs, hb] using run
          subst result
          simp only [noLabels] at valid ⊢
          exact ⟨listStep bindings bindings' hs valid.1, ih body body' hb valid.2⟩
    | call trace ticks location args =>
      cases hs : args.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some args' =>
        have equal : .call trace ticks location args' = result := by simpa [introMultiFuel, hs] using run
        subst result
        simp only [noLabels] at valid ⊢
        exact listStep args args' hs valid
    | op trace op args =>
      cases hs : args.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some args' =>
        have equal : .op trace op args' = result := by simpa [introMultiFuel, hs] using run
        subst result
        simp only [noLabels] at valid ⊢
        exact ⟨valid.1, listStep args args' hs valid.2⟩
    | app trace location head args =>
      cases location with
      | some location =>
        cases hh : introMultiFuel fuel maxApp head with
        | none => simp [introMultiFuel, hh] at run
        | some head' =>
          cases ha : args.mapM (introMultiFuel fuel maxApp) with
          | none => simp [introMultiFuel, hh, ha] at run
          | some args' =>
            have equal : .app trace (some location) head' args' = result := by
              simpa [introMultiFuel, hh, ha] using run
            subst result
            simp only [noLabels] at valid ⊢
            exact ⟨ih head head' hh valid.1, listStep args args' ha valid.2⟩
      | none =>
        cases collected : collectApps maxApp args head with
        | mk collectedArgs collectedHead =>
          cases hh : introMultiFuel fuel maxApp collectedHead with
          | none => simp [introMultiFuel, collected, hh] at run
          | some head' =>
            cases ha : collectedArgs.mapM (introMultiFuel fuel maxApp) with
            | none => simp [introMultiFuel, collected, hh, ha] at run
            | some args' =>
              have equal : .app trace none head' args' = result := by
                simpa [introMultiFuel, collected, hh, ha] using run
              subst result
              simp only [noLabels] at valid ⊢
              have collectedValid := collectApps_noLabels maxApp args head collectedArgs collectedHead
                ⟨collected, (noLabelsList_iff args).mp valid.2, valid.1⟩
              exact ⟨ih collectedHead head' hh collectedValid.2,
                listStep collectedArgs args' ha ((noLabelsList_iff collectedArgs).mpr collectedValid.1)⟩
    | fn name location vars arity body =>
      cases location with
      | some location =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => cases vars <;> simp [introMultiFuel, hb] at run
        | some body' =>
          cases vars <;> simp [introMultiFuel, hb] at run <;> subst result <;>
            simp only [noLabels] at valid ⊢ <;> exact ih body body' hb valid
      | none =>
        cases vars with
        | some vars =>
          cases hb : introMultiFuel fuel maxApp body with
          | none => simp [introMultiFuel, hb] at run
          | some body' =>
            have equal : .fn name none (some vars) arity body' = result := by
              simpa [introMultiFuel, hb] using run
            subst result
            simp only [noLabels] at valid ⊢
            exact ih body body' hb valid
        | none =>
          cases collected : collectArgs maxApp arity body with
          | mk count remaining =>
            cases hb : introMultiFuel fuel maxApp remaining with
            | none => simp [introMultiFuel, collected, hb] at run
            | some body' =>
              have equal : .fn name none none count body' = result := by
                simpa [introMultiFuel, collected, hb] using run
              subst result
              simp only [noLabels] at valid ⊢
              exact ih remaining body' hb (collectArgs_noLabels maxApp arity body count remaining ⟨collected, valid⟩)
    | letrec names location vars functions body =>
      let collected (entry : Nat × Exp) : Option (Nat × Exp) := do
        let (arity, rest) := collectArgs maxApp entry.1 entry.2
        pure (arity, ← introMultiFuel fuel maxApp rest)
      have collectedStep : ∀ target, functions.mapM collected = some target →
          noLabelsFuns functions → noLabelsFuns target := by
        intro target run valid
        apply mapM_funs_noLabels collected functions target _ run valid
        intro entry result run valid
        cases entry with
        | mk arity body =>
          cases found : collectArgs maxApp arity body with
          | mk count rest =>
            cases step : introMultiFuel fuel maxApp rest with
            | none => simp [collected, found, step] at run
            | some body' =>
              have equal : (count, body') = result := by simpa [collected, found, step] using run
              subst result
              exact ih rest body' step (collectArgs_noLabels maxApp arity body count rest ⟨found, valid⟩)
      cases location <;> cases vars
      case none.none =>
        change (do
          let fs ← functions.mapM collected
          let b ← introMultiFuel fuel maxApp body
          pure (.letrec names none none fs b)) = some result at run
        cases hf : functions.mapM collected with
        | none => simp [hf] at run
        | some functions' =>
          cases hb : introMultiFuel fuel maxApp body with
          | none => simp [hf, hb] at run
          | some body' =>
            simp [hf, hb] at run
            subst result
            simp only [noLabels] at valid ⊢
            exact ⟨collectedStep functions' hf valid.1, ih body body' hb valid.2⟩
      all_goals
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hb] at run
        | some body' =>
          simp [introMultiFuel, hb] at run
          subst result
          simp only [noLabels] at valid ⊢
          exact ⟨valid.1, ih body body' hb valid.2⟩
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
