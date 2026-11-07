import Flapjack.Compiler.Backend.ClosMti.Proofs.Globals

/-! Global-write bag preservation through multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang ClosProps
open Flapjack.Compiler.Backend.FlatProps (unionGlobalBag)
private theorem mapM_globals (f : Exp → Option Exp) (source target : List Exp)
    (pointwise : ∀ e result, f e = some result → setGlobals result = setGlobals e)
    (run : source.mapM f = some target) : elistGlobals target = elistGlobals source := by
  induction source generalizing target with
  | nil => simp at run; subst target; rfl
  | cons first rest ih =>
    cases head : f first with
    | none => simp [List.mapM_cons, head] at run
    | some next =>
      cases tail : rest.mapM f with
      | none => simp [List.mapM_cons, head, tail] at run
      | some nextRest =>
        have equal : next :: nextRest = target := by simpa [List.mapM_cons, head, tail] using run
        subst target
        simp only [elistGlobals, pointwise first next head, ih nextRest tail]

private theorem mapM_funs_globals (f : Nat × Exp → Option (Nat × Exp))
    (source target : List (Nat × Exp))
    (pointwise : ∀ entry result, f entry = some result → setGlobals result.2 = setGlobals entry.2)
    (run : source.mapM f = some target) : funGlobals target = funGlobals source := by
  induction source generalizing target with
  | nil => simp at run; subst target; rfl
  | cons first rest ih =>
    cases first with
    | mk arity body =>
      cases head : f (arity, body) with
      | none => simp [List.mapM_cons, head] at run
      | some next =>
        cases tail : rest.mapM f with
        | none => simp [List.mapM_cons, head, tail] at run
        | some nextRest =>
          have equal : next :: nextRest = target := by simpa [List.mapM_cons, head, tail] using run
          subst target
          cases next with
          | mk nextArity nextBody =>
            simp only [funGlobals, pointwise _ _ head, ih nextRest tail]
private theorem fuel_globals (fuel maxApp : Nat) (expression result : Exp)
    (run : introMultiFuel fuel maxApp expression = some result) : setGlobals result = setGlobals expression := by
  induction fuel generalizing expression result with
  | zero => simp [introMultiFuel] at run
  | succ fuel ih =>
    have listStep (source target : List Exp)
        (run : source.mapM (introMultiFuel fuel maxApp) = some target) :
        elistGlobals target = elistGlobals source :=
      mapM_globals _ source target (fun e result run => ih e result run) run
    cases expression with
    | var trace index => simp [introMultiFuel] at run; subst result; rfl
    | raise trace body =>
      cases step : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, step] at run
      | some next =>
        have equal : .raise trace next = result := by simpa [introMultiFuel, step] using run
        subst result
        simpa [setGlobals] using ih body next step
    | tick trace body =>
      cases step : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, step] at run
      | some next =>
        have equal : .tick trace next = result := by simpa [introMultiFuel, step] using run
        subst result
        simpa [setGlobals] using ih body next step
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
            simp only [setGlobals, ih condition condition' hc, ih yes yes' hy, ih no no' hn]
    | handle trace body handler =>
      cases hb : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, hb] at run
      | some body' =>
        cases hh : introMultiFuel fuel maxApp handler with
        | none => simp [introMultiFuel, hb, hh] at run
        | some handler' =>
          have equal : .handle trace body' handler' = result := by simpa [introMultiFuel, hb, hh] using run
          subst result
          simp only [setGlobals, ih body body' hb, ih handler handler' hh]
    | «let» trace bindings body =>
      cases hs : bindings.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some bindings' =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hs, hb] at run
        | some body' =>
          have equal : .let trace bindings' body' = result := by simpa [introMultiFuel, hs, hb] using run
          subst result
          simp only [setGlobals, ih body body' hb, listStep bindings bindings' hs]
    | call trace ticks location args =>
      cases hs : args.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some args' =>
        have equal : .call trace ticks location args' = result := by simpa [introMultiFuel, hs] using run
        subst result
        simpa [setGlobals] using listStep args args' hs
    | op trace op args =>
      cases hs : args.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some args' =>
        have equal : .op trace op args' = result := by simpa [introMultiFuel, hs] using run
        subst result
        simp only [setGlobals, listStep args args' hs]
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
            simp only [setGlobals, ih head head' hh, listStep args args' ha]
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
              simp only [setGlobals, ih collectedHead head' hh, listStep collectedArgs args' ha]
              have collector := collectApps_preserves_setGlobals maxApp args head collectedArgs collectedHead collected
              funext key
              have point := congrFun collector key
              simp only [unionGlobalBag, Flapjack.bagUnion] at point ⊢
              omega
    | fn name location vars arity body =>
      cases location with
      | some location =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => cases vars <;> simp [introMultiFuel, hb] at run
        | some body' =>
          cases vars <;> simp [introMultiFuel, hb] at run <;> subst result <;>
            simpa [setGlobals] using ih body body' hb
      | none =>
        cases vars with
        | some vars =>
          cases hb : introMultiFuel fuel maxApp body with
          | none => simp [introMultiFuel, hb] at run
          | some body' =>
            have equal : .fn name none (some vars) arity body' = result := by
              simpa [introMultiFuel, hb] using run
            subst result
            simpa [setGlobals] using ih body body' hb
        | none =>
          cases collected : collectArgs maxApp arity body with
          | mk count remaining =>
            cases hb : introMultiFuel fuel maxApp remaining with
            | none => simp [introMultiFuel, collected, hb] at run
            | some body' =>
              have equal : .fn name none none count body' = result := by
                simpa [introMultiFuel, collected, hb] using run
              subst result
              simpa [setGlobals] using (ih remaining body' hb).trans
                (collectArgs_preserves_setGlobals maxApp arity body count remaining collected)
    | letrec names location vars functions body =>
      let collected (entry : Nat × Exp) : Option (Nat × Exp) := do
        let (arity, rest) := collectArgs maxApp entry.1 entry.2
        pure (arity, ← introMultiFuel fuel maxApp rest)
      have collectedStep : ∀ target, functions.mapM collected = some target →
          funGlobals target = funGlobals functions := by
        intro target run
        apply mapM_funs_globals collected functions target _ run
        intro entry result run
        cases entry with
        | mk arity body =>
          cases found : collectArgs maxApp arity body with
          | mk count rest =>
            cases step : introMultiFuel fuel maxApp rest with
            | none => simp [collected, found, step] at run
            | some body' =>
              have equal : (count, body') = result := by simpa [collected, found, step] using run
              subst result
              exact (ih rest body' step).trans (collectArgs_preserves_setGlobals maxApp arity body count rest found)
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
            simp only [setGlobals, collectedStep functions' hf, ih body body' hb]
      all_goals
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hb] at run
        | some body' =>
          simp [introMultiFuel, hb] at run
          subst result
          simp only [setGlobals, ih body body' hb]
private theorem introExp_globals (maxApp : Nat) (expression : Exp) :
    setGlobals (introExp maxApp expression) = setGlobals expression := by
  have run := introExp_bounded 0 maxApp expression
  obtain ⟨fuel, success⟩ := introMultiBounded_origin 0 maxApp expression (introExp maxApp expression) run
  exact fuel_globals fuel maxApp expression (introExp maxApp expression) success

/-- Multi-argument introduction preserves the global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "intro_multi_preserves_elist_globals"]
theorem intro_multi_preserves_elist_globals (maxApp : Nat) (es : List Exp) :
    elistGlobals (introList maxApp es) = elistGlobals es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [introList_cons, elistGlobals, introExp_globals, ih]

/-- Optional multi-argument compilation preserves the global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "compile_preserves_elist_globals"]
theorem compile_preserves_elist_globals (maxApp : Nat) (enabled : Bool) (es : List Exp) :
    elistGlobals (compile enabled maxApp es) = elistGlobals es := by
  cases enabled <;> simp [compile, intro_multi_preserves_elist_globals]

private theorem mapM_esgcFree (f : Exp → Option Exp) (source target : List Exp)
    (pointwise : ∀ e result, f e = some result → esgcFree e → esgcFree result)
    (run : source.mapM f = some target) (valid : esgcFreeList source) : esgcFreeList target := by
  induction source generalizing target with
  | nil => simp at run; subst target; simp [esgcFreeList]
  | cons first rest ih =>
    simp only [esgcFreeList] at valid
    cases head : f first with
    | none => simp [List.mapM_cons, head] at run
    | some next =>
      cases tail : rest.mapM f with
      | none => simp [List.mapM_cons, head, tail] at run
      | some nextRest =>
        have equal : next :: nextRest = target := by simpa [List.mapM_cons, head, tail] using run
        subst target
        simp only [esgcFreeList]
        exact ⟨pointwise first next head valid.1, ih nextRest tail valid.2⟩

private theorem fuel_esgcFree (fuel maxApp : Nat) (expression result : Exp)
    (run : introMultiFuel fuel maxApp expression = some result) (valid : esgcFree expression) :
    esgcFree result := by
  induction fuel generalizing expression result with
  | zero => simp [introMultiFuel] at run
  | succ fuel ih =>
    have listStep (source target : List Exp)
        (run : source.mapM (introMultiFuel fuel maxApp) = some target)
        (valid : esgcFreeList source) : esgcFreeList target :=
      mapM_esgcFree _ source target (fun e result run valid => ih e result run valid) run valid
    cases expression with
    | var trace index => simp [introMultiFuel] at run; subst result; exact valid
    | raise trace body =>
      cases step : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, step] at run
      | some next =>
        have equal : .raise trace next = result := by simpa [introMultiFuel, step] using run
        subst result
        simp only [esgcFree] at valid ⊢
        exact ih body next step valid
    | tick trace body =>
      cases step : introMultiFuel fuel maxApp body with
      | none => simp [introMultiFuel, step] at run
      | some next =>
        have equal : .tick trace next = result := by simpa [introMultiFuel, step] using run
        subst result
        simp only [esgcFree] at valid ⊢
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
            simp only [esgcFree] at valid ⊢
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
          simp only [esgcFree] at valid ⊢
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
          simp only [esgcFree] at valid ⊢
          exact ⟨listStep bindings bindings' hs valid.1, ih body body' hb valid.2⟩
    | call trace ticks location args =>
      cases hs : args.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some args' =>
        have equal : .call trace ticks location args' = result := by simpa [introMultiFuel, hs] using run
        subst result
        simp only [esgcFree] at valid ⊢
        exact listStep args args' hs valid
    | op trace op args =>
      cases hs : args.mapM (introMultiFuel fuel maxApp) with
      | none => simp [introMultiFuel, hs] at run
      | some args' =>
        have equal : .op trace op args' = result := by simpa [introMultiFuel, hs] using run
        subst result
        simp only [esgcFree] at valid ⊢
        exact listStep args args' hs valid
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
            simp only [esgcFree] at valid ⊢
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
              simp only [esgcFree] at valid ⊢
              have collectedValid := collectApps_preserves_esgcFree maxApp args head collectedArgs collectedHead
                ⟨collected, (esgcFreeList_iff args).mp valid.2, valid.1⟩
              exact ⟨ih collectedHead head' hh collectedValid.2,
                listStep collectedArgs args' ha ((esgcFreeList_iff collectedArgs).mpr collectedValid.1)⟩
    | fn name location vars arity body =>
      have globalEq := fuel_globals (fuel + 1) maxApp (.fn name location vars arity body) result run
      cases location with
      | some location =>
        cases hb : introMultiFuel fuel maxApp body with
        | none => cases vars <;> simp [introMultiFuel, hb] at run
        | some body' =>
          cases vars <;> simp [introMultiFuel, hb] at run <;> subst result <;>
            simp only [esgcFree] at valid ⊢ <;>
            simp only [setGlobals] at globalEq <;> exact globalEq.trans valid
      | none =>
        cases vars with
        | some vars =>
          cases hb : introMultiFuel fuel maxApp body with
          | none => simp [introMultiFuel, hb] at run
          | some body' =>
            have equal : .fn name none (some vars) arity body' = result := by
              simpa [introMultiFuel, hb] using run
            subst result
            simp only [esgcFree] at valid ⊢
            simp only [setGlobals] at globalEq
            exact globalEq.trans valid
        | none =>
          cases collected : collectArgs maxApp arity body with
          | mk count remaining =>
            cases hb : introMultiFuel fuel maxApp remaining with
            | none => simp [introMultiFuel, collected, hb] at run
            | some body' =>
              have equal : .fn name none none count body' = result := by
                simpa [introMultiFuel, collected, hb] using run
              subst result
              simp only [esgcFree] at valid ⊢
              simp only [setGlobals] at globalEq
              exact globalEq.trans valid
    | letrec names location vars functions body =>
      have globalEq := fuel_globals (fuel + 1) maxApp (.letrec names location vars functions body) result run
      let collected (entry : Nat × Exp) : Option (Nat × Exp) := do
        let (arity, rest) := collectArgs maxApp entry.1 entry.2
        pure (arity, ← introMultiFuel fuel maxApp rest)
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
            simp only [esgcFree] at valid ⊢
            have bodyEq := fuel_globals fuel maxApp body body' hb
            have funEq : funGlobals functions' = funGlobals functions := by
              funext key
              have allPoint := congrFun globalEq key
              have bodyPoint := congrFun bodyEq key
              simp only [setGlobals, unionGlobalBag, Flapjack.bagUnion] at allPoint
              omega
            exact ⟨funEq.trans valid.1, ih body body' hb valid.2⟩
      all_goals
        cases hb : introMultiFuel fuel maxApp body with
        | none => simp [introMultiFuel, hb] at run
        | some body' =>
          simp [introMultiFuel, hb] at run
          subst result
          simp only [esgcFree] at valid ⊢
          exact ⟨valid.1, ih body body' hb valid.2⟩
/-- Multi-argument introduction preserves closure safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "intro_multi_preserves_esgc_free"]
theorem intro_multi_preserves_esgc_free (maxApp : Nat) (expressions : List Exp)
    (valid : ∀ expression ∈ expressions, esgcFree expression) :
    ∀ expression ∈ introList maxApp expressions, esgcFree expression := by
  intro expression member
  obtain ⟨source, sourceMember, rfl⟩ := List.mem_map.mp (by simpa [introList] using member)
  have run := introExp_bounded 0 maxApp source
  obtain ⟨fuel, success⟩ := introMultiBounded_origin 0 maxApp source (introExp maxApp source) run
  exact fuel_esgcFree fuel maxApp source (introExp maxApp source) success (valid source sourceMember)

/-- Optional multi-argument compilation preserves closure safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "compile_preserves_esgc_free"]
theorem compile_preserves_esgc_free (maxApp : Nat) (enabled : Bool) (expressions : List Exp)
    (valid : ∀ expression ∈ expressions, esgcFree expression) :
    ∀ expression ∈ compile enabled maxApp expressions, esgcFree expression := by
  cases enabled with
  | false => simpa [compile] using valid
  | true => simpa [compile] using intro_multi_preserves_esgc_free maxApp expressions valid
end Flapjack.Compiler.Backend.ClosMti
