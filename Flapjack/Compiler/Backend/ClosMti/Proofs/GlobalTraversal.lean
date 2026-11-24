module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.Globals

@[expose] public section

/-! Global-write bag preservation through multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang ClosProps
open Flapjack.Compiler.Backend.FlatProps (unionGlobalBag)
private theorem mapM_globals (f : Exp → Option Exp) (source target : List Exp)
    (pointwise : ∀ e result, f e = some result → setGlobals result = setGlobals e)
    (run : source.mapM f = some target) : elistGlobals target = elistGlobals source := by
  have rel := mapM_rel f (fun e result => setGlobals result = setGlobals e) pointwise source target run
  clear run
  induction rel with
  | nil => rfl
  | cons first rest ih => simp only [elistGlobals, first, ih]

private theorem mapM_funs_globals (f : Nat × Exp → Option (Nat × Exp))
    (source target : List (Nat × Exp))
    (pointwise : ∀ entry result, f entry = some result → setGlobals result.2 = setGlobals entry.2)
    (run : source.mapM f = some target) : funGlobals target = funGlobals source := by
  have rel := mapM_rel f (fun entry result => setGlobals result.2 = setGlobals entry.2) pointwise source target run
  clear run
  induction rel with
  | nil => rfl
  | @cons a b xs ys first rest ih =>
    cases a
    cases b
    simp only [funGlobals, first, ih]

private theorem fuel_globals (fuel maxApp : Nat) (expression result : Exp)
    (run : introMultiFuel fuel maxApp expression = some result) : setGlobals result = setGlobals expression := by
  induction fuel generalizing expression result with
  | zero => simp [introMultiFuel] at run
  | succ fuel ih =>
    have listStep (source target : List Exp)
        (run : source.mapM (introMultiFuel fuel maxApp) = some target) :
        elistGlobals target = elistGlobals source :=
      mapM_globals _ source target (fun e result run => ih e result run) run
    have funsStep : ∀ source target, source.mapM (collectEntry maxApp fuel) = some target →
        funGlobals target = funGlobals source := by
      intro source target run
      apply mapM_funs_globals (collectEntry maxApp fuel) source target _ run
      intro entry result run
      cases entry with
      | mk arity body =>
        cases found : collectArgs maxApp arity body with
        | mk count rest =>
          cases step : introMultiFuel fuel maxApp rest with
          | none => simp [collectEntry, found, step] at run
          | some body' =>
            have equal : (count, body') = result := by simpa [collectEntry, found, step] using run
            subst result
            exact (ih rest body' step).trans
              (collectArgs_preserves_setGlobals maxApp arity body count rest found)
    exact introMultiFuel_step (fuel := fuel) (maxApp := maxApp)
      (R := fun e r => setGlobals r = setGlobals e)
      (RList := fun xs ys => elistGlobals ys = elistGlobals xs)
      (RFuns := fun fs fs' => funGlobals fs' = funGlobals fs)
      (fun _ _ => rfl)
      (by
        intro t c c' y y' z z' hc hy hz
        simp [setGlobals, hc, hy, hz])
      (by
        intro t xs xs' b b' hs hb
        simp [setGlobals, hs, hb])
      (by
        intro t b b' hb
        simp [setGlobals, hb])
      (by
        intro t b b' h h' hb hh
        simp [setGlobals, hb, hh])
      (by
        intro t b b' hb
        simp [setGlobals, hb])
      (by
        intro t k l xs xs' hs
        simp [setGlobals, hs])
      (by
        intro t l b b' xs xs' hb hs
        simp [setGlobals, hb, hs])
      (by
        intro t args head argsC headC head' args' collected hlen hhead hargs
        have collector := collectApps_preserves_setGlobals maxApp args head argsC headC collected
        funext key
        have point := congrFun collector key
        have hh := congrFun hhead key
        have ha := congrFun hargs key
        simp only [setGlobals, unionGlobalBag, Flapjack.bagUnion] at point hh ha ⊢
        omega)
      (by
        intro t l v a b b' hb
        simp [setGlobals, hb])
      (by
        intro t v a b b' hb
        simp [setGlobals, hb])
      (by
        intro t a b c rest b' collected hrest
        simp [setGlobals, hrest, collectArgs_preserves_setGlobals maxApp a b c rest collected])
      (by
        intro t fs fs' b b' hfs hb
        simp [setGlobals, hb, hfs])
      (by
        intro t l v fs b b' hb
        simp [setGlobals, hb])
      (by
        intro t v fs b b' hb
        simp [setGlobals, hb])
      (by
        intro t o xs xs' hs
        simp [setGlobals, hs])
      listStep funsStep ih run


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
  have rel := mapM_rel f (fun e result => esgcFree e → esgcFree result) pointwise source target run
  clear run
  induction rel with
  | nil => simp [esgcFreeList]
  | cons first rest ih =>
    simp only [esgcFreeList] at valid ⊢
    exact ⟨first valid.1, ih valid.2⟩

private theorem fuel_esgcFree (fuel maxApp : Nat) (expression result : Exp)
    (run : introMultiFuel fuel maxApp expression = some result) (valid : esgcFree expression) :
    esgcFree result := by
  induction fuel generalizing expression result with
  | zero => simp [introMultiFuel] at run
  | succ fuel ih =>
    have ihB : ∀ e r, introMultiFuel fuel maxApp e = some r →
        setGlobals r = setGlobals e ∧ (esgcFree e → esgcFree r) := by
      intro e r run
      exact ⟨fuel_globals fuel maxApp e r run, ih e r run⟩
    have listStep (source target : List Exp)
        (run : source.mapM (introMultiFuel fuel maxApp) = some target) :
        elistGlobals target = elistGlobals source ∧ (esgcFreeList source → esgcFreeList target) :=
      ⟨mapM_globals _ source target (fun e result run => (ihB e result run).1) run,
        mapM_esgcFree _ source target (fun e result run => (ihB e result run).2) run⟩
    have funsStep : ∀ source target, source.mapM (collectEntry maxApp fuel) = some target →
        funGlobals target = funGlobals source := by
      intro source target run
      apply mapM_funs_globals (collectEntry maxApp fuel) source target _ run
      intro entry result run
      cases entry with
      | mk arity body =>
        cases found : collectArgs maxApp arity body with
        | mk count rest =>
          cases step : introMultiFuel fuel maxApp rest with
          | none => simp [collectEntry, found, step] at run
          | some body' =>
            have equal : (count, body') = result := by simpa [collectEntry, found, step] using run
            subst result
            exact (ihB rest body' step).1.trans
              (collectArgs_preserves_setGlobals maxApp arity body count rest found)
    exact (introMultiFuel_step (fuel := fuel) (maxApp := maxApp)
      (R := fun e r => setGlobals r = setGlobals e ∧ (esgcFree e → esgcFree r))
      (RList := fun xs ys =>
        elistGlobals ys = elistGlobals xs ∧ (esgcFreeList xs → esgcFreeList ys))
      (RFuns := fun fs fs' => funGlobals fs' = funGlobals fs)
      (fun _ _ => ⟨rfl, fun h => h⟩)
      (by
        intro t c c' y y' z z' hc hy hz
        refine ⟨by simp [setGlobals, hc.1, hy.1, hz.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        exact ⟨hc.2 h.1, hy.2 h.2.1, hz.2 h.2.2⟩)
      (by
        intro t xs xs' b b' hs hb
        refine ⟨by simp [setGlobals, hs.1, hb.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        exact ⟨hs.2 h.1, hb.2 h.2⟩)
      (by
        intro t b b' hb
        refine ⟨by simp [setGlobals, hb.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        exact hb.2 h)
      (by
        intro t b b' h h' hb hh
        refine ⟨by simp [setGlobals, hb.1, hh.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        exact ⟨hb.2 h.1, hh.2 h.2⟩)
      (by
        intro t b b' hb
        refine ⟨by simp [setGlobals, hb.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        exact hb.2 h)
      (by
        intro t k l xs xs' hs
        refine ⟨by simp [setGlobals, hs.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        exact hs.2 h)
      (by
        intro t l b b' xs xs' hb hs
        refine ⟨by simp [setGlobals, hb.1, hs.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        exact ⟨hb.2 h.1, hs.2 h.2⟩)
      (by
        intro t args head argsC headC head' args' collected hlen hhead hargs
        refine ⟨?_, ?_⟩
        · have collector := collectApps_preserves_setGlobals maxApp args head argsC headC collected
          funext key
          have point := congrFun collector key
          have hh := congrFun hhead.1 key
          have ha := congrFun hargs.1 key
          simp only [setGlobals, unionGlobalBag, Flapjack.bagUnion] at point hh ha ⊢
          omega
        · intro h
          simp only [esgcFree] at h ⊢
          have cv := collectApps_preserves_esgcFree maxApp args head argsC headC
            ⟨collected, (esgcFreeList_iff args).mp h.2, h.1⟩
          exact ⟨hhead.2 cv.2, hargs.2 ((esgcFreeList_iff argsC).mpr cv.1)⟩)
      (by
        intro t l v a b b' hb
        refine ⟨by simp [setGlobals, hb.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        simpa [hb.1] using h)
      (by
        intro t v a b b' hb
        refine ⟨by simp [setGlobals, hb.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        simpa [hb.1] using h)
      (by
        intro t a b c rest b' collected hrest
        have coll := collectArgs_preserves_setGlobals maxApp a b c rest collected
        refine ⟨by simp [setGlobals, hrest.1, coll], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        simpa [hrest.1, coll] using h)
      (by
        intro t fs fs' b b' hfs hb
        refine ⟨by simp [setGlobals, hb.1, hfs], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        refine ⟨?_, hb.2 h.2⟩
        rw [hfs]
        exact h.1)
      (by
        intro t l v fs b b' hb
        refine ⟨by simp [setGlobals, hb.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        exact ⟨h.1, hb.2 h.2⟩)
      (by
        intro t v fs b b' hb
        refine ⟨by simp [setGlobals, hb.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        exact ⟨h.1, hb.2 h.2⟩)
      (by
        intro t o xs xs' hs
        refine ⟨by simp [setGlobals, hs.1], ?_⟩
        intro h
        simp only [esgcFree] at h ⊢
        exact hs.2 h)
      listStep funsStep ihB run).2 valid


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
