import Flapjack.Compiler.Backend.Parmove.StepMapInj
import Flapjack.Compiler.Backend.Parmove.InjOnState.Step
import Flapjack.Compiler.Backend.Parmove.FstepMapInj
import Flapjack.Compiler.Backend.Parmove.FstepDstep
import Flapjack.Compiler.Backend.Parmove.DStepsSteps
import Flapjack.Compiler.Backend.Parmove.Invariants.Preservation
import Flapjack.Compiler.Backend.Parmove.PmovFinal
import Mathlib.Data.List.Nodup

/-!
# parmove renaming: `steps_inj_on_state`, `steps_MAP_INJ`, `pmov_MAP_INJ`, `parmove_MAP_INJ`

The renaming theorems of `cakeml/compiler/backend/reg_alloc/parmoveScript.sml`
(1115-1340): a renaming that is injective on the endpoints of a scheduler state
commutes with the scheduler, and on a windmill it commutes with `parmove`.
-/

namespace Flapjack.Compiler.Backend.Parmove

/-- Exact HOL `steps_inj_on_state` (`parmoveScript.sml:1115-1119`). HOL's free
`f` is implicit; `▷*` is `Steps`, the reflexive-transitive closure of `Step`. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_inj_on_state"]
theorem steps_inj_on_state {α β : Type} {f : Option α → Option β} :
    ∀ (s1 s2 : State α), injOnState f s1 ∧ Steps s1 s2 → injOnState f s2 := by
  rintro s1 s2 ⟨h, steps⟩
  induction steps with
  | refl => exact h
  | tail _ step ih => exact stepInjOnState f _ _ step ih

/-- Exact HOL `steps_MAP_INJ` (`parmoveScript.sml:1179-1189`, `[local]`). HOL's
free `f` is implicit. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "steps_MAP_INJ"]
theorem steps_MAP_INJ {α β : Type} {f : Option α → Option β} :
    ∀ (s1 s2 : State α), Steps s1 s2 → injOnState f s1 →
      Steps (mapState f s1) (mapState f s2) := by
  intro s1 s2 steps h
  induction steps with
  | refl => exact Relation.ReflTransGen.refl
  | @tail mid last steps step ih =>
      exact (ih).tail
        (stepMapInj f mid last step (steps_inj_on_state s1 mid ⟨h, steps⟩))

theorem measure_mapState {α β : Type} (f : Option α → Option β) (s : State α) :
    measure (mapState f s) = measure s := by
  rcases s with ⟨p, a, e⟩
  simp [measure, mapState]

/-- Exact HOL `pmov_MAP_INJ` (`parmoveScript.sml:1257-1292`). HOL's free `f` is
implicit; `⊢ p` is `wf p`. The proof follows HOL's `pmov_ind`, as induction on
`pmov`'s termination measure. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "pmov_MAP_INJ"]
theorem pmov_MAP_INJ {α β : Type} [DecidableEq α] [DecidableEq β] {f : Option α → Option β} :
    ∀ p : State α, wf p ∧ injOnState f p → pmov (mapState f p) = mapState f (pmov p) := by
  intro p
  induction p using pmov.induct with
  | case1 state finished =>
      rintro ⟨-, -⟩
      rcases state with ⟨pd, ac, em⟩
      obtain ⟨rfl, rfl⟩ := finished
      have h1 : pmov (([] : List (Move α)), ([] : List (Move α)), em) = ([], [], em) := by
        rw [pmov.eq_def]; simp
      have h2 : pmov (mapState f (([] : List (Move α)), ([] : List (Move α)), em)) =
          mapState f ([], [], em) := by
        rw [pmov.eq_def]; simp [mapState]
      rw [h2, h1]
  | case2 state unfinished ih =>
      rintro ⟨hw, hi⟩
      rcases state with ⟨pd, ac, em⟩
      have hu : ∀ emitted, (pd, ac, em) ≠ ([], [], emitted) := by
        intro emitted h
        simp only [Prod.mk.injEq] at h
        exact unfinished ⟨h.1, h.2.1⟩
      have hsteps : Steps (pd, ac, em) (fstep (pd, ac, em)) :=
        dsteps_steps _ _ (Relation.ReflTransGen.single (fstepDstep _ hu)) hw
      have hw' := wf_steps _ _ ⟨hw, hsteps⟩
      have hi' := steps_inj_on_state _ _ ⟨hi, hsteps⟩
      have hun' : ¬ ((mapState f (pd, ac, em)).1 = [] ∧ (mapState f (pd, ac, em)).2.1 = []) := by
        simpa [mapState] using unfinished
      rw [pmov.eq_def, dif_neg hun', fstepMapInj f _ hi, ih ⟨hw', hi'⟩, pmov.eq_def (pd, ac, em),
        dif_neg unfinished]

/-- Exact HOL `parmove_MAP_INJ` (`parmoveScript.sml:1294-1333`). HOL's free `f`
and `ls` are implicit; `f ## f` is `Prod.map f f` and `OPTION_MAP` is
`Option.map`. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parmove_MAP_INJ"]
theorem parmove_MAP_INJ {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    {ls : List (α × α)} :
    (let ls1 := ls.map Prod.fst ++ ls.map Prod.snd
     ∀ x y, x ∈ ls1 ∧ y ∈ ls1 ∧ f x = f y → x = y) ∧ windmill ls →
    parmove (ls.map (Prod.map f f)) = (parmove ls).map (Prod.map (Option.map f) (Option.map f)) := by
  rintro ⟨hinj, hwm⟩
  let p : State α := (ls.map (fun move => (some move.1, some move.2)), [], [])
  have hmp : ((ls.map (Prod.map f f)).map (fun move => (some move.1, some move.2)),
      ([] : List (Move β)), ([] : List (Move β))) = mapState (Option.map f) p := by
    simp [p, mapState, List.map_map, Function.comp_def]
  have hi : injOnState (Option.map f) p := by
    refine ⟨?_, ?_⟩
    · rintro x y ⟨hx, hy, hxy⟩
      simp only [p, stateToList, List.append_nil, List.map_map, List.mem_append, List.mem_map,
        Function.comp_def] at hx hy
      rcases hx with ⟨⟨a, b⟩, ha, rfl⟩ | ⟨⟨a, b⟩, ha, rfl⟩ <;>
        rcases hy with ⟨⟨c, d⟩, hc, rfl⟩ | ⟨⟨c, d⟩, hc, rfl⟩ <;>
        simp only [Option.map_some, Option.some.injEq] at hxy ⊢ <;>
        exact hinj _ _ ⟨by simp only [List.mem_append, List.mem_map]; first
          | exact Or.inl ⟨_, ha, rfl⟩ | exact Or.inr ⟨_, ha, rfl⟩,
          by simp only [List.mem_append, List.mem_map]; first
          | exact Or.inl ⟨_, hc, rfl⟩ | exact Or.inr ⟨_, hc, rfl⟩, hxy⟩
    · intro x; cases x <;> simp
  have hw : wf p := by
    apply wf_init
    refine ⟨?_, ?_, ?_⟩
    · show ((ls.map (fun move => (some move.1, some move.2))).map Prod.fst).Nodup
      simpa [List.map_map, Function.comp_def] using
        (List.Nodup.map (f := Option.some) (fun a b h => Option.some.inj h) hwm)
    · intro move hm
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm; rfl
    · intro move hm
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm; rfl
  have key := pmov_MAP_INJ (f := Option.map f) p ⟨hw, hi⟩
  simp only [parmove]
  rw [hmp, key]
  obtain ⟨em, hem⟩ := pmov_final p
  rw [hem]
  simp [mapState, List.map_reverse]

end Flapjack.Compiler.Backend.Parmove
