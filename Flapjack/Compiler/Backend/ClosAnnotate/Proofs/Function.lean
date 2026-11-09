import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Control
import Flapjack.Compiler.Backend.DbVars.Proofs.Lookup
import Flapjack.Misc.Sptree.ToAList

/-! Closure creation for the proof-side annotation simulation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.Compiler.Backend.DbVars

/-- Selecting only in-range indices from an environment succeeds. -/
theorem lookupVars_exists {α : Type} (indices : List Nat) (env : List α)
    (bounds : ∀ n ∈ indices, n < env.length) : ∃ values, lookupVars indices env = some values := by
  induction indices with
  | nil => exact ⟨[], rfl⟩
  | cons n rest ih =>
    have bound : n < env.length := bounds n (by simp)
    have tailBounds : ∀ i ∈ rest, i < env.length := by
      intro i member
      exact bounds i (by simp [member])
    obtain ⟨values, tailRun⟩ := ih tailBounds
    have selected : env[n]? = some env[n] := List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
    exact ⟨env[n] :: values, by simp [lookupVars, selected, tailRun]⟩

/-- Creating a closure captures a related compact environment. This candidate
simulation is untagged while its evaluator and carriers await HOL review. -/
theorem evaluate_fn {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp) :
    EvalSimulation (C := C) (F := F) [.fn name location selected arity body] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have safeParts : selected = none ∧ everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  have selectedNone := safeParts.1
  subst selected
  let live := varsToList (.shift arity (altFree [body]).2)
  have distinct : live.Nodup := sptAllDistinctMapFstToAList _
  have liveVars : ∀ n ∈ live, EnvOk m l index env nextEnv n := by
    intro n member
    apply vars n
    rw [altFv_fn]
    have present := (memVarsToList n (.shift arity (altFree [body]).2)).mp member
    simpa [altFv, hasVar] using present
  have bounds : ∀ n ∈ (live.filter (· < m + l)).map (getVar m l index), n < nextEnv.length := by
    intro n member
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    have memberParts := List.mem_filter.mp originalMember
    have tracked : original < l + m := by simp only [decide_eq_true_eq] at memberParts; omega
    exact (envOk_getVar m l index env nextEnv original (liveVars original memberParts.1) tracked).2.1
  obtain ⟨captured, captureRun⟩ := lookupVars_exists _ nextEnv bounds
  by_cases valid : arity ≤ source.maxApp ∧ arity ≠ 0
  · have targetValid : arity ≤ target.maxApp ∧ arity ≠ 0 := by simpa [← states.2.2.1] using valid
    simp [evaluate, valid] at run
    obtain ⟨rfl, rfl⟩ := run
    let nextBody := shiftSing (altFreeSing body).1 (m + l) arity
      (shiftedEnv 0 (live.filter (· < m + l)))
    have bodyRel : ValueRel (.closure location [] env arity body) (.closure location [] captured arity nextBody) := by
      apply ValueRel.closure location [] [] env captured arity (m + l) body nextBody
        (shiftedEnv 0 (live.filter (· < m + l)))
      · simp [nextBody, shiftSource_eq_shiftList, altFreeSource_eq_altFree, altFree_singleton, shiftList]
      · intro n ⟨present, above⟩
        have member : n - arity ∈ live := by
          apply (memVarsToList _ _).mpr
          have equal : n - arity + arity = n := by omega
          simpa [altFvSource_eq_altFv, altFv, hasVar, equal] using present
        exact envOk_shiftedEnv m l index env nextEnv captured (n - arity) live
          (liveVars _ member) member distinct captureRun
      · exact safeParts.2
      · omega
      · exact .nil
    refine ⟨.val [.closure location [] captured arity nextBody], target, ?_, .cons bodyRel .nil, states⟩
    rw [altFree_fn]
    simp only [altFree_singleton, Flapjack.holHd, shiftList, shiftSing]
    have captureRun' : lookupVars
        ((varsToList (.shift arity (altFreeSing body).2)).filter (· < m + l) |>.map (getVar m l index))
        nextEnv = some captured := by
      simpa [live, altFree_singleton] using captureRun
    simp [evaluate, targetValid, captureRun', live, nextBody, altFree_singleton]
  · simp [evaluate, valid] at run
    exact False.elim (noType run.1.symm)

end Flapjack.Compiler.Backend.ClosAnnotate
