module

public import Flapjack.Compiler.Inference.Unify.ComputationalWalk
public import Flapjack.Compiler.Inference.Unify.Walkstar.Induction

@[expose] public section

/-! Agreement of executable occurrence checking with normalized variables. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

open Classical in
/-- A worklist continuation is preserved by the normalized occurrence of its head. -/
private theorem occursContinuation (s : Spt InferT) (hw : cwfs s) (n : Nat) :
    ∀ t ts rest, occursWorkPartial s n ((t :: ts) :: rest) =
      if tVars (tWalkstar (sp2fm s) t) n then some true else occursWorkPartial s n (ts :: rest) := by
  have hws : tWfs (sp2fm s) := by
    change WellFounded (vR ((sp2fm s).map2 (fun p => encodeInferT p.2)))
    exact wfCvwalkR s n hw
  apply tWalkstarInd (sp2fm s) hws
  intro t ih ts rest
  have he := walkExecutableCorrect s hw t
  change walkExecutable s t = some (tWalk (sp2fm s) t) at he
  rw [occursWorkPartial.eq_3, he, walkstarEqn (sp2fm s) hws t]
  cases found : tWalk (sp2fm s) t with
  | varDb k => simp [tVars, encodeInferT, vars]
  | uvar u => simp [tVars, encodeInferT, vars]
  | app xs tc =>
    change occursWorkPartial s n (xs :: ts :: rest) =
      if tVars (.app (xs.map (tWalkstar (sp2fm s))) tc) n then some true
      else occursWorkPartial s n (ts :: rest)
    have listStep : ∀ ls : List InferT,
        (∀ a ∈ ls, ∀ tail rest, occursWorkPartial s n ((a :: tail) :: rest) =
          if tVars (tWalkstar (sp2fm s) a) n then some true else occursWorkPartial s n (tail :: rest)) →
        ∀ rest, occursWorkPartial s n (ls :: rest) =
          if ∃ a ∈ ls, tVars (tWalkstar (sp2fm s) a) n then some true else occursWorkPartial s n rest := by
      intro ls
      induction ls with
      | nil => intro h rest; simp [occursWorkPartial.eq_2]
      | cons a ls rec =>
        intro h rest
        have ha := h a (by simp)
        have hl := rec (by intro q hq; exact h q (by simp [hq])) rest
        rw [ha ls rest, hl]
        by_cases hav : tVars (tWalkstar (sp2fm s) a) n <;> simp [hav]
    have hs : ∀ a ∈ xs, ∀ tail rest, occursWorkPartial s n ((a :: tail) :: rest) =
        if tVars (tWalkstar (sp2fm s) a) n then some true else occursWorkPartial s n (tail :: rest) := by
      intro a ha
      exact ih xs tc a ⟨found, ha⟩
    rw [listStep xs hs (ts :: rest)]
    congr 1
    rw [tVarsEqn.2.1]
    apply propext
    change (∃ a ∈ xs, tVars (tWalkstar (sp2fm s) a) n) ↔
      ∃ p : Nat → Prop, (∃ a, a ∈ xs.map (tWalkstar (sp2fm s)) ∧ tVars a = p) ∧ p n
    simp only [List.mem_map]
    constructor
    · rintro ⟨a, ha, hv⟩
      exact ⟨tVars (tWalkstar (sp2fm s) a), ⟨tWalkstar (sp2fm s) a, ⟨a, ha, rfl⟩, rfl⟩, hv⟩
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, hv⟩
      exact ⟨a, ha, hv⟩

/-- On well-formed substitutions the executed worklist terminates and returns
    true exactly when an input type contains the variable after normalization.
    This connects execution to CakeML's occurrence-correctness theorem; the
    additional `Option` is not a claimed HOL declaration. -/
theorem occursWorkListCorrect (s : Spt InferT) (hw : cwfs s) (n : Nat) :
    ∀ ts, ∃ b, occursWorkPartial s n [ts] = some b ∧
      (b = true ↔ ∃ t ∈ ts, tVars (tWalkstar (sp2fm s) t) n) := by
  classical
  have listStep : ∀ ts rest, occursWorkPartial s n (ts :: rest) =
      if ∃ t ∈ ts, tVars (tWalkstar (sp2fm s) t) n then some true else occursWorkPartial s n rest := by
    intro ts
    induction ts with
    | nil => intro rest; simp [occursWorkPartial.eq_2]
    | cons t ts ih =>
      intro rest
      rw [occursContinuation s hw n t ts rest, ih rest]
      by_cases ht : tVars (tWalkstar (sp2fm s) t) n <;> simp [ht]
  intro ts
  rw [listStep ts [], occursWorkPartial.eq_1]
  by_cases h : ∃ t ∈ ts, tVars (tWalkstar (sp2fm s) t) n
  · exact ⟨true, by simp [h], by simp [h]⟩
  · exact ⟨false, by simp [h], by simp [h]⟩

end Flapjack.Compiler.Inference.Unify
