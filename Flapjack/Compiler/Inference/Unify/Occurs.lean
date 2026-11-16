module

public import Flapjack.Compiler.Inference.Unify.ComputationalWalk
public import Flapjack.Compiler.Inference.Unify.Walkstar.Induction

@[expose] public section

/-! Agreement of executable occurrence checking with normalized variables. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- On well-formed substitutions the executed occurs check terminates and
    decides membership in the normalized type's variables. This connects the
    partial executable result to the HOL occurrence predicate; the additional
    `Option` is execution infrastructure, not a claimed HOL declaration. -/
theorem occursPartialCorrect (s : Spt InferT) (hw : cwfs s) (n : Nat) :
    ∀ t, ∃ b, occursPartial s n t = some b ∧
      (b = true ↔ tVars (tWalkstar (sp2fm s) t) n) := by
  classical
  have hws : tWfs (sp2fm s) := by
    change WellFounded (vR ((sp2fm s).map2 (fun p => encodeInferT p.2)))
    exact wfCvwalkR s n hw
  have continuation : ∀ t ts rest, occursWorkPartial s n ((t :: ts) :: rest) =
      if tVars (tWalkstar (sp2fm s) t) n then some true else occursWorkPartial s n (ts :: rest) := by
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
  intro t
  have h := continuation t [] []
  rw [occursWorkPartial.eq_2, occursWorkPartial.eq_1] at h
  by_cases ht : tVars (tWalkstar (sp2fm s) t) n
  · refine ⟨true, ?_, ?_⟩
    · simpa [occursPartial, ht] using h
    · simp [ht]
  · refine ⟨false, ?_, ?_⟩
    · simpa [occursPartial, ht] using h
    · simp [ht]

end Flapjack.Compiler.Inference.Unify
