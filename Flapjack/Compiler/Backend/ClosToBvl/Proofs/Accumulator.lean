import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ExpsEquivalence
import Flapjack.Compiler.Backend.ClosToBvl.Layout.Auxiliary

/-! Auxiliary-code accumulator properties of closure expression compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private abbrev Aux := List (Nat × Nat × Bvl.Exp)

mutual
/-- The source-shaped singleton compiler preserves its input accumulator. -/
theorem compileExp_auxSuffix (maxApp : Nat) (expression : ClosLang.Exp) (aux : Aux) :
    aux <:+ (compileExpHOL maxApp expression aux).2 := by
  cases expression with
  | var trace index => simp [compileExpHOL]
  | ifThenElse trace x y z =>
      cases hx : compileExpHOL maxApp x aux with
      | mk a aux1 =>
        have p1 := compileExp_auxSuffix maxApp x aux
        rw [hx] at p1
        cases hy : compileExpHOL maxApp y aux1 with
        | mk b aux2 =>
          have p2 := compileExp_auxSuffix maxApp y aux1
          rw [hy] at p2
          cases hz : compileExpHOL maxApp z aux2 with
          | mk c aux3 =>
            have p3 := compileExp_auxSuffix maxApp z aux2
            rw [hz] at p3
            simpa [compileExpHOL, hx, hy, hz] using p1.trans (p2.trans p3)
  | «let» trace xs body =>
      cases hx : compileExpListHOL maxApp xs aux with
      | mk a aux1 =>
        have p1 := compileExpList_auxSuffix maxApp xs aux
        rw [hx] at p1
        cases hb : compileExpHOL maxApp body aux1 with
        | mk b aux2 =>
          have p2 := compileExp_auxSuffix maxApp body aux1
          rw [hb] at p2
          simpa [compileExpHOL, hx, hb] using p1.trans p2
  | raise trace x | tick trace x =>
      cases hx : compileExpHOL maxApp x aux with
      | mk a aux1 =>
        have p := compileExp_auxSuffix maxApp x aux
        rw [hx] at p
        simpa [compileExpHOL, hx] using p
  | handle trace x y =>
      cases hx : compileExpHOL maxApp x aux with
      | mk a aux1 =>
        have p1 := compileExp_auxSuffix maxApp x aux
        rw [hx] at p1
        cases hy : compileExpHOL maxApp y aux1 with
        | mk b aux2 =>
          have p2 := compileExp_auxSuffix maxApp y aux1
          rw [hy] at p2
          simpa [compileExpHOL, hx, hy] using p1.trans p2
  | op trace op xs | call trace _ _ xs =>
      cases hx : compileExpListHOL maxApp xs aux with
      | mk a aux1 =>
        have p := compileExpList_auxSuffix maxApp xs aux
        rw [hx] at p
        simpa [compileExpHOL, hx] using p
  | app trace location x xs =>
      cases hx : compileExpHOL maxApp x aux with
      | mk a aux1 =>
        have p1 := compileExp_auxSuffix maxApp x aux
        rw [hx] at p1
        cases hs : compileExpListHOL maxApp xs aux1 with
        | mk b aux2 =>
          have p2 := compileExpList_auxSuffix maxApp xs aux1
          rw [hs] at p2
          simpa [compileExpHOL, hx, hs] using p1.trans p2
  | fn trace location vars args body =>
      cases hb : compileExpHOL maxApp body aux with
      | mk b aux1 =>
        have p := compileExp_auxSuffix maxApp body aux
        rw [hb] at p
        simpa [compileExpHOL, hb] using p.trans (List.suffix_cons _ aux1)
  | letrec names location vars functions body =>
      cases functions with
      | nil => simpa [compileExpHOL] using compileExp_auxSuffix maxApp body aux
      | cons first rest =>
        cases rest with
        | nil =>
          obtain ⟨arity, functionBody⟩ := first
          cases hf : compileExpHOL maxApp functionBody aux with
          | mk compiled aux1 =>
            have p1 := compileExp_auxSuffix maxApp functionBody aux
            rw [hf] at p1
            let entry := (location.getD 0 + numStubs maxApp, arity + 1,
              Bvl.Exp.let ((List.range arity).map Bvl.Exp.var ++ [.var arity] ++
                freeLet (.var arity) (vars.getD []).length) compiled)
            cases hb : compileExpHOL maxApp body (entry :: aux1) with
            | mk result aux2 =>
              have p2 := compileExp_auxSuffix maxApp body (entry :: aux1)
              rw [hb] at p2
              have p := p1.trans ((List.suffix_cons entry aux1).trans p2)
              simp only [entry, List.append_assoc, List.singleton_append] at hb
              simpa [compileExpHOL, hf, hb, entry] using p
        | cons second rest =>
          cases hf : compileExpFunsHOL maxApp (first :: second :: rest) aux with
          | mk compiled aux1 =>
            have p1 := compileExpFuns_auxSuffix maxApp (first :: second :: rest) aux
            rw [hf] at p1
            let entries := compiled.map (fun (args, b) =>
              codeForReccCase ((first :: second :: rest).length + (vars.getD []).length) args b)
            let nextAux := (buildAux (location.getD 0 + numStubs maxApp) entries aux1).2
            have p2 : aux1 <:+ nextAux := by
              obtain ⟨added, h⟩ := buildAux_acc entries (location.getD 0 + numStubs maxApp) aux1
              exact ⟨added, h.symm⟩
            cases hb : compileExpHOL maxApp body nextAux with
            | mk result aux2 =>
              have p3 := compileExp_auxSuffix maxApp body nextAux
              rw [hb] at p3
              have p := p1.trans (p2.trans p3)
              simp only [nextAux, entries, List.length_cons] at hb
              simpa [compileExpHOL, hf, hb, nextAux, entries] using p
termination_by sizeOf expression
decreasing_by all_goals simp_wf <;> omega

/-- List compilation preserves the input auxiliary-code suffix. -/
theorem compileExpList_auxSuffix (maxApp : Nat) (expressions : List ClosLang.Exp) (aux : Aux) :
    aux <:+ (compileExpListHOL maxApp expressions aux).2 := by
  cases expressions with
  | nil => simp [compileExpListHOL]
  | cons expression rest =>
      cases hx : compileExpHOL maxApp expression aux with
      | mk compiled aux1 =>
        have p1 := compileExp_auxSuffix maxApp expression aux
        rw [hx] at p1
        cases hs : compileExpListHOL maxApp rest aux1 with
        | mk compiledRest aux2 =>
          have p2 := compileExpList_auxSuffix maxApp rest aux1
          rw [hs] at p2
          simpa [compileExpListHOL, hx, hs] using p1.trans p2
termination_by sizeOf expressions
decreasing_by all_goals simp_wf <;> omega

/-- Compiling the bodies of a recursive group also preserves the suffix. -/
theorem compileExpFuns_auxSuffix (maxApp : Nat) (functions : List (Nat × ClosLang.Exp)) (aux : Aux) :
    aux <:+ (compileExpFunsHOL maxApp functions aux).2 := by
  cases functions with
  | nil => simp [compileExpFunsHOL]
  | cons first rest =>
      obtain ⟨arity, body⟩ := first
      cases hx : compileExpHOL maxApp body aux with
      | mk compiled aux1 =>
        have p1 := compileExp_auxSuffix maxApp body aux
        rw [hx] at p1
        cases hs : compileExpFunsHOL maxApp rest aux1 with
        | mk compiledRest aux2 =>
          have p2 := compileExpFuns_auxSuffix maxApp rest aux1
          rw [hs] at p2
          simpa [compileExpFunsHOL, hx, hs] using p1.trans p2
termination_by sizeOf functions
decreasing_by all_goals simp_wf <;> omega
end

/-- The reformulated list compiler emits exactly one expression per input. -/
theorem compileExpList_length (maxApp : Nat) (expressions : List ClosLang.Exp) (aux : Aux) :
    (compileExpListHOL maxApp expressions aux).1.length = expressions.length := by
  induction expressions generalizing aux with
  | nil => simp [compileExpListHOL]
  | cons expression rest ih =>
      cases first : compileExpHOL maxApp expression aux with
      | mk compiled aux1 =>
        cases tail : compileExpListHOL maxApp rest aux1 with
        | mk compiledRest aux2 =>
          have length := ih aux1
          rw [tail] at length
          simpa [compileExpListHOL, first, tail] using congrArg Nat.succ length

/-- The original list compiler emits one expression per input and retains its
initial accumulator as a suffix of the output accumulator. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_exps_acc"]
theorem compileExps_acc (maxApp : Nat) (expressions : List ClosLang.Exp) (aux : Aux) :
    let (compiled, finalAux) := compileExpsHOL maxApp expressions aux
    compiled.length = expressions.length ∧ ∃ added, finalAux = added ++ aux := by
  rw [compileExps_eq_list]
  cases result : compileExpListHOL maxApp expressions aux with
  | mk compiled finalAux =>
      have length := compileExpList_length maxApp expressions aux
      have suffix := compileExpList_auxSuffix maxApp expressions aux
      rw [result] at length suffix
      obtain ⟨added, equal⟩ := suffix
      exact ⟨length, added, equal.symm⟩

/-- The expression-count component of the accumulator theorem. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_exps_LENGTH"]
theorem compileExps_length (maxApp : Nat) (expressions : List ClosLang.Exp) (aux : Aux)
    (compiled : List Bvl.Exp) (finalAux : Aux)
    (run : compileExpsHOL maxApp expressions aux = (compiled, finalAux)) :
    compiled.length = expressions.length := by
  have invariant := compileExps_acc maxApp expressions aux
  rw [run] at invariant
  exact invariant.1

end Flapjack.Compiler.Backend.ClosToBvl
