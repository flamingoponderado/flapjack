module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Accumulator

@[expose] public section

/-! Appending auxiliary-code suffixes during closure compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private abbrev Aux' := List (Nat × Nat × Bvl.Exp)

mutual
/-- Flapjack infrastructure: the singleton case needed for mutual list induction. -/
private theorem expAppend (m : Nat) (e : ClosLang.Exp) (a s : Aux') :
    compileExpHOL m e (a ++ s) =
      let (r, b) := compileExpHOL m e a
      (r, b ++ s) := by
  cases e with
  | var t n => simp [compileExpHOL]
  | ifThenElse t x y z =>
    simp [compileExpHOL, expAppend m x, expAppend m y, expAppend m z]
  | «let» t xs x =>
    simp [compileExpHOL, listAppend m xs, expAppend m x]
  | raise t x | tick t x =>
    simp [compileExpHOL, expAppend m x]
  | handle t x y =>
    simp [compileExpHOL, expAppend m x, expAppend m y]
  | op t op xs | call t _ _ xs =>
    simp [compileExpHOL, listAppend m xs]
  | app t loc x xs =>
    simp [compileExpHOL, expAppend m x, listAppend m xs]
  | fn name loc vs args x =>
    simp [compileExpHOL, expAppend m x, List.cons_append]
  | letrec names loc vs fns x =>
    cases fns with
    | nil => simpa [compileExpHOL] using expAppend m x a s
    | cons first rest =>
      cases rest with
      | nil =>
        obtain ⟨arity, body⟩ := first
        have step (entry : Nat × Nat × Bvl.Exp) (tail : Aux') :
            compileExpHOL m x (entry :: (tail ++ s)) =
              let (r, b) := compileExpHOL m x (entry :: tail)
              (r, b ++ s) := by
          simpa only [List.cons_append] using expAppend m x (entry :: tail) s
        simp [compileExpHOL, expAppend m body, step]
      | cons second tail =>
        simp [compileExpHOL, funsAppend m (first :: second :: tail),
          expAppend m x, buildAux_append_aux]
termination_by sizeOf e
decreasing_by all_goals subst_vars; simp_wf <;> omega

/-- Flapjack infrastructure: the list reformulation used to prove the HOL theorem. -/
private theorem listAppend (m : Nat) (es : List ClosLang.Exp) (a s : Aux') :
    compileExpListHOL m es (a ++ s) =
      let (r, b) := compileExpListHOL m es a
      (r, b ++ s) := by
  cases es with
  | nil => simp [compileExpListHOL]
  | cons e es =>
    simp [compileExpListHOL, expAppend m e, listAppend m es]
termination_by sizeOf es
decreasing_by all_goals simp_wf <;> omega

/-- Flapjack infrastructure: recursive-body lists participate in the mutual induction. -/
private theorem funsAppend (m : Nat) (fs : List (Nat × ClosLang.Exp)) (a s : Aux') :
    compileExpFunsHOL m fs (a ++ s) =
      let (r, b) := compileExpFunsHOL m fs a
      (r, b ++ s) := by
  cases fs with
  | nil => simp [compileExpFunsHOL]
  | cons f fs =>
    obtain ⟨arity, body⟩ := f
    simp [compileExpFunsHOL, expAppend m body, funsAppend m fs]
termination_by sizeOf fs
decreasing_by all_goals simp_wf <;> omega
end

/-- Appending a suffix to the input accumulator appends it to the compiled result. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_append_aux"]
theorem compileExps_append_aux (extra : List (Nat × Nat × Bvl.Exp)) (m : Nat)
    (es : List ClosLang.Exp) (aux : List (Nat × Nat × Bvl.Exp)) :
    compileExpsHOL m es (aux ++ extra) =
      let (out, rest) := compileExpsHOL m es aux
      (out, rest ++ extra) := by
  simp only [compileExps_eq_list]
  exact listAppend m es aux extra

/-- The initial accumulator is appended to the result compiled from empty. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_eq_append"]
theorem compileExps_eq_append (m : Nat) (es : List ClosLang.Exp)
    (aux : List (Nat × Nat × Bvl.Exp)) :
    compileExpsHOL m es aux =
      let (out, rest) := compileExpsHOL m es []
      (out, rest ++ aux) := by
  simpa using compileExps_append_aux aux m es []

end Flapjack.Compiler.Backend.ClosToBvl
