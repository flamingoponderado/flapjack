import Flapjack.Compiler.Backend.ClosToBvl.SourceCompile
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Total

/-! Correspondence between total source-shaped conversion and the executed
checked closure-to-BVL converter. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

mutual
/-- The executed singleton converter returns the original total result. -/
theorem compileExp_checked_eq (maxApp : Nat) (expression : ClosLang.Exp)
    (aux : List (Nat × Nat × Bvl.Exp)) :
    compileExp? maxApp expression aux = some (compileExpHOL maxApp expression aux) := by
  cases expression with
  | var t v => simp [compileExp?, compileExpHOL]
  | ifThenElse t x y z =>
    cases hx : compileExpHOL maxApp x aux with
    | mk a aux1 =>
      have cx := compileExp_checked_eq maxApp x aux
      rw [hx] at cx
      cases hy : compileExpHOL maxApp y aux1 with
      | mk b aux2 =>
        have cy := compileExp_checked_eq maxApp y aux1
        rw [hy] at cy
        cases hz : compileExpHOL maxApp z aux2 with
        | mk c aux3 =>
          have cz := compileExp_checked_eq maxApp z aux2
          rw [hz] at cz
          simp [compileExp?, compileExpHOL, cx, cy, cz, hx, hy, hz]
  | «let» t xs body =>
    cases hx : compileExpListHOL maxApp xs aux with
    | mk a aux1 =>
      have cx := compileExpList_checked_eq maxApp xs aux
      rw [hx] at cx
      cases hb : compileExpHOL maxApp body aux1 with
      | mk b aux2 =>
        have cb := compileExp_checked_eq maxApp body aux1
        rw [hb] at cb
        simp [compileExp?, compileExpHOL, cx, cb, hx, hb]
  | raise t x | tick t x =>
    cases hx : compileExpHOL maxApp x aux with
    | mk a aux1 =>
      have cx := compileExp_checked_eq maxApp x aux
      rw [hx] at cx
      simp [compileExp?, compileExpHOL, cx, hx]
  | handle t x y =>
    cases hx : compileExpHOL maxApp x aux with
    | mk a aux1 =>
      have cx := compileExp_checked_eq maxApp x aux
      rw [hx] at cx
      cases hy : compileExpHOL maxApp y aux1 with
      | mk b aux2 =>
        have cy := compileExp_checked_eq maxApp y aux1
        rw [hy] at cy
        simp [compileExp?, compileExpHOL, cx, cy, hx, hy]
  | op t op xs | call t _ _ xs =>
    cases hx : compileExpListHOL maxApp xs aux with
    | mk a aux1 =>
      have cx := compileExpList_checked_eq maxApp xs aux
      rw [hx] at cx
      simp [compileExp?, compileExpHOL, cx, hx] <;> rfl
  | app t loc x xs =>
    cases hx : compileExpHOL maxApp x aux with
    | mk a aux1 =>
      have cx := compileExp_checked_eq maxApp x aux
      rw [hx] at cx
      cases hs : compileExpListHOL maxApp xs aux1 with
      | mk b aux2 =>
        have cs := compileExpList_checked_eq maxApp xs aux1
        rw [hs] at cs
        simp [compileExp?, compileExpHOL, cx, cs, hx, hs] <;> rfl
  | fn t loc vs args x =>
    cases hx : compileExpHOL maxApp x aux with
    | mk a aux1 =>
      have cx := compileExp_checked_eq maxApp x aux
      rw [hx] at cx
      simp [compileExp?, compileExpHOL, cx, hx]
  | letrec names loc vs fs body =>
    cases fs with
    | nil => simpa [compileExp?, compileExpHOL] using compileExp_checked_eq maxApp body aux
    | cons first rest =>
      cases rest with
      | nil =>
        obtain ⟨arity, f⟩ := first
        cases hf : compileExpHOL maxApp f aux with
        | mk compiled aux1 =>
          have cf := compileExp_checked_eq maxApp f aux
          rw [hf] at cf
          let entry := (loc.getD 0 + numStubs maxApp, arity + 1,
            Bvl.Exp.let ((List.range arity).map Bvl.Exp.var ++ [.var arity] ++
              freeLet (.var arity) (vs.getD []).length) compiled)
          cases hb : compileExpHOL maxApp body (entry :: aux1) with
          | mk result aux2 =>
            have cb := compileExp_checked_eq maxApp body (entry :: aux1)
            rw [hb] at cb
            simp only [entry, List.append_assoc, List.singleton_append] at cb hb
            simp [compileExp?, compileExpHOL, cf, cb, hf, hb] <;> rfl
      | cons second rest =>
        cases hf : compileExpFunsHOL maxApp (first :: second :: rest) aux with
        | mk compiled aux1 =>
          have cf := compileExpFuns_checked_eq maxApp (first :: second :: rest) aux
          rw [hf] at cf
          let cases := compiled.map (fun (args, b) =>
            codeForReccCase ((first :: second :: rest).length + (vs.getD []).length) args b)
          let nextAux := (buildAux (loc.getD 0 + numStubs maxApp) cases aux1).2
          cases hb : compileExpHOL maxApp body nextAux with
          | mk result aux2 =>
            have cb := compileExp_checked_eq maxApp body nextAux
            rw [hb] at cb
            have check := buildReccLets_checked_eq ((first :: second :: rest).map Prod.fst)
              (vs.getD []) (loc.getD 0 + numStubs maxApp) result (by simp)
            simp only [nextAux, cases, List.length_cons] at cb hb
            simp only [List.length_map, List.length_cons, List.map_cons] at check
            simp [compileExp?, compileExpHOL, cf, cb, hf, hb, check] <;> rfl
termination_by sizeOf expression
decreasing_by all_goals simp_wf <;> omega

/-- The executed list converter returns the original total result. -/
theorem compileExpList_checked_eq (maxApp : Nat) (expressions : List ClosLang.Exp)
    (aux : List (Nat × Nat × Bvl.Exp)) :
    compileExpList? maxApp expressions aux = some (compileExpListHOL maxApp expressions aux) := by
  cases expressions with
  | nil => simp [compileExpList?, compileExpListHOL]
  | cons e es =>
    cases hx : compileExpHOL maxApp e aux with
    | mk a aux1 =>
      have cx := compileExp_checked_eq maxApp e aux
      rw [hx] at cx
      cases hs : compileExpListHOL maxApp es aux1 with
      | mk b aux2 =>
        have cs := compileExpList_checked_eq maxApp es aux1
        rw [hs] at cs
        simp [compileExpList?, compileExpListHOL, cx, cs, hx, hs]
termination_by sizeOf expressions
decreasing_by all_goals simp_wf <;> omega

/-- The checked recursive-group traversal matches the source-shaped helper. -/
theorem compileExpFuns_checked_eq (maxApp : Nat) (functions : List (Nat × ClosLang.Exp))
    (aux : List (Nat × Nat × Bvl.Exp)) :
    compileExpFuns? maxApp functions aux = some (compileExpFunsHOL maxApp functions aux) := by
  cases functions with
  | nil => simp [compileExpFuns?, compileExpFunsHOL]
  | cons first rest =>
    obtain ⟨arity, body⟩ := first
    cases hx : compileExpHOL maxApp body aux with
    | mk a aux1 =>
      have cx := compileExp_checked_eq maxApp body aux
      rw [hx] at cx
      cases hs : compileExpFunsHOL maxApp rest aux1 with
      | mk b aux2 =>
        have cs := compileExpFuns_checked_eq maxApp rest aux1
        rw [hs] at cs
        simp [compileExpFuns?, compileExpFunsHOL, cx, cs, hx, hs]
termination_by sizeOf functions
decreasing_by all_goals simp_wf <;> omega
end

/-- The recursive-group helper implements the source's mapped bodies followed
by MAP2 over the original arities. -/
theorem compileExpFunsHOL_eq_map (maxApp : Nat) (functions : List (Nat × ClosLang.Exp))
    (aux : List (Nat × Nat × Bvl.Exp)) :
    compileExpFunsHOL maxApp functions aux =
      let (bodies, aux') := compileExpListHOL maxApp (functions.map Prod.snd) aux
      ((functions.map Prod.fst).zip bodies, aux') := by
  induction functions generalizing aux with
  | nil => simp [compileExpFunsHOL, compileExpListHOL]
  | cons first rest ih =>
    obtain ⟨arity, body⟩ := first
    cases h : compileExpHOL maxApp body aux with
    | mk b aux1 =>
      have restEq := ih aux1
      cases hr : compileExpListHOL maxApp (rest.map Prod.snd) aux1 with
      | mk bs aux2 =>
        simp only [hr] at restEq
        simp [compileExpFunsHOL, compileExpListHOL, h, restEq, hr]

private theorem map_zip_eq_zipWith {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) :
    (xs.zip ys).map (fun (x, y) => f x y) = List.zipWith f xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih => cases ys <;> simp [ih]

/-- The recursive-group code cases are exactly the source's MAP2 of original
arities and the separately compiled function bodies. -/
theorem compileExpFunsHOL_cases (maxApp n : Nat) (functions : List (Nat × ClosLang.Exp))
    (aux : List (Nat × Nat × Bvl.Exp)) :
    ((compileExpFunsHOL maxApp functions aux).1.map (fun (arity, body) => codeForReccCase n arity body)) =
      List.zipWith (codeForReccCase n) (functions.map Prod.fst)
        (compileExpListHOL maxApp (functions.map Prod.snd) aux).1 := by
  rw [compileExpFunsHOL_eq_map]
  cases h : compileExpListHOL maxApp (functions.map Prod.snd) aux with
  | mk bodies aux' => simp [map_zip_eq_zipWith]

/-- The executed program converter returns the source-shaped result. -/
theorem compileProg_checked_eq (maxApp : Nat) (prog : List (Nat × Nat × ClosLang.Exp)) :
    compileProg? maxApp prog = some (compileProgHOL maxApp prog) := by
  cases h : compileExpListHOL maxApp (prog.map (fun (_, _, exp) => exp)) [] with
  | mk bodies aux =>
    have checked := compileExpList_checked_eq maxApp (prog.map (fun (_, _, exp) => exp)) []
    rw [h] at checked
    simp [compileProg?, compileProgHOL, checked, h]

end Flapjack.Compiler.Backend.ClosToBvl
