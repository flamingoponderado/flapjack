import Flapjack.Compiler.Backend.ClosToBvl.SourceExps
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.SourceCompile

/-! Equivalence between the original list-valued converter and its singleton
reformulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

private abbrev Aux := List (Nat × Nat × Bvl.Exp)

private theorem option_size_pos {α : Type} [SizeOf α] (x : Option α) : 0 < sizeOf x := by
  cases x <;> simp_wf <;> omega

private theorem trace_size_pos (x : BackendCommon.Tra) : 0 < sizeOf x := by
  cases x <;> simp_wf <;> omega

private theorem map_zip_eq_zipWith {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) :
    (xs.zip ys).map (fun (x, y) => f x y) = List.zipWith f xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih => cases ys <;> simp [ih]

mutual
/-- The original list conversion equals the total list reformulation. -/
theorem compileExps_eq_list (maxApp : Nat) (es : List ClosLang.Exp) (aux : Aux) :
    compileExpsHOL maxApp es aux = compileExpListHOL maxApp es aux := by
  cases es with
  | nil => simp [compileExpsHOL, compileExpListHOL]
  | cons e es =>
    cases he : compileExpHOL maxApp e aux with
    | mk compiled aux1 =>
      have first := compileExpsSingleton_eq maxApp e aux
      rw [he] at first
      cases ht : compileExpListHOL maxApp es aux1 with
      | mk rest aux2 =>
        have tail := compileExps_eq_list maxApp es aux1
        rw [ht] at tail
        simp [compileExpsHOL, compileExpListHOL, first, tail, he, ht]
termination_by 2 * sizeOf es
decreasing_by all_goals simp_wf <;> omega

/-- The source singleton cases yield exactly one reformulated expression. -/
theorem compileExpsSingleton_eq (maxApp : Nat) (e : ClosLang.Exp) (aux : Aux) :
    compileExpsSingletonHOL maxApp e aux =
      let (compiled, aux') := compileExpHOL maxApp e aux
      ([compiled], aux') := by
  cases e with
  | var t v => simp [compileExpsSingletonHOL, compileExpHOL]
  | ifThenElse t x y z =>
    cases hx : compileExpHOL maxApp x aux with
    | mk a aux1 =>
      have cx := compileExps_eq_list maxApp [x] aux
      simp [compileExpListHOL, hx] at cx
      cases hy : compileExpHOL maxApp y aux1 with
      | mk b aux2 =>
        have cy := compileExps_eq_list maxApp [y] aux1
        simp [compileExpListHOL, hy] at cy
        cases hz : compileExpHOL maxApp z aux2 with
        | mk c aux3 =>
          have cz := compileExps_eq_list maxApp [z] aux2
          simp [compileExpListHOL, hz] at cz
          simp [compileExpsSingletonHOL, compileExpHOL, cx, cy, cz, hx, hy, hz, Flapjack.holHd]
  | «let» t xs x =>
    cases hs : compileExpListHOL maxApp xs aux with
    | mk a aux1 =>
      have cs := compileExps_eq_list maxApp xs aux
      rw [hs] at cs
      cases hx : compileExpHOL maxApp x aux1 with
      | mk b aux2 =>
        have cx := compileExps_eq_list maxApp [x] aux1
        simp [compileExpListHOL, hx] at cx
        simp [compileExpsSingletonHOL, compileExpHOL, cs, cx, hs, hx, Flapjack.holHd]
  | raise t x | tick t x =>
    cases hx : compileExpHOL maxApp x aux with
    | mk a aux1 =>
      have cx := compileExps_eq_list maxApp [x] aux
      simp [compileExpListHOL, hx] at cx
      simp [compileExpsSingletonHOL, compileExpHOL, cx, hx, Flapjack.holHd]
  | handle t x y =>
    cases hx : compileExpHOL maxApp x aux with
    | mk a aux1 =>
      have cx := compileExps_eq_list maxApp [x] aux
      simp [compileExpListHOL, hx] at cx
      cases hy : compileExpHOL maxApp y aux1 with
      | mk b aux2 =>
        have cy := compileExps_eq_list maxApp [y] aux1
        simp [compileExpListHOL, hy] at cy
        simp [compileExpsSingletonHOL, compileExpHOL, cx, cy, hx, hy, Flapjack.holHd]
  | op t op xs | call t _ _ xs =>
    cases hs : compileExpListHOL maxApp xs aux with
    | mk a aux1 =>
      have cs := compileExps_eq_list maxApp xs aux
      rw [hs] at cs
      simp [compileExpsSingletonHOL, compileExpHOL, cs, hs] <;> rfl
  | app t loc x xs =>
    cases hx : compileExpHOL maxApp x aux with
    | mk a aux1 =>
      have cx := compileExps_eq_list maxApp [x] aux
      simp [compileExpListHOL, hx] at cx
      cases hs : compileExpListHOL maxApp xs aux1 with
      | mk b aux2 =>
        have cs := compileExps_eq_list maxApp xs aux1
        rw [hs] at cs
        simp [compileExpsSingletonHOL, compileExpHOL, cx, cs, hx, hs] <;> rfl
  | fn t loc vs args x =>
    cases hx : compileExpHOL maxApp x aux with
    | mk a aux1 =>
      have cx := compileExps_eq_list maxApp [x] aux
      simp [compileExpListHOL, hx] at cx
      simp [compileExpsSingletonHOL, compileExpHOL, cx, hx, Flapjack.holHd]
  | letrec names loc vs fs body =>
    cases fs with
    | nil =>
      have cb := compileExps_eq_list maxApp [body] aux
      simpa [compileExpsSingletonHOL, compileExpHOL, compileExpListHOL] using cb
    | cons first rest =>
      cases rest with
      | nil =>
        obtain ⟨arity, f⟩ := first
        cases hf : compileExpHOL maxApp f aux with
        | mk compiled aux1 =>
          have cf := compileExps_eq_list maxApp [f] aux
          simp [compileExpListHOL, hf] at cf
          let entry := (loc.getD 0 + numStubs maxApp, arity + 1,
            Bvl.Exp.let ((List.range arity).map Bvl.Exp.var ++ [.var arity] ++
              freeLet (.var arity) (vs.getD []).length) compiled)
          cases hb : compileExpHOL maxApp body (entry :: aux1) with
          | mk result aux2 =>
            have cb := compileExps_eq_list maxApp [body] (entry :: aux1)
            simp [compileExpListHOL, hb] at cb
            simp only [entry, List.append_assoc, List.singleton_append] at cb hb
            simp [compileExpsSingletonHOL, compileExpHOL, cf, cb, hf, hb, Flapjack.holHd] <;> rfl
      | cons second rest =>
        cases hf : compileExpListHOL maxApp ((first :: second :: rest).map Prod.snd) aux with
        | mk compiled aux1 =>
          have cf := compileExpsFuns_eq_list maxApp (first :: second :: rest) aux
          rw [hf] at cf
          have gf := compileExpFunsHOL_eq_map maxApp (first :: second :: rest) aux
          rw [hf] at gf
          let cases := List.zipWith (codeForReccCase ((first :: second :: rest).length + (vs.getD []).length))
            ((first :: second :: rest).map Prod.fst) compiled
          let nextAux := (buildAux (loc.getD 0 + numStubs maxApp) cases aux1).2
          cases hb : compileExpHOL maxApp body nextAux with
          | mk result aux2 =>
            have cb := compileExps_eq_list maxApp [body] nextAux
            simp [compileExpListHOL, hb] at cb
            simp only [nextAux, cases, List.length_cons, List.map_cons] at cb hb
            simp [compileExpsSingletonHOL, compileExpHOL, cf, gf, cb, hb,
              map_zip_eq_zipWith, Flapjack.holHd] <;> rfl
termination_by 2 * sizeOf e + 1
decreasing_by
  all_goals simp_wf
  all_goals try have h : 0 < sizeOf (‹BackendCommon.Tra›) := trace_size_pos _
  all_goals try have h : 0 < sizeOf (‹Option Nat›) := option_size_pos _
  all_goals omega

/-- The mapped recursive-body helper agrees with source list conversion. -/
theorem compileExpsFuns_eq_list (maxApp : Nat) (fs : List (Nat × ClosLang.Exp)) (aux : Aux) :
    compileExpsFunsHOL maxApp fs aux = compileExpListHOL maxApp (fs.map Prod.snd) aux := by
  cases fs with
  | nil => simp [compileExpsFunsHOL, compileExpListHOL]
  | cons first fs =>
    obtain ⟨arity, e⟩ := first
    cases he : compileExpHOL maxApp e aux with
    | mk compiled aux1 =>
      have head := compileExps_eq_list maxApp [e] aux
      simp [compileExpListHOL, he] at head
      cases ht : compileExpListHOL maxApp (fs.map Prod.snd) aux1 with
      | mk rest aux2 =>
        have tail := compileExpsFuns_eq_list maxApp fs aux1
        rw [ht] at tail
        simp [compileExpsFunsHOL, compileExpListHOL, head, tail, he, ht]
termination_by 2 * sizeOf fs + 1
decreasing_by all_goals simp_wf <;> omega
end

/-- A singleton list uses precisely the source singleton clause. -/
theorem compileExps_singleton (maxApp : Nat) (e : ClosLang.Exp) (aux : Aux) :
    compileExpsHOL maxApp [e] aux = compileExpsSingletonHOL maxApp e aux := by
  cases h : compileExpsSingletonHOL maxApp e aux with
  | mk result aux' => simp [compileExpsHOL, h]

/-- The original multi-element recursion compiles the first singleton before
the remaining expressions. -/
theorem compileExps_cons (maxApp : Nat) (e : ClosLang.Exp) (es : List ClosLang.Exp) (aux : Aux) :
    compileExpsHOL maxApp (e :: es) aux =
      let (first, aux') := compileExpsHOL maxApp [e] aux
      let (rest, aux'') := compileExpsHOL maxApp es aux'
      (first ++ rest, aux'') := by
  simp only [compileExps_eq_list]
  cases h : compileExpHOL maxApp e aux with
  | mk result aux' =>
    cases hs : compileExpListHOL maxApp es aux' with
    | mk rest aux'' => simp [compileExpListHOL, h, hs]

/-- The factored body traversal is the source's mapped list conversion. -/
theorem compileExpsFuns_eq_map (maxApp : Nat) (fs : List (Nat × ClosLang.Exp)) (aux : Aux) :
    compileExpsFunsHOL maxApp fs aux = compileExpsHOL maxApp (fs.map Prod.snd) aux := by
  rw [compileExpsFuns_eq_list, compileExps_eq_list]

/-- The original singleton and list forms agree with the reformulation. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "compile_exp_sing_eq"]
theorem compileExpSing_eq :
    (∀ n e aux, compileExpsHOL n [e] aux =
      (fun (result : Bvl.Exp × Aux) => ([result.1], result.2)) (compileExpHOL n e aux)) ∧
    (∀ n es aux, compileExpsHOL n es aux = compileExpListHOL n es aux) := by
  constructor
  · intro n e aux
    have h := compileExps_eq_list n [e] aux
    simpa [compileExpListHOL] using h
  · exact compileExps_eq_list

/-- The program's zip-and-map helper has the source MAP2 shape. -/
theorem compileProgExps_map2 (maxApp : Nat) (prog : List (Nat × Nat × ClosLang.Exp)) :
    compileProgExpsHOL maxApp prog =
      let (exps, aux) := compileExpsHOL maxApp (prog.map (fun (_, _, exp) => exp)) []
      List.zipWith (fun (item : Nat × Nat × ClosLang.Exp) exp =>
        (item.1 + numStubs maxApp, item.2.1, exp)) prog exps ++ aux := by
  unfold compileProgExpsHOL
  cases h : compileExpsHOL maxApp (prog.map (fun (_, _, exp) => exp)) [] with
  | mk exps aux =>
    simp only
    have correspondence := map_zip_eq_zipWith
      (fun (item : Nat × Nat × ClosLang.Exp) exp => (item.1 + numStubs maxApp, item.2.1, exp)) prog exps
    simpa using congrArg (fun xs => xs ++ aux) correspondence

/-- The source-shaped reformulated program converter equals the original
list-valued program converter. -/
theorem compileProgExps_eq (maxApp : Nat) (prog : List (Nat × Nat × ClosLang.Exp)) :
    compileProgExpsHOL maxApp prog = compileProgHOL maxApp prog := by
  simp [compileProgExpsHOL, compileProgHOL, compileExps_eq_list]

/-- The production program converter returns the original program result. -/
theorem compileProg_checked_eq_original (maxApp : Nat) (prog : List (Nat × Nat × ClosLang.Exp)) :
    compileProg? maxApp prog = some (compileProgExpsHOL maxApp prog) := by
  rw [compileProgExps_eq]
  exact compileProg_checked_eq maxApp prog

end Flapjack.Compiler.Backend.ClosToBvl
