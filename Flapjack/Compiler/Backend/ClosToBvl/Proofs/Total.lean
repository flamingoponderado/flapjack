import Flapjack.Compiler.Backend.ClosToBvl.Prepared

/-!
Totality of the checked closure-to-BVL expression conversion. This is
Flapjack-specific infrastructure; the source correspondence and semantic
correctness of the pass require separate proofs.
-/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The checked recursive builder succeeds when its list contains at least
the requested number of arities. -/
theorem reccLets_succeeds (n : Nat) (args : List Nat) (k : Nat) (body : Bvl.Exp)
    (enough : k ≤ args.length) : ∃ result, reccLets? n args k body = some result := by
  induction k generalizing args with
  | zero => cases args <;> exact ⟨body, rfl⟩
  | succ k ih =>
    cases args with
    | nil => simp at enough
    | cons a rest =>
      have bound : k ≤ rest.length := by simp only [List.length_cons, Nat.succ_le_succ_iff] at enough; exact enough
      obtain ⟨next, nextEq⟩ := ih rest bound
      exact ⟨.let [reccLet (n + 2 * k) a k] next, by simp [reccLets?, nextEq]⟩

/-- For the bounded arity lists used by compilation, the executed checked
builder returns the source-shaped layout. -/
theorem reccLets_checked_eq (n : Nat) (args : List Nat) (k : Nat) (body : Bvl.Exp)
    (enough : k ≤ args.length) : reccLets? n args k body = some (reccLetsHOL n args k body) := by
  induction k generalizing args with
  | zero => cases args <;> rfl
  | succ k ih =>
    cases args with
    | nil => simp at enough
    | cons a rest =>
      have bound : k ≤ rest.length := by simpa using enough
      simp [reccLets?, reccLetsHOL, Flapjack.holHd, ih rest bound]

/-- A nonempty recursive group whose arity count agrees with its size passes
the checked layout construction. -/
theorem buildReccLets_succeeds (args vs : List Nat) (n : Nat) (body : Bvl.Exp)
    (nonempty : args ≠ []) : ∃ result, buildReccLets? args vs n args.length body = some result := by
  cases h : args.reverse with
  | nil =>
    have : args = [] := by simpa using congrArg List.reverse h
    exact False.elim (nonempty this)
  | cons last rest =>
    have length : args.length = rest.length + 1 := by
      have := congrArg List.length h
      simpa using this
    have bound : args.length - 1 ≤ rest.length := by omega
    obtain ⟨next, nextEq⟩ := reccLets_succeeds n rest (args.length - 1) body bound
    refine ⟨.let [.let [.op (.memOp .ref) (((args.map fun _ => mkConst 0) ++
      (vs.map Bvl.Exp.var)).reverse)]
      (reccLet0 (n + 2 * (args.length - 1)) last (args.length - 1))] next, ?_⟩
    simp [buildReccLets?, h, nextEq]

/-- The actual recursive-group builder implements the source definition when
its argument list is nonempty and the group length is that list's length. -/
theorem buildReccLets_checked_eq (args vs : List Nat) (n : Nat) (body : Bvl.Exp)
    (nonempty : args ≠ []) :
    buildReccLets? args vs n args.length body = some (buildReccLetsHOL args vs n args.length body) := by
  cases h : args.reverse with
  | nil =>
    have : args = [] := by simpa using congrArg List.reverse h
    exact False.elim (nonempty this)
  | cons last rest =>
    have length : args.length = rest.length + 1 := by
      have := congrArg List.length h
      simpa using this
    have bound : args.length - 1 ≤ rest.length := by omega
    simp [buildReccLets?, buildReccLetsHOL, h, Flapjack.holHd, reccLets_checked_eq n rest _ body bound]

mutual
/-- The checked expression converter always finds the recursive layout it
needs. The result includes the accumulated auxiliary functions. -/
theorem compileExp_succeeds (maxApp : Nat) (expression : ClosLang.Exp)
    (aux : List (Nat × Nat × Bvl.Exp)) :
    ∃ result, compileExp? maxApp expression aux = some result := by
  cases expression with
  | var trace v => exact ⟨(.var v, aux), by simp [compileExp?]⟩
  | ifThenElse trace x y z =>
    obtain ⟨⟨x', aux1⟩, hx⟩ := compileExp_succeeds maxApp x aux
    obtain ⟨⟨y', aux2⟩, hy⟩ := compileExp_succeeds maxApp y aux1
    obtain ⟨⟨z', aux3⟩, hz⟩ := compileExp_succeeds maxApp z aux2
    exact ⟨_, by simp [compileExp?, hx, hy, hz]; rfl⟩
  | «let» trace xs body =>
    obtain ⟨⟨xs', aux1⟩, hxs⟩ := compileExpList_succeeds maxApp xs aux
    obtain ⟨⟨body', aux2⟩, hb⟩ := compileExp_succeeds maxApp body aux1
    exact ⟨_, by simp [compileExp?, hxs, hb]; rfl⟩
  | raise trace x =>
    obtain ⟨⟨x', aux1⟩, hx⟩ := compileExp_succeeds maxApp x aux
    exact ⟨_, by simp [compileExp?, hx]; rfl⟩
  | tick trace x =>
    obtain ⟨⟨x', aux1⟩, hx⟩ := compileExp_succeeds maxApp x aux
    exact ⟨_, by simp [compileExp?, hx]; rfl⟩
  | handle trace x y =>
    obtain ⟨⟨x', aux1⟩, hx⟩ := compileExp_succeeds maxApp x aux
    obtain ⟨⟨y', aux2⟩, hy⟩ := compileExp_succeeds maxApp y aux1
    exact ⟨_, by simp [compileExp?, hx, hy]; rfl⟩
  | op trace op xs =>
    obtain ⟨⟨xs', aux1⟩, hxs⟩ := compileExpList_succeeds maxApp xs aux
    exact ⟨_, by simp [compileExp?, hxs]; rfl⟩
  | app trace loc x xs =>
    obtain ⟨⟨x', aux1⟩, hx⟩ := compileExp_succeeds maxApp x aux
    obtain ⟨⟨xs', aux2⟩, hxs⟩ := compileExpList_succeeds maxApp xs aux1
    exact ⟨_, by simp [compileExp?, hx, hxs]; rfl⟩
  | fn name loc vs args x =>
    obtain ⟨⟨x', aux1⟩, hx⟩ := compileExp_succeeds maxApp x aux
    exact ⟨_, by simp [compileExp?, hx]; rfl⟩
  | call trace ticks dest xs =>
    obtain ⟨⟨xs', aux1⟩, hxs⟩ := compileExpList_succeeds maxApp xs aux
    exact ⟨_, by simp [compileExp?, hxs]; rfl⟩
  | letrec names loc vs funs body =>
    cases funs with
    | nil =>
      obtain ⟨result, h⟩ := compileExp_succeeds maxApp body aux
      exact ⟨result, by simpa [compileExp?] using h⟩
    | cons first rest =>
      cases rest with
      | nil =>
        obtain ⟨args, function⟩ := first
        obtain ⟨⟨function', aux1⟩, hf⟩ := compileExp_succeeds maxApp function aux
        let entry := (loc.getD 0 + numStubs maxApp, args + 1,
          Bvl.Exp.let ((List.range args).map Bvl.Exp.var ++ [.var args] ++
            freeLet (.var args) (vs.getD []).length) function')
        obtain ⟨⟨body', aux2⟩, hb⟩ := compileExp_succeeds maxApp body (entry :: aux1)
        simp only [entry, List.append_assoc, List.singleton_append] at hb
        exact ⟨_, by simp [compileExp?, hf, hb]; rfl⟩
      | cons second rest =>
        obtain ⟨⟨compiled, aux1⟩, hf⟩ := compileExpFuns_succeeds maxApp (first :: second :: rest) aux
        let cases := compiled.map (fun (args, b) =>
          codeForReccCase ((first :: second :: rest).length + (vs.getD []).length) args b)
        let nextAux := (buildAux (loc.getD 0 + numStubs maxApp) cases aux1).2
        obtain ⟨⟨body', aux2⟩, hb⟩ := compileExp_succeeds maxApp body nextAux
        obtain ⟨finished, hfinished⟩ := buildReccLets_succeeds ((first :: second :: rest).map Prod.fst)
          (vs.getD []) (loc.getD 0 + numStubs maxApp) body' (by simp)
        simp only [nextAux, cases, List.length_cons] at hb
        simp only [List.length_map, List.length_cons, List.map_cons] at hfinished
        exact ⟨_, by simp [compileExp?, hf, hb, hfinished]; rfl⟩
termination_by sizeOf expression
decreasing_by all_goals simp_wf <;> omega

/-- Checked list conversion succeeds for arbitrary expressions and auxiliary
tables. -/
theorem compileExpList_succeeds (maxApp : Nat) (expressions : List ClosLang.Exp)
    (aux : List (Nat × Nat × Bvl.Exp)) :
    ∃ result, compileExpList? maxApp expressions aux = some result := by
  cases expressions with
  | nil => exact ⟨([], aux), by simp [compileExpList?]⟩
  | cons x xs =>
    obtain ⟨⟨x', aux1⟩, hx⟩ := compileExp_succeeds maxApp x aux
    obtain ⟨⟨xs', aux2⟩, hxs⟩ := compileExpList_succeeds maxApp xs aux1
    exact ⟨_, by simp [compileExpList?, hx, hxs]; rfl⟩
termination_by sizeOf expressions
decreasing_by all_goals simp_wf <;> omega

/-- Checked recursive-function conversion succeeds for arbitrary bodies. -/
theorem compileExpFuns_succeeds (maxApp : Nat) (functions : List (Nat × ClosLang.Exp))
    (aux : List (Nat × Nat × Bvl.Exp)) :
    ∃ result, compileExpFuns? maxApp functions aux = some result := by
  cases functions with
  | nil => exact ⟨([], aux), by simp [compileExpFuns?]⟩
  | cons first rest =>
    obtain ⟨arity, x⟩ := first
    obtain ⟨⟨x', aux1⟩, hx⟩ := compileExp_succeeds maxApp x aux
    obtain ⟨⟨rest', aux2⟩, hrest⟩ := compileExpFuns_succeeds maxApp rest aux1
    exact ⟨_, by simp [compileExpFuns?, hx, hrest]; rfl⟩
termination_by sizeOf functions
decreasing_by all_goals simp_wf <;> omega
end

/-- The program conversion itself cannot fail. -/
theorem compileProg_succeeds (maxApp : Nat) (prog : List (Nat × Nat × ClosLang.Exp)) :
    ∃ result, compileProg? maxApp prog = some result := by
  obtain ⟨⟨expressions, aux⟩, h⟩ := compileExpList_succeeds maxApp (prog.map (fun (_, _, e) => e)) []
  exact ⟨_, by simp [compileProg?, h]; rfl⟩

/-- Once preprocessing has produced a closure program, the checked assembly
stage cannot fail during expression lowering. -/
theorem compilePrepared_succeeds (original current : Config) (es : List ClosLang.Exp)
    (prog : List (Nat × Nat × ClosLang.Exp)) :
    ∃ result, compilePrepared? original current es prog = some result := by
  obtain ⟨compiled, h⟩ := compileProg_succeeds current.maxApp prog
  exact ⟨_, by simp [compilePrepared?, h]; rfl⟩

/-- With the optional closure optimizations disabled, neither preprocessing
nor the prepared conversion can fail. -/
theorem compileNoOpts_succeeds (config : Config) (es : List ClosLang.Exp)
    (mti : config.doMti = false) (call : config.doCall = false)
    (known : config.knownConf = none) :
    ∃ result, compileNoOpts? config es = some result := by
  unfold compileNoOpts? compileCommonNoOpts?
  simp only [mti, call, Bool.false_or, Bool.false_eq_true, ↓reduceIte, known]
  generalize renumbered : ClosNumber.renumberList
      (if (config.nextLoc + max 1 es.length) % 2 = 0 then config.nextLoc + max 1 es.length
       else config.nextLoc + max 1 es.length + 1) es = pair
  obtain ⟨next, code⟩ := pair
  simpa [mti, call] using compilePrepared_succeeds config
    { config with start := config.nextLoc, nextLoc := next, knownConf := none, callState := (.ln, []) }
    es (ClosAnnotate.compile (chainExps config.nextLoc code))

end Flapjack.Compiler.Backend.ClosToBvl
