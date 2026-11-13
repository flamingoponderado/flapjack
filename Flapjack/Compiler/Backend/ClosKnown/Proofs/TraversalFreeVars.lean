module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SourceEquations
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.InlineFreeVars
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.FreeVars

@[expose] public section

/-! Free-variable preservation for the complete known-function traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosProps

private def Inv (c : Config) (es : List Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : Prop :=
  ∀ eas next n, knownListTotal c es env globals = (eas, next) →
    fvMax n es → fvMax n (eas.map Prod.fst)

private theorem work (c : Config) (xs : List Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : Inv c xs env globals := by
  induction c, xs, env, globals using knownListTotal.induct
    (motive1 := fun c e env g => Inv c [e] env g)
    (motive2 := fun c fns clos env g => ∀ n e, (n, e) ∈ fns →
      Inv c [e] (List.replicate n .other ++ clos ++ env) g)
  case case1 c env g t v =>
    intro eas next n run safe
    simp only [knownListTotal_var, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    simpa using safe
  case case2 =>
    rename_i c env g t x y z xe xa g1 hx ye ya g2 hy ze za g3 hz ix iy iz
    intro eas next n run safe
    have parts : fvMax n [x] ∧ fvMax n [y] ∧ fvMax n [z] := by
      simpa [fvMax, freeVars, freeVarExp, or_imp, forall_and] using safe
    have h1 : knownListTotal c [x] env g = ([(xe, xa)], g1) := by simp [knownListTotal_single, hx]
    have h2 : knownListTotal c [y] env g1 = ([(ye, ya)], g2) := by simp [knownListTotal_single, hy]
    have h3 : knownListTotal c [z] env g2 = ([(ze, za)], g3) := by simp [knownListTotal_single, hz]
    have r1 := ix _ _ n h1 parts.1
    have r2 := iy _ _ n h2 parts.2.1
    have r3 := iz _ _ n h3 parts.2.2
    rw [knownListTotal_if, h1] at run
    dsimp only at run
    rw [h2] at run
    dsimp only at run
    rw [h3] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simp [fvMax, freeVars, freeVarExp, or_imp, forall_and] at r1 r2 r3 ⊢
    exact ⟨r1, r2, r3⟩
  case case3 =>
    rename_i c env g t xs body ea g1 h1 e a g2 h2 ib indBody
    intro eas next n run safe
    have parts := (fvMaxLet n t xs body).mp safe
    have r1 := ib ea g1 n h1 parts.1
    have bodyRun : knownListTotal c [body] (ea.map Prod.snd ++ env) g1 = ([(e, a)], g2) := by
      simp [knownListTotal_single, h2]
    have r2 := indBody _ _ (n + xs.length) bodyRun parts.2
    have len : ea.length = xs.length := by
      have h := knownListTotal_length c xs env g
      rw [h1] at h
      exact h
    rw [knownListTotal_let, h1] at run
    dsimp only at run
    rw [bodyRun] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simp only [List.map_singleton]
    apply (fvMaxLet n t (ea.map Prod.fst) e).mpr
    exact ⟨r1, by simpa [len] using r2⟩
  case case4 c env g t x xe xa g1 hx ih =>
    intro eas next n run safe
    have bodyRun : knownListTotal c [x] env g = ([(xe, xa)], g1) := by
      simp [knownListTotal_single, hx]
    have bodySafe : fvMax n [x] := by simpa [fvMax, freeVars, freeVarExp] using safe
    have result := ih _ _ n bodyRun bodySafe
    rw [knownListTotal_raise, bodyRun] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [fvMax, freeVars, freeVarExp] using result
  case case5 c env g t x xe xa g1 hx ih =>
    intro eas next n run safe
    have bodyRun : knownListTotal c [x] env g = ([(xe, xa)], g1) := by
      simp [knownListTotal_single, hx]
    have bodySafe : fvMax n [x] := by simpa [fvMax, freeVars, freeVarExp] using safe
    have result := ih _ _ n bodyRun bodySafe
    rw [knownListTotal_tickSource, bodyRun] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [fvMax, freeVars, freeVarExp] using result
  case case6 =>
    rename_i c env g t body handler e1 a1 g1 h1 e2 a2 g2 h2 ib ih
    intro eas next n run safe
    have parts := (fvMaxHandle n t body handler).mp safe
    have bodyRun : knownListTotal c [body] env g = ([(e1, a1)], g1) := by simp [knownListTotal_single, h1]
    have handlerRun : knownListTotal c [handler] (.other :: env) g1 = ([(e2, a2)], g2) := by simp [knownListTotal_single, h2]
    have r1 := ib _ _ n bodyRun parts.1
    have r2 := ih _ _ (n + 1) handlerRun parts.2
    rw [knownListTotal_handle, bodyRun] at run
    dsimp only at run
    rw [handlerRun] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simp only [List.map_singleton]
    exact (fvMaxHandle n t e1 e2).mpr ⟨by simpa using r1, by simpa using r2⟩
  case case7 c env g t ticks dest args ea g1 hargs ih =>
    intro eas next n run safe
    have argsSafe : fvMax n args := by simpa [fvMax, freeVars, freeVarExp] using safe
    have result := ih ea g1 n hargs argsSafe
    rw [knownListTotal_call, hargs] at run
    simp at run
    rcases run with ⟨rfl, rfl⟩
    simpa [fvMax, freeVars, freeVarExp] using result
  case case8 c env g t op args ea g1 hargs a g2 hop ih =>
    intro eas next n run safe
    have argsSafe : fvMax n args := by simpa [fvMax, freeVars, freeVarExp] using safe
    have result := ih ea g1 n hargs argsSafe
    rw [knownListTotal_op, hargs] at run
    dsimp only at run
    rw [hop] at run
    dsimp only at run
    let out := match op, a with
      | .globOp (.global _), .int i => Exp.op t (.intOp (.const i)) (ea.map Prod.fst)
      | .globOp (.global _), .tuple tag [] => Exp.op t (.blockOp (.cons tag)) (ea.map Prod.fst)
      | _, _ => ClosOp.smartOp t op (ea.map Prod.fst)
    have outSafe : fvMax n [out] := by
      dsimp only [out]
      split
      · simpa [fvMax, freeVars, freeVarExp] using result
      · simpa [fvMax, freeVars, freeVarExp] using result
      · apply fvMaxSmartOp
        simpa [fvMax, freeVars, freeVarExp] using result
    change ([(out, a)], g2) = (eas, next) at run
    cases run
    simpa using outSafe
  case case9 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx hd iargs ifun
    intro eas next n run safe
    have parts : fvMax n [x] ∧ fvMax n xs := by
      simpa [fvMax, freeVars, freeVarExp, or_imp, forall_and] using safe
    have ra := iargs ea g1 n ha parts.2
    have functionRun : knownListTotal c [x] env g1 = ([(e, a)], g2) := by simp [knownListTotal_single, hx]
    have rf := ifun _ _ n functionRun parts.1
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    rw [knownListTotal_app, ha] at run
    dsimp only at run
    rw [functionRun] at run
    simp [knownSourceHead, ← len, hd] at run
    rcases run with ⟨rfl, rfl⟩
    simp [fvMax, freeVars, freeVarExp, or_imp, forall_and] at ra rf ⊢
    exact ⟨rf, ra⟩
  case case10 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx target hd iargs ifun
    intro eas next n run safe
    have parts : fvMax n [x] ∧ fvMax n xs := by
      simpa [fvMax, freeVars, freeVarExp, or_imp, forall_and] using safe
    have ra := iargs ea g1 n ha parts.2
    have functionRun : knownListTotal c [x] env g1 = ([(e, a)], g2) := by simp [knownListTotal_single, hx]
    have rf := ifun _ _ n functionRun parts.1
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    rw [knownListTotal_app, ha] at run
    dsimp only at run
    rw [functionRun] at run
    simp [knownSourceHead, ← len, hd] at run
    rcases run with ⟨rfl, rfl⟩
    simp [fvMax, freeVars, freeVarExp, or_imp, forall_and] at ra rf ⊢
    exact ⟨rf, ra⟩
  case case11 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx body hd be ba g3 hb iargs ifun ibody
    intro eas next n run safe
    have parts : fvMax n [x] ∧ fvMax n xs := by
      simpa [fvMax, freeVars, freeVarExp, or_imp, forall_and] using safe
    have ra := iargs ea g1 n ha parts.2
    have functionRun : knownListTotal c [x] env g1 = ([(e, a)], g2) := by simp [knownListTotal_single, hx]
    have rf := ifun _ _ n functionRun parts.1
    have bodySafe : fvMax ea.length [body] :=
      (InlineFreeVars.decideInlineLetInlineFvMax c a loc ea.length body hd).choose_spec.choose_spec.2
    have bodyRun : knownListTotal (decInlineFactor c) [body] (ea.map Prod.snd) g2 = ([(be, ba)], g3) := by
      simp [knownListTotal_single, hb]
    have rb := ibody _ _ ea.length bodyRun bodySafe
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    rw [knownListTotal_app, ha] at run
    dsimp only at run
    rw [functionRun] at run
    simp [knownSourceHead, ← len, hd, bodyRun] at run
    rcases run with ⟨rfl, rfl⟩
    let outArgs := if ClosLang.pure x then ea.map Prod.fst else ea.map Prod.fst ++ [e]
    have outArgsSafe : fvMax n outArgs := by
      dsimp [outArgs]
      split
      · exact ra
      · apply (fvMaxAppend _ _ _).mpr
        exact ⟨ra, by simpa using rf⟩
    have argBound : ea.length ≤ n + outArgs.length := by
      dsimp [outArgs]
      split <;> (simp <;> omega)
    have widened : fvMax (n + outArgs.length) [be] :=
      fvMaxLess ea.length (n + outArgs.length) [be] ⟨by simpa using rb, argBound⟩
    have tickBound : fvMax (n + outArgs.length) [ticks t 1 ea.length be] :=
      (fvMaxTicks _ _ _ _ _).mpr widened
    change fvMax n [.let (BackendCommon.mkCons t 0) outArgs (ticks t 1 ea.length be)]
    exact (fvMaxLet _ _ _ _).mpr ⟨outArgsSafe, tickBound⟩
  case case12 c env g name loc vs arity body e a g1 hb ih =>
    intro eas next n run safe
    have bodySafe := (fvMaxFn n arity name loc vs body).mp safe
    have bodyRun : knownListTotal c [body] (List.replicate arity .other ++ env) g = ([(e, a)], g1) := by
      simp [knownListTotal_single, hb]
    have result := ih [(e, a)] g1 (n + arity) bodyRun bodySafe
    rw [knownListTotal_fn, bodyRun] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simp only [List.map_singleton]
    exact (fvMaxFn n arity name loc none e).mpr (by simpa using result)
  case case13 =>
    rename_i c env g names loc vs fns body clos be ba g1 hb ifuns ibody
    intro eas next n run safe
    have parts := (fvMaxLetrec n names loc vs fns body).mp safe
    let newFns := fns.map (fun (arity, e) =>
      (arity, (knownSourceHead (knownListTotal c [e] (List.replicate arity ValApprox.other ++ clos ++ env) g).1).1))
    have newLen : newFns.length = fns.length := by simp [newFns]
    have newSafe : ∀ p ∈ newFns, fvMax (n + p.1 + newFns.length) [p.2] := by
      intro p member
      obtain ⟨⟨arity, e⟩, inFns, entryEq⟩ := List.mem_map.mp member
      have bodySafe := parts.1 (arity, e) inFns
      cases he : knownListTotal c [e] (List.replicate arity ValApprox.other ++ clos ++ env) g with
      | mk ea ge =>
        obtain ⟨e', a', eaEq⟩ := knownListTotal_single_result c e _ g ge ea he
        subst ea
        have result := ifuns arity e inFns [(e', a')] ge (n + arity + fns.length) he (by simpa using bodySafe)
        change (arity, (knownSourceHead (knownListTotal c [e] (List.replicate arity ValApprox.other ++ clos ++ env) g).1).1) = p at entryEq
        simp [knownSourceHead] at entryEq
        subst p
        simpa [newLen, ← List.append_assoc, he, knownSourceHead] using result
    have bodyRun : knownListTotal c [body] (clos ++ env) g = ([(be, ba)], g1) := by
      simp [knownListTotal_single, hb]
    have bodyResult := ibody _ _ (n + fns.length) bodyRun parts.2
    rw [knownListTotal_letrec] at run
    dsimp only at run
    cases loc <;> simp [knownSourceHead] at run
    all_goals rcases run with ⟨rfl, rfl⟩
    all_goals simp only [List.map_singleton]
    all_goals apply (fvMaxLetrec _ _ _ _ _ _).mpr
    all_goals simp [clos, noInline] at bodyRun
    all_goals exact ⟨by simpa only [newFns, clos, noInline, knownSourceHead, List.headD_eq_head?_getD, List.length_map, List.replicate_add, List.append_assoc] using newSafe,
      by simpa [newFns, knownSourceHead, ← List.append_assoc, bodyRun] using bodyResult⟩
  case case14 => contradiction
  case case15 =>
    rename_i c clos env g arity body fns e a g1 hb ihBody ihRest n x member
    rcases List.mem_cons.mp member with same | tail
    · cases Prod.mk.inj same with
      | intro hn hx => subst n; subst x; exact ihBody
    · exact ihRest n x tail
  case case16 c env g =>
    intro eas next n run safe
    simp [knownListTotal] at run
    rcases run with ⟨rfl, rfl⟩
    simpa using safe
  case case17 =>
    rename_i c env g x xs xe xa g1 hx tailEa g2 ht ix it
    cases xs with
    | nil => exact ix
    | cons y ys =>
      intro eas next n run safe
      have parts := (fvMaxCons n x (y :: ys)).mp safe
      have headRun : knownListTotal c [x] env g = ([(xe, xa)], g1) := by simp [knownListTotal_single, hx]
      have headResult := ix [(xe, xa)] g1 n headRun parts.1
      have tailResult := it tailEa g2 n ht parts.2
      rw [knownListTotal_cons_cons, headRun] at run
      dsimp only at run
      rw [ht] at run
      simp only [Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      simp only [List.cons_append, List.nil_append, List.map_cons]
      exact (fvMaxCons n xe (tailEa.map Prod.fst)).mpr ⟨by simpa using headResult, tailResult⟩
/-- The optimizer preserves the free-variable bound of the source expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_fv_max"]
theorem knownPreservesFvMax (c : Config) (es : List Exp) (aenv : List ValApprox)
    (g0 : Spt ValApprox) (eas : List (Exp × ValApprox)) (g : Spt ValApprox) (n : Nat)
    (h : knownListTotal c es aenv g0 = (eas, g) ∧ fvMax n es) :
    fvMax n (eas.map Prod.fst) :=
  work c es aenv g0 eas g n h.1 h.2

end Flapjack.Compiler.Backend.ClosKnown
