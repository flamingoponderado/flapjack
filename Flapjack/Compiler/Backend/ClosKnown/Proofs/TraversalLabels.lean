module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxLabels
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SourceEquations
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.TicksSyntax
public import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartAnnotations

/-! Label preservation for the complete known-function traversal. -/
@[expose] public section

namespace Flapjack.Compiler.Backend.ClosKnown
open ClosLang ClosProps

/-- Flapjack induction infrastructure for the source list traversal. -/
private def Inv (c : Config) (es : List Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : Prop :=
  ∀ eas next, knownListTotal c es env globals = (eas, next) →
    (∀ e ∈ es, noLabels e) →
    (∀ a ∈ env, valApproxNoLabels a) →
    globalsApproxNoLabels globals →
    (∀ e ∈ eas.map Prod.fst, noLabels e) ∧
    (∀ a ∈ eas.map Prod.snd, valApproxNoLabels a) ∧
    globalsApproxNoLabels next

/-- The traversal preserves all three source label invariants. -/
private theorem work (c : Config) (xs : List Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : Inv c xs env globals := by
  induction c, xs, env, globals using knownListTotal.induct
    (motive1 := fun c e env g => Inv c [e] env g)
    (motive2 := fun c fns clos env g => ∀ n e, (n, e) ∈ fns →
      Inv c [e] (List.replicate n .other ++ clos ++ env) g)
  case case1 c env g t v =>
    intro eas next run _ safe globalSafe
    simp only [knownListTotal_var, Prod.mk.injEq] at run
    rcases run with ⟨rfl, rfl⟩
    have selected : valApproxNoLabels (env[v]?.getD .other) := by
      cases found : env[v]? with
      | none => simp [valApproxNoLabels]
      | some a => simpa [found] using safe a (List.mem_of_getElem? found)
    simpa [noLabels, selected] using globalSafe
  case case2 =>
    rename_i c env g t x y z xe xa g1 hx ye ya g2 hy ze za g3 hz ix iy iz
    intro eas next run inputSafe envSafe globalSafe
    have parts : noLabels x ∧ noLabels y ∧ noLabels z := by
      simpa [noLabels] using inputSafe
    have h1 : knownListTotal c [x] env g = ([(xe, xa)], g1) := by
      simp [knownListTotal_single, hx]
    have h2 : knownListTotal c [y] env g1 = ([(ye, ya)], g2) := by
      simp [knownListTotal_single, hy]
    have h3 : knownListTotal c [z] env g2 = ([(ze, za)], g3) := by
      simp [knownListTotal_single, hz]
    have r1 := ix _ _ h1 (by simpa using parts.1) envSafe globalSafe
    have r2 := iy _ _ h2 (by simpa using parts.2.1) envSafe r1.2.2
    have r3 := iz _ _ h3 (by simpa using parts.2.2) envSafe r2.2.2
    rw [knownListTotal_if, h1] at run
    dsimp only at run
    rw [h2] at run
    dsimp only at run
    rw [h3] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    have merged := valApproxNoLabelsMerge ya za
      ⟨r2.2.1 ya (by simp), r3.2.1 za (by simp)⟩
    simp [noLabels] at r1 r2 r3 ⊢
    exact ⟨⟨r1.1, r2.1, r3.1⟩, merged, r3.2.2⟩
  case case3 =>
    rename_i c env g t xs body ea g1 h1 e a g2 h2 ib indBody
    intro eas next run inputSafe envSafe globalSafe
    have parts : noLabelsList xs ∧ noLabels body := by
      simpa [noLabels] using inputSafe
    have r1 := ib ea g1 h1 ((noLabelsList_iff xs).mp parts.1) envSafe globalSafe
    have bodyEnvSafe : ∀ a ∈ ea.map Prod.snd ++ env, valApproxNoLabels a := by
      intro a member
      rcases List.mem_append.mp member with inArgs | inEnv
      · exact r1.2.1 a inArgs
      · exact envSafe a inEnv
    have bodyRun : knownListTotal c [body] (ea.map Prod.snd ++ env) g1 = ([(e, a)], g2) := by
      simp [knownListTotal_single, h2]
    have r2 := indBody _ _ bodyRun (by simpa using parts.2) bodyEnvSafe r1.2.2
    rw [knownListTotal_let, h1] at run
    dsimp only at run
    rw [bodyRun] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    have bindingSafe := (noLabelsList_iff _).mpr r1.1
    simpa [noLabels, bindingSafe] using r2
  case case4 c env g t x xe xa g1 hx ih =>
    intro eas next run inputSafe envSafe globalSafe
    have bodyRun : knownListTotal c [x] env g = ([(xe, xa)], g1) := by
      simp [knownListTotal_single, hx]
    have bodySafe : ∀ e ∈ [x], noLabels e := by
      simpa [noLabels] using inputSafe
    have result := ih [(xe, xa)] g1 bodyRun bodySafe envSafe globalSafe
    rw [knownListTotal_raise, bodyRun] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [noLabels, valApproxNoLabels] using And.intro result.1 result.2.2
  case case5 c env g t x xe xa g1 hx ih =>
    intro eas next run inputSafe envSafe globalSafe
    have bodyRun : knownListTotal c [x] env g = ([(xe, xa)], g1) := by
      simp [knownListTotal_single, hx]
    have bodySafe : ∀ e ∈ [x], noLabels e := by
      simpa [noLabels] using inputSafe
    have result := ih [(xe, xa)] g1 bodyRun bodySafe envSafe globalSafe
    rw [knownListTotal_tickSource, bodyRun] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [noLabels] using result
  case case6 =>
    rename_i c env g t body handler e1 a1 g1 h1 e2 a2 g2 h2 ib ih
    intro eas next run inputSafe envSafe globalSafe
    have parts : noLabels body ∧ noLabels handler := by
      simpa [noLabels] using inputSafe
    have bodyRun : knownListTotal c [body] env g = ([(e1, a1)], g1) := by
      simp [knownListTotal_single, h1]
    have handlerRun : knownListTotal c [handler] (.other :: env) g1 = ([(e2, a2)], g2) := by
      simp [knownListTotal_single, h2]
    have r1 := ib _ _ bodyRun (by simpa using parts.1) envSafe globalSafe
    have newEnvSafe : ∀ a ∈ ValApprox.other :: env, valApproxNoLabels a := by
      intro a member
      rcases List.mem_cons.mp member with same | old
      · subst a; simp [valApproxNoLabels]
      · exact envSafe a old
    have r2 := ih _ _ handlerRun (by simpa using parts.2) newEnvSafe r1.2.2
    rw [knownListTotal_handle, bodyRun] at run
    dsimp only at run
    rw [handlerRun] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    have merged := valApproxNoLabelsMerge a1 a2
      ⟨r1.2.1 a1 (by simp), r2.2.1 a2 (by simp)⟩
    simp [noLabels] at r1 r2 ⊢
    exact ⟨⟨r1.1, r2.1⟩, merged, r2.2.2⟩
  case case7 c env g t ticks dest args ea g1 hargs ih =>
    intro eas next run inputSafe envSafe globalSafe
    have argsSafe : ∀ e ∈ args, noLabels e := by
      have h : noLabelsList args := by simpa [noLabels] using inputSafe
      exact (noLabelsList_iff args).mp h
    have result := ih ea g1 hargs argsSafe envSafe globalSafe
    rw [knownListTotal_call, hargs] at run
    simp at run
    rcases run with ⟨rfl, rfl⟩
    have argsResult := (noLabelsList_iff _).mpr result.1
    simpa [noLabels, valApproxNoLabels, argsResult] using result.2.2
  case case8 c env g t op args ea g1 hargs a g2 hop ih =>
    intro eas next run inputSafe envSafe globalSafe
    have parts : (∀ n, op ≠ .label n) ∧ noLabelsList args := by
      simpa [noLabels] using inputSafe
    have operatorSafe := parts.1
    have argsSafe : ∀ e ∈ args, noLabels e := by
      exact (noLabelsList_iff args).mp parts.2
    have result := ih ea g1 hargs argsSafe envSafe globalSafe
    have reverseSafe : ∀ a ∈ (ea.map Prod.snd).reverse, valApproxNoLabels a := by
      intro a member
      exact result.2.1 a (List.mem_reverse.mp member)
    have opSafe := knownOpNoLabels op (ea.map Prod.snd).reverse g1 a g2
      ⟨hop, reverseSafe, result.2.2⟩
    rw [knownListTotal_op, hargs] at run
    dsimp only at run
    rw [hop] at run
    dsimp only at run
    let out := match op, a with
      | .globOp (.global _), .int i => Exp.op t (.intOp (.const i)) (ea.map Prod.fst)
      | .globOp (.global _), .tuple tag [] => Exp.op t (.blockOp (.cons tag)) (ea.map Prod.fst)
      | _, _ => ClosOp.smartOp t op (ea.map Prod.fst)
    have outSafe : noLabels out := by
      dsimp only [out]
      split
      · simp [noLabels, (noLabelsList_iff _).mpr result.1]
      · simp [noLabels, (noLabelsList_iff _).mpr result.1]
      · apply (ClosOp.smartNoLabels t op _).mpr
        simpa only [noLabels] using And.intro operatorSafe ((noLabelsList_iff _).mpr result.1)
    change ([(out, a)], g2) = (eas, next) at run
    cases run
    simpa [outSafe] using opSafe
  case case9 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx hd iargs ifun
    intro eas next run inputSafe envSafe globalSafe
    have parts : noLabels x ∧ noLabelsList xs := by
      simpa [noLabels] using inputSafe
    have ra := iargs ea g1 ha ((noLabelsList_iff xs).mp parts.2) envSafe globalSafe
    have functionRun : knownListTotal c [x] env g1 = ([(e, a)], g2) := by
      simp [knownListTotal_single, hx]
    have rf := ifun _ _ functionRun (by simpa using parts.1) envSafe ra.2.2
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    rw [knownListTotal_app, ha] at run
    dsimp only at run
    rw [functionRun] at run
    simp [knownSourceHead, ← len, hd] at run
    rcases run with ⟨rfl, rfl⟩
    have safeArgs := (noLabelsList_iff _).mpr ra.1
    have safeFun := rf.1 e (by simp)
    simp [noLabels, valApproxNoLabels, safeArgs, safeFun, rf.2.2]
  case case10 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx target hd iargs ifun
    intro eas next run inputSafe envSafe globalSafe
    have parts : noLabels x ∧ noLabelsList xs := by
      simpa [noLabels] using inputSafe
    have ra := iargs ea g1 ha ((noLabelsList_iff xs).mp parts.2) envSafe globalSafe
    have functionRun : knownListTotal c [x] env g1 = ([(e, a)], g2) := by
      simp [knownListTotal_single, hx]
    have rf := ifun _ _ functionRun (by simpa using parts.1) envSafe ra.2.2
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    rw [knownListTotal_app, ha] at run
    dsimp only at run
    rw [functionRun] at run
    simp [knownSourceHead, ← len, hd] at run
    rcases run with ⟨rfl, rfl⟩
    have safeArgs := (noLabelsList_iff _).mpr ra.1
    have safeFun := rf.1 e (by simp)
    simp [noLabels, valApproxNoLabels, safeArgs, safeFun, rf.2.2]
  case case11 =>
    rename_i c env g t loc x xs ea g1 ha e a g2 hx body hd be ba g3 hb iargs ifun ibody
    intro eas next run inputSafe envSafe globalSafe
    have parts : noLabels x ∧ noLabelsList xs := by
      simpa [noLabels] using inputSafe
    have ra := iargs ea g1 ha ((noLabelsList_iff xs).mp parts.2) envSafe globalSafe
    have functionRun : knownListTotal c [x] env g1 = ([(e, a)], g2) := by
      simp [knownListTotal_single, hx]
    have rf := ifun _ _ functionRun (by simpa using parts.1) envSafe ra.2.2
    have bodySafe : noLabels body :=
      decideInlineNoLabels c a loc ea.length body ⟨rf.2.1 a (by simp), hd⟩
    have bodyRun : knownListTotal (decInlineFactor c) [body] (ea.map Prod.snd) g2 =
        ([(be, ba)], g3) := by simp [knownListTotal_single, hb]
    have rb := ibody _ _ bodyRun (by simpa using bodySafe) ra.2.1 rf.2.2
    have len := knownListTotal_length c xs env g
    rw [ha] at len
    simp only at len
    rw [knownListTotal_app, ha] at run
    dsimp only at run
    rw [functionRun] at run
    simp [knownSourceHead, ← len, hd, bodyRun] at run
    rcases run with ⟨rfl, rfl⟩
    have safeFun := rf.1 e (by simp)
    have safeArgs : noLabelsList
        (if ClosLang.pure x then ea.map Prod.fst else ea.map Prod.fst ++ [e]) := by
      apply (noLabelsList_iff _).mpr
      split
      · exact ra.1
      · intro x member
        rcases List.mem_append.mp member with original | extra
        · exact ra.1 x original
        · simp only [List.mem_singleton] at extra
          subst x
          exact safeFun
    have safeBody := rb.1 be (by simp)
    have safeTicks := ticks_noLabels t 1 xs.length be safeBody
    simp [noLabels, safeArgs, safeTicks, len, rb.2.1 ba (by simp), rf.2.2]
  case case12 c env g name loc vs arity body e a g1 hb ih =>
    intro eas next run inputSafe envSafe globalSafe
    have bodySafe : ∀ e ∈ [body], noLabels e := by
      simpa [noLabels] using inputSafe
    have bodyEnvSafe : ∀ a ∈ List.replicate arity ValApprox.other ++ env,
        valApproxNoLabels a := by
      intro a member
      rcases List.mem_append.mp member with replicated | old
      · have equal : a = .other := (List.mem_replicate.mp replicated).2
        subst a
        simp [valApproxNoLabels]
      · exact envSafe a old
    have bodyRun : knownListTotal c [body] (List.replicate arity .other ++ env) g =
        ([(e, a)], g1) := by simp [knownListTotal_single, hb]
    have result := ih [(e, a)] g1 bodyRun bodySafe bodyEnvSafe globalSafe
    rw [knownListTotal_fn, bodyRun] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    have resultSafe : noLabels e := result.1 e (by simp)
    refine ⟨?_, ?_, result.2.2⟩
    · simpa [noLabels] using resultSafe
    · cases loc with
      | none => simp [valApproxNoLabels]
      | some loc =>
        simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq]
        unfold closApproxHOL
        split <;> simp [valApproxNoLabels, bodySafe]
  case case13 =>
    rename_i c env g names loc vs fns body clos be ba g1 hb ifuns ibody
    intro eas next run inputSafe envSafe globalSafe
    have parts : noLabelsFuns fns ∧ noLabels body := by
      simpa [noLabels] using inputSafe
    have closSafe : ∀ a ∈ clos, valApproxNoLabels a := by
      cases loc with
      | none => simp [clos, valApproxNoLabels]
      | some n => simpa [clos, noInline] using closGenNoInline_noLabels fns 0 n
    have closEnvSafe : ∀ a ∈ clos ++ env, valApproxNoLabels a := by
      intro a member
      rcases List.mem_append.mp member with mem | mem
      · exact closSafe a mem
      · exact envSafe a mem
    have originalBodies : ∀ e ∈ fns.map Prod.snd, noLabels e :=
      (noLabelsList_iff _).mp ((noLabelsFuns_eq_map fns).mp parts.1)
    let newFns := fns.map (fun (n, e) =>
      (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ env) g).1).1))
    have newBodies : ∀ e ∈ newFns.map Prod.snd, noLabels e := by
      intro transformed member
      obtain ⟨entry, inNew, valueEq⟩ := List.mem_map.mp member
      obtain ⟨⟨n, e⟩, inFns, entryEq⟩ := List.mem_map.mp inNew
      have bodySafe := originalBodies e (List.mem_map.mpr ⟨(n, e), inFns, rfl⟩)
      have bodyEnvSafe : ∀ a ∈ List.replicate n ValApprox.other ++ clos ++ env,
          valApproxNoLabels a := by
        intro a mem
        rw [List.append_assoc] at mem
        rcases List.mem_append.mp mem with inRep | inRest
        · have eq : a = .other := (List.mem_replicate.mp inRep).2
          subst a; simp [valApproxNoLabels]
        · exact closEnvSafe a inRest
      cases he : knownListTotal c [e] (List.replicate n .other ++ clos ++ env) g with
      | mk ea ge =>
        obtain ⟨e', a', eaEq⟩ := knownListTotal_single_result c e _ g ge ea he
        subst ea
        have result := ifuns n e inFns [(e', a')] ge he (by simpa using bodySafe) bodyEnvSafe globalSafe
        change (n, (knownSourceHead (knownListTotal c [e] (List.replicate n .other ++ clos ++ env) g).1).1) = entry at entryEq
        simp [knownSourceHead] at entryEq
        subst entry
        subst transformed
        simpa [← List.append_assoc, he, knownSourceHead] using result.1
    have newFnsSafe : noLabelsFuns newFns :=
      (noLabelsFuns_eq_map _).mpr ((noLabelsList_iff _).mpr newBodies)
    have bodyRun : knownListTotal c [body] (clos ++ env) g = ([(be, ba)], g1) := by
      simp [knownListTotal_single, hb]
    have result := ibody _ _ bodyRun (by simpa using parts.2) closEnvSafe globalSafe
    have bodyOut : noLabels be := result.1 be (by simp)
    have approxOut : valApproxNoLabels ba := result.2.1 ba (by simp)
    rw [knownListTotal_letrec] at run
    dsimp only at run
    cases loc <;> simp_all [clos, noInline, newFns, knownSourceHead, noLabels]
    all_goals rcases run with ⟨rfl, rfl⟩
    all_goals simp_all [noLabels]
    all_goals exact ⟨bodyOut, approxOut⟩
  case case14 => contradiction
  case case15 =>
    rename_i c clos env g arity body fns e a g1 hb ihBody ihRest n x member
    rcases List.mem_cons.mp member with same | tail
    · cases Prod.mk.inj same with
      | intro hn hx => subst n; subst x; exact ihBody
    · exact ihRest n x tail
  case case16 c env g =>
    intro eas next run _ _ safe
    simp [knownListTotal] at run
    rcases run with ⟨rfl, rfl⟩
    simpa using safe
  case case17 =>
    rename_i c env g x xs xe xa g1 hx tailEa g2 ht ix it
    cases xs with
    | nil => exact ix
    | cons y ys =>
      intro eas next run inputSafe envSafe globalSafe
      have headRun : knownListTotal c [x] env g = ([(xe, xa)], g1) := by
        simp [knownListTotal_single, hx]
      have headSafe : ∀ e ∈ [x], noLabels e := by
        simpa using inputSafe x (by simp)
      have tailSafe : ∀ e ∈ y :: ys, noLabels e := by
        intro e mem
        exact inputSafe e (by simp [mem])
      have headResult := ix [(xe, xa)] g1 headRun headSafe envSafe globalSafe
      have tailResult := it tailEa g2 ht tailSafe envSafe headResult.2.2
      rw [knownListTotal_cons_cons, headRun] at run
      dsimp only at run
      rw [ht] at run
      simp only [Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      simp only [List.cons_append, List.nil_append, List.map_cons, List.mem_cons, forall_eq_or_imp]
      exact ⟨⟨headResult.1 xe (by simp), tailResult.1⟩,
        ⟨headResult.2.1 xa (by simp), tailResult.2.1⟩, tailResult.2.2⟩

/-- The known-function traversal preserves all three label-free invariants. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_no_Labels"]
theorem knownNoLabels (c : Config) (xs : List Exp) (env : List ValApprox)
    (globals : Spt ValApprox)
    (h : (∀ e ∈ xs, noLabels e) ∧
      (∀ a ∈ env, valApproxNoLabels a) ∧ globalsApproxNoLabels globals) :
    (∀ e ∈ (knownListTotal c xs env globals).1.map Prod.fst, noLabels e) ∧
    (∀ a ∈ (knownListTotal c xs env globals).1.map Prod.snd, valApproxNoLabels a) ∧
    globalsApproxNoLabels (knownListTotal c xs env globals).2 := by
  cases run : knownListTotal c xs env globals with
  | mk eas next =>
    have result := work c xs env globals eas next run h.1 h.2.1 h.2.2
    simpa [run] using result

end Flapjack.Compiler.Backend.ClosKnown
