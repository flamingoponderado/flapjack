module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxLocations
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.SourceEquations
public import Flapjack.Compiler.Backend.ClosKnown.Proofs.Syntax
public import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartAnnotations

@[expose] public section

/-! Annotation preservation cases for the known-function traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown.TraversalLocations
open ClosProps

private theorem everyFnLocationSome_append (xs ys : List ClosLang.Exp) :
    everyFnLocationSome (xs ++ ys) ↔ everyFnLocationSome xs ∧ everyFnLocationSome ys := by
  induction xs with
  | nil => simp [everyFnLocationSome]
  | cons x xs ih => simp [everyFnLocationSome, ih, and_assoc]

/-- Factoring the source invariant through the traversal result makes the
result-dependent induction hypotheses explicit. -/
def KnownLocationsInvariant (c : Config) (es : List ClosLang.Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : Prop :=
  ∀ eas next, knownListTotal c es env globals = (eas, next) ∧ everyFnLocationSome es ∧
    (∀ a ∈ env, valApproxLocations a) ∧ globalsApproxLocations globals →
    everyFnLocationSome (eas.map Prod.fst) ∧
    (∀ a ∈ eas.map Prod.snd, valApproxLocations a) ∧ globalsApproxLocations next

/-- Empty-list case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsNil (c : Config) (env : List ValApprox) (globals : Spt ValApprox) :
    KnownLocationsInvariant c [] env globals := by
  intro eas next ⟨run, _, _, safe⟩
  simp [knownListTotal] at run
  rcases run with ⟨rfl, rfl⟩
  simp [everyFnLocationSome, safe]

/-- Variable case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsVar (c : Config) (trace : BackendCommon.Tra) (index : Nat)
    (env : List ValApprox) (globals : Spt ValApprox) :
    KnownLocationsInvariant c [.var trace index] env globals := by
  intro eas next ⟨run, _, safe, globalSafe⟩
  simp only [knownListTotal_var, Prod.mk.injEq] at run
  rcases run with ⟨rfl, rfl⟩
  have selected : valApproxLocations (env[index]?.getD .other) := by
    cases found : env[index]? with
    | none => simp [valApproxLocations]
    | some a => exact safe a (List.mem_of_getElem? found)
  simp [everyFnLocationSome, fnLocationSomeExp, selected, globalSafe]

/-- Sequential-list case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsCons (c : Config) (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox)
    (tailIH : ∀ ea1 g1, (ea1, g1) = knownListTotal c [x] env globals →
      KnownLocationsInvariant c (y :: xs) env g1)
    (headIH : KnownLocationsInvariant c [x] env globals) :
    KnownLocationsInvariant c (x :: y :: xs) env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have parts : everyFnLocationSome [x] ∧ everyFnLocationSome (y :: xs) := by
    simpa [everyFnLocationSome] using annotations
  have headSyntax := parts.1
  have tailSyntax := parts.2
  cases headRun : knownListTotal c [x] env globals with
  | mk headEas g1 =>
    cases tailRun : knownListTotal c (y :: xs) env g1 with
    | mk tailEas g2 =>
      rw [knownListTotal_cons_cons, headRun] at run
      dsimp only at run
      rw [tailRun] at run
      simp only [Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨headExp, headVal, headGlobal⟩ := headIH headEas g1 ⟨headRun, headSyntax, safe, globalSafe⟩
      obtain ⟨tailExp, tailVal, tailGlobal⟩ :=
        tailIH headEas g1 headRun.symm tailEas g2 ⟨tailRun, tailSyntax, safe, headGlobal⟩
      refine ⟨?_, ?_, tailGlobal⟩
      · simpa [List.map_append, everyFnLocationSome_append] using And.intro headExp tailExp
      · simpa only [List.map_append, List.mem_append, or_imp, forall_and] using ⟨headVal, tailVal⟩

/-- Raise case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsRaise (c : Config) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox) (bodyIH : KnownLocationsInvariant c [body] env globals) :
    KnownLocationsInvariant c [.raise trace body] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have bodySafe : everyFnLocationSome [body] := by simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
  cases hk : knownListTotal c [body] env globals with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body env globals bodyG bodyEas hk
    subst bodyEas
    have result := bodyIH [(bodyExpr, bodyApprox)] bodyG ⟨hk, bodySafe, safe, globalSafe⟩
    rw [knownListTotal_raise, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [everyFnLocationSome, fnLocationSomeExp, valApproxLocations] using And.intro result.1 result.2.2

/-- Tick case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsTick (c : Config) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox) (bodyIH : KnownLocationsInvariant c [body] env globals) :
    KnownLocationsInvariant c [.tick trace body] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have bodySafe : everyFnLocationSome [body] := by simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
  cases hk : knownListTotal c [body] env globals with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body env globals bodyG bodyEas hk
    subst bodyEas
    have result := bodyIH [(bodyExpr, bodyApprox)] bodyG ⟨hk, bodySafe, safe, globalSafe⟩
    rw [knownListTotal_tickSource, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [everyFnLocationSome, fnLocationSomeExp] using result

/-- Direct-call case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsCall (c : Config) (trace : BackendCommon.Tra) (ticks dest : Nat)
    (xs : List ClosLang.Exp) (env : List ValApprox) (globals : Spt ValApprox)
    (argsIH : KnownLocationsInvariant c xs env globals) :
    KnownLocationsInvariant c [.call trace ticks dest xs] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have argsSafe : everyFnLocationSome xs := by simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
  cases hk : knownListTotal c xs env globals with
  | mk ea g1 =>
    have result := argsIH ea g1 ⟨hk, argsSafe, safe, globalSafe⟩
    rw [knownListTotal_call, hk] at run
    simp at run
    rcases run with ⟨rfl, rfl⟩
    simpa [everyFnLocationSome, fnLocationSomeExp, valApproxLocations] using And.intro result.1 result.2.2

/-- Primitive-operation case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsOp (c : Config) (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (xs : List ClosLang.Exp) (env : List ValApprox) (globals : Spt ValApprox)
    (argsIH : KnownLocationsInvariant c xs env globals) :
    KnownLocationsInvariant c [.op trace op xs] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have argsSafe : everyFnLocationSome xs := by simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
  cases hk : knownListTotal c xs env globals with
  | mk ea g1 =>
    have result := argsIH ea g1 ⟨hk, argsSafe, safe, globalSafe⟩
    have reverseSafe : ∀ a ∈ (ea.map Prod.snd).reverse, valApproxLocations a := by
      intro a member
      exact result.2.1 a (List.mem_reverse.mp member)
    cases hop : knownOpHOL op (ea.map Prod.snd).reverse g1 with
    | mk approx g2 =>
      have opSafe := knownOpLocations op (ea.map Prod.snd).reverse g1 approx g2
        ⟨hop, reverseSafe, result.2.2⟩
      rw [knownListTotal_op, hk] at run
      dsimp only at run
      rw [hop] at run
      dsimp only at run
      let out := match op, approx with
        | .globOp (.global _), .int i => ClosLang.Exp.op trace (.intOp (.const i)) (ea.map Prod.fst)
        | .globOp (.global _), .tuple tag [] => ClosLang.Exp.op trace (.blockOp (.cons tag)) (ea.map Prod.fst)
        | _, _ => ClosOp.smartOp trace op (ea.map Prod.fst)
      have outSafe : everyFnLocationSome [out] := by
        dsimp only [out]
        split
        · simpa [everyFnLocationSome, fnLocationSomeExp] using result.1
        · simpa [everyFnLocationSome, fnLocationSomeExp] using result.1
        · apply (ClosOp.smartSome trace op _).mpr
          simpa [everyFnLocationSome, fnLocationSomeExp] using result.1
      change ([(out, approx)], g2) = (eas, next) at run
      cases run
      simpa using And.intro outSafe opSafe

/-- Conditional case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsIf (c : Config) (trace : BackendCommon.Tra) (x y z : ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox)
    (thirdIH : ∀ ea1 g1 ea2 g2, (ea1, g1) = knownListTotal c [x] env globals ∧
      (ea2, g2) = knownListTotal c [y] env g1 → KnownLocationsInvariant c [z] env g2)
    (secondIH : ∀ ea1 g1, (ea1, g1) = knownListTotal c [x] env globals → KnownLocationsInvariant c [y] env g1)
    (firstIH : KnownLocationsInvariant c [x] env globals) :
    KnownLocationsInvariant c [.ifThenElse trace x y z] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have parts : everyFnLocationSome [x] ∧ everyFnLocationSome [y] ∧ everyFnLocationSome [z] := by
    simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
  cases h1 : knownListTotal c [x] env globals with
  | mk ea1 g1 =>
    obtain ⟨x', a1, eq1⟩ := knownListTotal_single_result c x env globals g1 ea1 h1
    subst ea1
    have r1 := firstIH [(x', a1)] g1 ⟨h1, parts.1, safe, globalSafe⟩
    cases h2 : knownListTotal c [y] env g1 with
    | mk ea2 g2 =>
      obtain ⟨y', a2, eq2⟩ := knownListTotal_single_result c y env g1 g2 ea2 h2
      subst ea2
      have r2 := secondIH [(x', a1)] g1 h1.symm [(y', a2)] g2 ⟨h2, parts.2.1, safe, r1.2.2⟩
      cases h3 : knownListTotal c [z] env g2 with
      | mk ea3 g3 =>
        obtain ⟨z', a3, eq3⟩ := knownListTotal_single_result c z env g2 g3 ea3 h3
        subst ea3
        have r3 := thirdIH [(x', a1)] g1 [(y', a2)] g2 ⟨h1.symm, h2.symm⟩ [(z', a3)] g3
          ⟨h3, parts.2.2, safe, r2.2.2⟩
        rw [knownListTotal_if, h1] at run
        dsimp only at run
        rw [h2] at run
        dsimp only at run
        rw [h3] at run
        simp [knownSourceHead] at run
        rcases run with ⟨rfl, rfl⟩
        have merged : valApproxLocations (mergeHOL a2 a3) := valApproxLocationsMerge a2 a3
          ⟨by simpa using r2.2.1, by simpa using r3.2.1⟩
        simp [everyFnLocationSome, fnLocationSomeExp] at r1 r2 r3 ⊢
        exact ⟨⟨r1.1, r2.1, r3.1⟩, merged, r3.2.2⟩

/-- Let-binding case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsLet (c : Config) (trace : BackendCommon.Tra) (xs : List ClosLang.Exp)
    (body : ClosLang.Exp) (env : List ValApprox) (globals : Spt ValApprox)
    (bodyIH : ∀ ea g, (ea, g) = knownListTotal c xs env globals →
      KnownLocationsInvariant c [body] (ea.map Prod.snd ++ env) g)
    (bindingsIH : KnownLocationsInvariant c xs env globals) :
    KnownLocationsInvariant c [.let trace xs body] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have parts : everyFnLocationSome xs ∧ everyFnLocationSome [body] := by
    simpa [everyFnLocationSome, fnLocationSomeExp, and_comm] using annotations
  cases h1 : knownListTotal c xs env globals with
  | mk ea1 g1 =>
    have r1 := bindingsIH ea1 g1 ⟨h1, parts.1, safe, globalSafe⟩
    have bodyEnvSafe : ∀ a ∈ ea1.map Prod.snd ++ env, valApproxLocations a := by
      intro a member
      rcases List.mem_append.mp member with inArgs | inEnv
      · exact r1.2.1 a inArgs
      · exact safe a inEnv
    cases h2 : knownListTotal c [body] (ea1.map Prod.snd ++ env) g1 with
    | mk ea2 g2 =>
      obtain ⟨bodyExpr, bodyApprox, eq2⟩ :=
        knownListTotal_single_result c body (ea1.map Prod.snd ++ env) g1 g2 ea2 h2
      subst ea2
      have r2 := bodyIH ea1 g1 h1.symm [(bodyExpr, bodyApprox)] g2
        ⟨h2, parts.2, bodyEnvSafe, r1.2.2⟩
      rw [knownListTotal_let, h1] at run
      dsimp only at run
      rw [h2] at run
      simp [knownSourceHead] at run
      rcases run with ⟨rfl, rfl⟩
      simp [everyFnLocationSome, fnLocationSomeExp] at r2 ⊢
      exact ⟨⟨r2.1, r1.1⟩, r2.2.1, r2.2.2⟩

/-- Handler case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsHandle (c : Config) (trace : BackendCommon.Tra) (body handler : ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox)
    (handlerIH : ∀ ea g, (ea, g) = knownListTotal c [body] env globals →
      KnownLocationsInvariant c [handler] (.other :: env) g)
    (bodyIH : KnownLocationsInvariant c [body] env globals) :
    KnownLocationsInvariant c [.handle trace body handler] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have parts : everyFnLocationSome [body] ∧ everyFnLocationSome [handler] := by
    simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
  cases h1 : knownListTotal c [body] env globals with
  | mk ea1 g1 =>
    obtain ⟨e1, a1, eq1⟩ := knownListTotal_single_result c body env globals g1 ea1 h1
    subst ea1
    have r1 := bodyIH [(e1, a1)] g1 ⟨h1, parts.1, safe, globalSafe⟩
    have newEnvSafe : ∀ a ∈ ValApprox.other :: env, valApproxLocations a := by
      intro a member
      rcases List.mem_cons.mp member with same | old
      · subst a; simp [valApproxLocations]
      · exact safe a old
    cases h2 : knownListTotal c [handler] (.other :: env) g1 with
    | mk ea2 g2 =>
      obtain ⟨e2, a2, eq2⟩ := knownListTotal_single_result c handler (.other :: env) g1 g2 ea2 h2
      subst ea2
      have r2 := handlerIH [(e1, a1)] g1 h1.symm [(e2, a2)] g2 ⟨h2, parts.2, newEnvSafe, r1.2.2⟩
      rw [knownListTotal_handle, h1] at run
      dsimp only at run
      rw [h2] at run
      simp [knownSourceHead] at run
      rcases run with ⟨rfl, rfl⟩
      have merged := valApproxLocationsMerge a1 a2 ⟨by simpa using r1.2.1, by simpa using r2.2.1⟩
      simp [everyFnLocationSome, fnLocationSomeExp] at r1 r2 ⊢
      exact ⟨⟨r1.1, r2.1⟩, merged, r2.2.2⟩

/-- Closure-construction case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsFn (c : Config) (name : Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vs : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox)
    (bodyIH : KnownLocationsInvariant c [body] (List.replicate arity .other ++ env) globals) :
    KnownLocationsInvariant c [.fn name loc vs arity body] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have parts : loc.isSome ∧ everyFnLocationSome [body] := by
    simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
  have bodyEnvSafe : ∀ a ∈ List.replicate arity ValApprox.other ++ env, valApproxLocations a := by
    intro a member
    rcases List.mem_append.mp member with replicated | old
    · have equal : a = .other := (List.mem_replicate.mp replicated).2
      subst a
      simp [valApproxLocations]
    · exact safe a old
  cases hk : knownListTotal c [body] (List.replicate arity .other ++ env) globals with
  | mk ea g1 =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ :=
      knownListTotal_single_result c body (List.replicate arity .other ++ env) globals g1 ea hk
    subst ea
    have result := bodyIH [(bodyExpr, bodyApprox)] g1 ⟨hk, parts.2, bodyEnvSafe, globalSafe⟩
    rw [knownListTotal_fn, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    have outSafe : everyFnLocationSome [.fn name loc none arity bodyExpr] := by
      simpa [everyFnLocationSome, fnLocationSomeExp, parts.1] using result.1
    refine ⟨outSafe, ?_, result.2.2⟩
    cases loc with
    | none => simp [valApproxLocations]
    | some loc =>
      simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq]
      unfold closApproxHOL
      split <;> simp [valApproxLocations, parts.2]

/-- Tick insertion preserves the closure annotation predicate. -/
private theorem ticksLocations (trace : BackendCommon.Tra) (index n : Nat) (e : ClosLang.Exp) :
    everyFnLocationSome [ticks trace index n e] ↔ everyFnLocationSome [e] := by
  induction n generalizing index e with
  | zero => rfl
  | succ n ih =>
    simpa [ticks, everyFnLocationSome, fnLocationSomeExp] using
      (ih (index + 1) (.tick (BackendCommon.mkCons trace index) e))

/-- Application case of the source optimizer annotation invariant, including
the recursive inlining branch. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsApp (c : Config) (trace : BackendCommon.Tra) (loc : Option Nat)
    (x : ClosLang.Exp) (xs : List ClosLang.Exp) (env : List ValApprox) (globals : Spt ValApprox)
    (inlineIH : ∀ ea2 g1 ea1 g2 e1 a1 body,
      (ea2, g1) = knownListTotal c xs env globals ∧ (ea1, g2) = knownListTotal c [x] env g1 ∧
      (e1, a1) = knownSourceHead ea1 ∧ decideInlineHOL c a1 loc xs.length = .letInline body →
      KnownLocationsInvariant (decInlineFactor c) [body] (ea2.map Prod.snd) g2)
    (functionIH : ∀ ea2 g1, (ea2, g1) = knownListTotal c xs env globals → KnownLocationsInvariant c [x] env g1)
    (argsIH : KnownLocationsInvariant c xs env globals) :
    KnownLocationsInvariant c [.app trace loc x xs] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have parts : everyFnLocationSome [x] ∧ everyFnLocationSome xs := by
    simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
  cases ha : knownListTotal c xs env globals with
  | mk ea2 g1 =>
    have rArgs := argsIH ea2 g1 ⟨ha, parts.2, safe, globalSafe⟩
    cases hf : knownListTotal c [x] env g1 with
    | mk ea1 g2 =>
      obtain ⟨e1, a1, eq1⟩ := knownListTotal_single_result c x env g1 g2 ea1 hf
      subst ea1
      have rFun := functionIH ea2 g1 ha.symm [(e1, a1)] g2 ⟨hf, parts.1, safe, rArgs.2.2⟩
      have e1Safe : everyFnLocationSome [e1] := by simpa using rFun.1
      have a1Safe : valApproxLocations a1 := by simpa using rFun.2.1
      rw [knownListTotal_app, ha] at run
      dsimp only at run
      rw [hf] at run
      simp only [knownSourceHead, List.headD_cons] at run
      cases decision : decideInlineHOL c a1 loc xs.length with
      | nothing =>
        simp only [decision, Prod.mk.injEq] at run
        rcases run with ⟨rfl, rfl⟩
        simpa [everyFnLocationSome, fnLocationSomeExp, valApproxLocations] using
          And.intro (And.intro e1Safe rArgs.1) rFun.2.2
      | annotate target =>
        simp only [decision, Prod.mk.injEq] at run
        rcases run with ⟨rfl, rfl⟩
        simpa [everyFnLocationSome, fnLocationSomeExp, valApproxLocations] using
          And.intro (And.intro e1Safe rArgs.1) rFun.2.2
      | letInline body =>
        have bodySafe := decideInlineLocations c a1 loc xs.length body ⟨a1Safe, decision⟩
        have bodyInvariant := inlineIH ea2 g1 [(e1, a1)] g2 e1 a1 body
          ⟨ha.symm, hf.symm, by simp [knownSourceHead], decision⟩
        cases hb : knownListTotal (decInlineFactor c) [body] (ea2.map Prod.snd) g2 with
        | mk inlineEa inlineG =>
          obtain ⟨inlineExpr, inlineApprox, eqBody⟩ :=
            knownListTotal_single_result (decInlineFactor c) body (ea2.map Prod.snd) g2 inlineG inlineEa hb
          subst inlineEa
          have rBody := bodyInvariant [(inlineExpr, inlineApprox)] inlineG ⟨hb, bodySafe, rArgs.2.1, rFun.2.2⟩
          have inlineSafe : everyFnLocationSome [inlineExpr] := by simpa using rBody.1
          have tickSafe := (ticksLocations trace 1 xs.length inlineExpr).mpr inlineSafe
          simp only [decision] at run
          rw [hb] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          have argSafe : everyFnLocationSome (if ClosLang.pure x then ea2.map Prod.fst else ea2.map Prod.fst ++ [e1]) := by
            split
            · exact rArgs.1
            · exact (everyFnLocationSome_append _ _).mpr ⟨rArgs.1, e1Safe⟩
          simp [everyFnLocationSome, fnLocationSomeExp] at tickSafe rBody ⊢
          exact ⟨⟨tickSafe, argSafe⟩, rBody.2.1, rFun.2.2⟩

/-- Recursive-closure case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_SOME"]
theorem knownLocationsLetrec (c : Config) (names : List Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vs : Option (List Nat)) (fns : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env : List ValApprox) (globals : Spt ValApprox)
    (bodyIH : ∀ clos newFns,
      clos = (match loc with | none => List.replicate fns.length .other | some n => closGenNoInline n 0 fns) ∧
      newFns = fns.map (fun (n, e) =>
        (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ env) globals).1).1)) →
      KnownLocationsInvariant c [body] (clos ++ env) globals)
    (funsIH : ∀ clos arity e newEnv,
      clos = (match loc with | none => List.replicate fns.length .other | some n => closGenNoInline n 0 fns) ∧
      (arity, e) ∈ fns ∧ newEnv = List.replicate arity .other ++ clos ++ env →
      KnownLocationsInvariant c [e] newEnv globals) :
    KnownLocationsInvariant c [.letrec names loc vs fns body] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have parts : loc.isSome ∧ fnLocationSomeFuns fns ∧ everyFnLocationSome [body] := by
    simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
  let clos := match loc with
    | none => List.replicate fns.length ValApprox.other
    | some n => closGenNoInline n 0 fns
  let newFns := fns.map (fun (n, e) =>
    (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ env) globals).1).1))
  have closSafe : ∀ a ∈ clos, valApproxLocations a := by
    cases loc with
    | none => simp [clos, valApproxLocations]
    | some n => exact closGenNoInlineLocations fns 0 n
  have closEnvSafe : ∀ a ∈ clos ++ env, valApproxLocations a := by
    intro a member
    rcases List.mem_append.mp member with mem | mem
    · exact closSafe a mem
    · exact safe a mem
  have originalBodies : ∀ e ∈ fns.map Prod.snd, everyFnLocationSome [e] :=
    (everyFnLocationSome_every _).mp ((fnLocationSomeFuns_eq_map fns).mp parts.2.1)
  have newBodies : ∀ e ∈ newFns.map Prod.snd, everyFnLocationSome [e] := by
    intro transformed member
    obtain ⟨entry, inNew, valueEq⟩ := List.mem_map.mp member
    obtain ⟨⟨n, e⟩, inFns, entryEq⟩ := List.mem_map.mp inNew
    have bodySafe := originalBodies e (List.mem_map.mpr ⟨(n, e), inFns, rfl⟩)
    have bodyEnvSafe : ∀ a ∈ List.replicate n ValApprox.other ++ clos ++ env, valApproxLocations a := by
      intro a mem
      rw [List.append_assoc] at mem
      rcases List.mem_append.mp mem with inRep | inRest
      · have eq : a = .other := (List.mem_replicate.mp inRep).2
        subst a; simp [valApproxLocations]
      · exact closEnvSafe a inRest
    have ih := funsIH clos n e (List.replicate n ValApprox.other ++ clos ++ env)
      ⟨by cases loc <;> rfl, inFns, rfl⟩
    cases he : knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ env) globals with
    | mk ea ge =>
      obtain ⟨e', a', eaEq⟩ := knownListTotal_single_result c e _ globals ge ea he
      subst ea
      have result := ih [(e', a')] ge ⟨he, bodySafe, bodyEnvSafe, globalSafe⟩
      change (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ env) globals).1).1) = entry at entryEq
      simp [knownSourceHead] at entryEq
      subst entry
      subst transformed
      simpa [← List.append_assoc, he, knownSourceHead] using result.1
  have newFnsSafe : fnLocationSomeFuns newFns := (fnLocationSomeFuns_eq_map _).mpr ((everyFnLocationSome_every _).mpr newBodies)
  cases hb : knownListTotal c [body] (clos ++ env) globals with
  | mk ea gb =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body (clos ++ env) globals gb ea hb
    subst ea
    have result := bodyIH clos newFns ⟨by cases loc <;> rfl, rfl⟩ [(bodyExpr, bodyApprox)] gb
      ⟨hb, parts.2.2, closEnvSafe, globalSafe⟩
    rw [knownListTotal_letrec] at run
    change (let (ea, g) := knownListTotal c [body] (clos ++ env) globals
      let (e, a) := knownSourceHead ea
      ([(.letrec names loc none newFns e, a)], g)) = (eas, next) at run
    rw [hb] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simp [everyFnLocationSome, fnLocationSomeExp] at result ⊢
    exact ⟨⟨parts.1, newFnsSafe, result.1⟩, result.2.1, result.2.2⟩

end Flapjack.Compiler.Backend.ClosKnown.TraversalLocations
