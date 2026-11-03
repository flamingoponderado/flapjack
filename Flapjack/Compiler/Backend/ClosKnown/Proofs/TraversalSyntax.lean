import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxSyntax
import Flapjack.Compiler.Backend.ClosKnown.Proofs.SourceEquations
import Flapjack.Compiler.Backend.ClosKnown.Proofs.Syntax
import Flapjack.Compiler.Backend.ClosOp.Proofs.SmartAnnotations

/-! Annotation preservation cases for the known-function traversal. -/
namespace Flapjack.Compiler.Backend.ClosKnown.TraversalSyntax
open ClosProps

/-- Factoring the source invariant through the traversal result makes the
result-dependent induction hypotheses explicit. -/
def KnownVarsInvariant (c : Config) (es : List ClosLang.Exp) (env : List ValApprox)
    (globals : Spt ValApprox) : Prop :=
  ∀ eas next, knownListTotal c es env globals = (eas, next) ∧ everyFnVarsNone es ∧
    (∀ a ∈ env, valApproxVarsNone a) ∧ globalsApproxVarsNone globals →
    everyFnVarsNone (eas.map Prod.fst) ∧
    (∀ a ∈ eas.map Prod.snd, valApproxVarsNone a) ∧ globalsApproxVarsNone next

/-- Empty-list case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_vs_NONE"]
theorem knownVarsNil (c : Config) (env : List ValApprox) (globals : Spt ValApprox) :
    KnownVarsInvariant c [] env globals := by
  intro eas next ⟨run, _, _, safe⟩
  simp [knownListTotal] at run
  rcases run with ⟨rfl, rfl⟩
  simp [everyFnVarsNone, safe]

/-- Variable case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_vs_NONE"]
theorem knownVarsVar (c : Config) (trace : BackendCommon.Tra) (index : Nat)
    (env : List ValApprox) (globals : Spt ValApprox) :
    KnownVarsInvariant c [.var trace index] env globals := by
  intro eas next ⟨run, _, safe, globalSafe⟩
  simp only [knownListTotal_var, Prod.mk.injEq] at run
  rcases run with ⟨rfl, rfl⟩
  have selected : valApproxVarsNone (env[index]?.getD .other) := by
    cases found : env[index]? with
    | none => simp [valApproxVarsNone]
    | some a => exact safe a (List.mem_of_getElem? found)
  simp [everyFnVarsNone, fnVarsNoneExp, selected, globalSafe]

/-- Sequential-list case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_vs_NONE"]
theorem knownVarsCons (c : Config) (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox)
    (tailIH : ∀ ea1 g1, (ea1, g1) = knownListTotal c [x] env globals →
      KnownVarsInvariant c (y :: xs) env g1)
    (headIH : KnownVarsInvariant c [x] env globals) :
    KnownVarsInvariant c (x :: y :: xs) env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have parts : everyFnVarsNone [x] ∧ everyFnVarsNone (y :: xs) := by
    simpa [everyFnVarsNone] using annotations
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
      · simpa [List.map_append, everyFnVarsNone_append] using And.intro headExp tailExp
      · simpa only [List.map_append, List.mem_append, or_imp, forall_and] using ⟨headVal, tailVal⟩

/-- Raise case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_vs_NONE"]
theorem knownVarsRaise (c : Config) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox) (bodyIH : KnownVarsInvariant c [body] env globals) :
    KnownVarsInvariant c [.raise trace body] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have bodySafe : everyFnVarsNone [body] := by simpa [everyFnVarsNone, fnVarsNoneExp] using annotations
  cases hk : knownListTotal c [body] env globals with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body env globals bodyG bodyEas hk
    subst bodyEas
    have result := bodyIH [(bodyExpr, bodyApprox)] bodyG ⟨hk, bodySafe, safe, globalSafe⟩
    rw [knownListTotal_raise, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [everyFnVarsNone, fnVarsNoneExp, valApproxVarsNone] using And.intro result.1 result.2.2

/-- Tick case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_vs_NONE"]
theorem knownVarsTick (c : Config) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox) (bodyIH : KnownVarsInvariant c [body] env globals) :
    KnownVarsInvariant c [.tick trace body] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have bodySafe : everyFnVarsNone [body] := by simpa [everyFnVarsNone, fnVarsNoneExp] using annotations
  cases hk : knownListTotal c [body] env globals with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body env globals bodyG bodyEas hk
    subst bodyEas
    have result := bodyIH [(bodyExpr, bodyApprox)] bodyG ⟨hk, bodySafe, safe, globalSafe⟩
    rw [knownListTotal_tickSource, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [everyFnVarsNone, fnVarsNoneExp] using result

/-- Direct-call case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_vs_NONE"]
theorem knownVarsCall (c : Config) (trace : BackendCommon.Tra) (ticks dest : Nat)
    (xs : List ClosLang.Exp) (env : List ValApprox) (globals : Spt ValApprox)
    (argsIH : KnownVarsInvariant c xs env globals) :
    KnownVarsInvariant c [.call trace ticks dest xs] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have argsSafe : everyFnVarsNone xs := by simpa [everyFnVarsNone, fnVarsNoneExp] using annotations
  cases hk : knownListTotal c xs env globals with
  | mk ea g1 =>
    have result := argsIH ea g1 ⟨hk, argsSafe, safe, globalSafe⟩
    rw [knownListTotal_call, hk] at run
    simp at run
    rcases run with ⟨rfl, rfl⟩
    simpa [everyFnVarsNone, fnVarsNoneExp, valApproxVarsNone] using And.intro result.1 result.2.2

/-- Primitive-operation case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_vs_NONE"]
theorem knownVarsOp (c : Config) (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (xs : List ClosLang.Exp) (env : List ValApprox) (globals : Spt ValApprox)
    (argsIH : KnownVarsInvariant c xs env globals) :
    KnownVarsInvariant c [.op trace op xs] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have argsSafe : everyFnVarsNone xs := by simpa [everyFnVarsNone, fnVarsNoneExp] using annotations
  cases hk : knownListTotal c xs env globals with
  | mk ea g1 =>
    have result := argsIH ea g1 ⟨hk, argsSafe, safe, globalSafe⟩
    have reverseSafe : ∀ a ∈ (ea.map Prod.snd).reverse, valApproxVarsNone a := by
      intro a member
      exact result.2.1 a (List.mem_reverse.mp member)
    cases hop : knownOpHOL op (ea.map Prod.snd).reverse g1 with
    | mk approx g2 =>
      have opSafe := knownOpVarsNone op (ea.map Prod.snd).reverse g1 approx g2
        ⟨hop, reverseSafe, result.2.2⟩
      rw [knownListTotal_op, hk] at run
      dsimp only at run
      rw [hop] at run
      dsimp only at run
      let out := match op, approx with
        | .globOp (.global _), .int i => ClosLang.Exp.op trace (.intOp (.const i)) (ea.map Prod.fst)
        | .globOp (.global _), .tuple tag [] => ClosLang.Exp.op trace (.blockOp (.cons tag)) (ea.map Prod.fst)
        | _, _ => ClosOp.smartOp trace op (ea.map Prod.fst)
      have outSafe : everyFnVarsNone [out] := by
        dsimp only [out]
        split
        · simpa [everyFnVarsNone, fnVarsNoneExp] using result.1
        · simpa [everyFnVarsNone, fnVarsNoneExp] using result.1
        · exact ClosOp.smartNone trace op _ result.1
      change ([(out, approx)], g2) = (eas, next) at run
      cases run
      simpa using And.intro outSafe opSafe

/-- Conditional case of the source optimizer annotation invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_every_Fn_vs_NONE"]
theorem knownVarsIf (c : Config) (trace : BackendCommon.Tra) (x y z : ClosLang.Exp)
    (env : List ValApprox) (globals : Spt ValApprox)
    (thirdIH : ∀ ea1 g1 ea2 g2, (ea1, g1) = knownListTotal c [x] env globals ∧
      (ea2, g2) = knownListTotal c [y] env g1 → KnownVarsInvariant c [z] env g2)
    (secondIH : ∀ ea1 g1, (ea1, g1) = knownListTotal c [x] env globals → KnownVarsInvariant c [y] env g1)
    (firstIH : KnownVarsInvariant c [x] env globals) :
    KnownVarsInvariant c [.ifThenElse trace x y z] env globals := by
  intro eas next ⟨run, annotations, safe, globalSafe⟩
  have parts : everyFnVarsNone [x] ∧ everyFnVarsNone [y] ∧ everyFnVarsNone [z] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using annotations
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
        have merged : valApproxVarsNone (mergeHOL a2 a3) := valApproxVarsNoneMerge a2 a3
          ⟨by simpa using r2.2.1, by simpa using r3.2.1⟩
        simp [everyFnVarsNone, fnVarsNoneExp] at r1 r2 r3 ⊢
        exact ⟨⟨r1.1, r2.1, r3.1⟩, merged, r3.2.2⟩

end Flapjack.Compiler.Backend.ClosKnown.TraversalSyntax
