import Flapjack.Compiler.Backend.ClosKnown.Proofs.SourceEquations
import Flapjack.Compiler.Backend.ClosKnown.Proofs.ApproxGlobalSafety
import Flapjack.Compiler.Backend.ClosKnown.Proofs.Syntax
import Flapjack.Compiler.Backend.ClosOp.Proofs.ReductionInvariants

/-! Safety preservation for the known-function optimization. -/
namespace Flapjack.Compiler.Backend.ClosKnown.PreserveSafety
open ClosProps


/-- Inserting ticks does not change an expression's global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "mk_Ticks_set_globals"]
theorem ticksSetGlobals (trace : BackendCommon.Tra) (index n : Nat) (e : ClosLang.Exp) :
    setGlobals (ticks trace index n e) = setGlobals e := by
  induction n generalizing index e with
  | zero => rfl
  | succ n ih => simpa [ticks, setGlobals] using ih (index + 1) (.tick (BackendCommon.mkCons trace index) e)

/-- Tick insertion retains closure-body safety; Flapjack infrastructure. -/
private theorem ticksEsgcFree (trace : BackendCommon.Tra) (index n : Nat) (e : ClosLang.Exp) :
    esgcFree (ticks trace index n e) ↔ esgcFree e := by
  induction n generalizing index e with
  | zero => rfl
  | succ n ih => simpa [ticks, esgcFree] using ih (index + 1) (.tick (BackendCommon.mkCons trace index) e)

/-- The source safety theorem after fixing optimizer inputs, used as its
induction predicate. This abbreviation has no separate HOL declaration. -/
def KnownSafetyInvariant (c : Config) (es : List ClosLang.Exp) (aenv : List ValApprox)
    (g0 : Spt ValApprox) : Prop :=
  ∀ (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox),
    knownListTotal c es aenv g0 = (eas, g) ∧ (∀ e ∈ es, esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0 →
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals es i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g

/-- The empty-list induction case for optimizer global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyNil (c : Config) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [] aenv g0 = (eas, g) ∧ (∀ e ∈ ([] : List ClosLang.Exp), esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨known, _, _, globals⟩
  simp [knownListTotal] at known
  rcases known with ⟨rfl, rfl⟩
  simp [globals]

/-- The variable induction case for optimizer global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyVar (c : Config) (trace : BackendCommon.Tra) (index : Nat)
    (aenv : List ValApprox) (g0 : Spt ValApprox) (eas : List (ClosLang.Exp × ValApprox))
    (g : Spt ValApprox)
    (h : knownListTotal c [.var trace index] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.var trace index], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.var trace index] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨known, _, safe, globals⟩
  simp only [knownListTotal_var, Prod.mk.injEq] at known
  rcases known with ⟨rfl, rfl⟩
  have selected : valApproxSgcFree (aenv[index]?.getD .other) := by
    cases found : aenv[index]? with
    | none => simp [valApproxSgcFree]
    | some a =>
      exact safe a (List.mem_of_getElem? found)
  simp [esgcFree, selected, globals]

/-- Sequential-list induction case for optimizer global safety. The hypotheses
are the original head and result-dependent tail induction hypotheses. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyCons (c : Config) (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (aenv : List ValApprox) (g0 : Spt ValApprox)
    (tailIH : ∀ (ea1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea1, g1) = knownListTotal c [x] aenv g0 → KnownSafetyInvariant c (y :: xs) aenv g1)
    (headIH : KnownSafetyInvariant c [x] aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c (x :: y :: xs) aenv g0 = (eas, g) ∧
      (∀ e ∈ x :: y :: xs, esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals (x :: y :: xs) i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have headSafe : ∀ e ∈ [x], esgcFree e := by simpa using safe x (by simp)
  have tailSafe : ∀ e ∈ y :: xs, esgcFree e := by
    intro e member
    exact safe e (List.mem_cons_of_mem _ member)
  cases headRun : knownListTotal c [x] aenv g0 with
  | mk headEas g1 =>
    cases tailRun : knownListTotal c (y :: xs) aenv g1 with
    | mk tailEas g2 =>
      rw [knownListTotal_cons_cons, headRun] at run
      dsimp only at run
      rw [tailRun] at run
      simp only [Prod.mk.injEq] at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨headBound, headExpSafe, headValSafe, headGlobals⟩ :=
        headIH headEas g1 ⟨headRun, headSafe, envSafe, globalSafe⟩
      obtain ⟨tailBound, tailExpSafe, tailValSafe, tailGlobals⟩ :=
        tailIH headEas g1 headRun.symm tailEas g2 ⟨tailRun, tailSafe, envSafe, headGlobals⟩
      refine ⟨?_, ?_, ?_, tailGlobals⟩
      · intro i
        change elistGlobals ((headEas ++ tailEas).map Prod.fst) i ≤
          elistGlobals ([x] ++ (y :: xs)) i
        simp only [List.map_append, elistGlobals_append]
        have h1 := headBound i
        have h2 := tailBound i
        omega
      · simpa only [List.map_append, List.mem_append, or_imp, forall_and] using ⟨headExpSafe, tailExpSafe⟩
      · simpa only [List.map_append, List.mem_append, or_imp, forall_and] using ⟨headValSafe, tailValSafe⟩

/-- Raise induction case for optimizer global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyRaise (c : Config) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (aenv : List ValApprox) (g0 : Spt ValApprox) (bodyIH : KnownSafetyInvariant c [body] aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [.raise trace body] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.raise trace body], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.raise trace body] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have bodySafe : ∀ e ∈ [body], esgcFree e := by
    have h := safe (.raise trace body) (by simp)
    simpa [esgcFree] using h
  cases hk : knownListTotal c [body] aenv g0 with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body aenv g0 bodyG bodyEas hk
    subst bodyEas
    have result := bodyIH [(bodyExpr, bodyApprox)] bodyG ⟨hk, bodySafe, envSafe, globalSafe⟩
    rw [knownListTotal_raise, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, result.2.2.2⟩
    · simpa [elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] using result.1
    · simpa [esgcFree] using result.2.1
    · simp [valApproxSgcFree]

/-- Tick induction case for optimizer global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyTick (c : Config) (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (aenv : List ValApprox) (g0 : Spt ValApprox) (bodyIH : KnownSafetyInvariant c [body] aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [.tick trace body] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.tick trace body], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.tick trace body] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have bodySafe : ∀ e ∈ [body], esgcFree e := by
    have h := safe (.tick trace body) (by simp)
    simpa [esgcFree] using h
  cases hk : knownListTotal c [body] aenv g0 with
  | mk bodyEas bodyG =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body aenv g0 bodyG bodyEas hk
    subst bodyEas
    have result := bodyIH [(bodyExpr, bodyApprox)] bodyG ⟨hk, bodySafe, envSafe, globalSafe⟩
    rw [knownListTotal_tickSource, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    simpa [elistGlobals, setGlobals, esgcFree, FlatProps.unionGlobalBag,
      FlatProps.emptyGlobalBag, valApproxSgcFree] using result

/-- Conditional induction case for optimizer global safety, with the original
result-dependent hypotheses for each successive branch. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyIf (c : Config) (trace : BackendCommon.Tra)
    (x y z : ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (thirdIH : ∀ (ea1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox)
      (ea2 : List (ClosLang.Exp × ValApprox)) (g2 : Spt ValApprox),
      (ea1, g1) = knownListTotal c [x] aenv g0 ∧
      (ea2, g2) = knownListTotal c [y] aenv g1 → KnownSafetyInvariant c [z] aenv g2)
    (secondIH : ∀ (ea1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea1, g1) = knownListTotal c [x] aenv g0 → KnownSafetyInvariant c [y] aenv g1)
    (firstIH : KnownSafetyInvariant c [x] aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [.ifThenElse trace x y z] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.ifThenElse trace x y z], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.ifThenElse trace x y z] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have allSafe := safe (.ifThenElse trace x y z) (by simp)
  simp only [esgcFree] at allSafe
  cases h1 : knownListTotal c [x] aenv g0 with
  | mk ea1 g1 =>
    obtain ⟨x', a1, eq1⟩ := knownListTotal_single_result c x aenv g0 g1 ea1 h1
    subst ea1
    have r1 := firstIH [(x', a1)] g1 ⟨h1, by simpa using allSafe.1, envSafe, globalSafe⟩
    cases h2 : knownListTotal c [y] aenv g1 with
    | mk ea2 g2 =>
      obtain ⟨y', a2, eq2⟩ := knownListTotal_single_result c y aenv g1 g2 ea2 h2
      subst ea2
      have r2 := secondIH [(x', a1)] g1 h1.symm [(y', a2)] g2
        ⟨h2, by simpa using allSafe.2.1, envSafe, r1.2.2.2⟩
      cases h3 : knownListTotal c [z] aenv g2 with
      | mk ea3 g3 =>
        obtain ⟨z', a3, eq3⟩ := knownListTotal_single_result c z aenv g2 g3 ea3 h3
        subst ea3
        have r3 := thirdIH [(x', a1)] g1 [(y', a2)] g2 ⟨h1.symm, h2.symm⟩ [(z', a3)] g3
          ⟨h3, by simpa using allSafe.2.2, envSafe, r2.2.2.2⟩
        rw [knownListTotal_if, h1] at run
        dsimp only at run
        rw [h2] at run
        dsimp only at run
        rw [h3] at run
        simp [knownSourceHead] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨?_, ?_, ?_, r3.2.2.2⟩
        · intro i
          have b1 := r1.1 i
          have b2 := r2.1 i
          have b3 := r3.1 i
          simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] at b1 b2 b3 ⊢
          omega
        · have sx : esgcFree x' := by simpa using r1.2.1
          have sy : esgcFree y' := by simpa using r2.2.1
          have sz : esgcFree z' := by simpa using r3.2.1
          simpa [esgcFree] using ⟨sx, sy, sz⟩
        · have m := valApproxSgcFreeMerge a2 a3 ⟨by simpa using r2.2.2.1, by simpa using r3.2.2.1⟩
          simpa using m

/-- Let-binding induction case for optimizer global safety, using the source
body hypothesis under the approximations produced by the bindings. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyLet (c : Config) (trace : BackendCommon.Tra)
    (xs : List ClosLang.Exp) (body : ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (bodyIH : ∀ (ea1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea1, g1) = knownListTotal c xs aenv g0 → KnownSafetyInvariant c [body] (ea1.map Prod.snd ++ aenv) g1)
    (bindingsIH : KnownSafetyInvariant c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [.let trace xs body] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.let trace xs body], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.let trace xs body] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have letSafe := safe (.let trace xs body) (by simp)
  simp only [esgcFree, esgcFreeList_iff] at letSafe
  cases h1 : knownListTotal c xs aenv g0 with
  | mk ea1 g1 =>
    have r1 := bindingsIH ea1 g1 ⟨h1, letSafe.1, envSafe, globalSafe⟩
    have bodyEnvSafe : ∀ a ∈ ea1.map Prod.snd ++ aenv, valApproxSgcFree a := by
      intro a member
      rcases List.mem_append.mp member with a1 | a2
      · exact r1.2.2.1 a a1
      · exact envSafe a a2
    cases h2 : knownListTotal c [body] (ea1.map Prod.snd ++ aenv) g1 with
    | mk ea2 g2 =>
      obtain ⟨bodyExpr, bodyApprox, eq2⟩ :=
        knownListTotal_single_result c body (ea1.map Prod.snd ++ aenv) g1 g2 ea2 h2
      subst ea2
      have r2 := bodyIH ea1 g1 h1.symm [(bodyExpr, bodyApprox)] g2
        ⟨h2, by simpa using letSafe.2, bodyEnvSafe, r1.2.2.2⟩
      rw [knownListTotal_let, h1] at run
      dsimp only at run
      rw [h2] at run
      simp [knownSourceHead] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨?_, ?_, ?_, r2.2.2.2⟩
      · intro i
        have b1 := r1.1 i
        have b2 := r2.1 i
        simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] at b2 ⊢
        omega
      · have exprSafe : esgcFree bodyExpr := by simpa using r2.2.1
        simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq, esgcFree, esgcFreeList_iff]
        exact ⟨r1.2.1, exprSafe⟩
      · simpa using r2.2.2.1

/-- Handler induction case for optimizer global safety; the handler sees the
source's leading `Other` approximation. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyHandle (c : Config) (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (handlerIH : ∀ (ea1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea1, g1) = knownListTotal c [body] aenv g0 → KnownSafetyInvariant c [handler] (.other :: aenv) g1)
    (bodyIH : KnownSafetyInvariant c [body] aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [.handle trace body handler] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.handle trace body handler], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.handle trace body handler] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have bothSafe := safe (.handle trace body handler) (by simp)
  simp only [esgcFree] at bothSafe
  cases h1 : knownListTotal c [body] aenv g0 with
  | mk ea1 g1 =>
    obtain ⟨e1, a1, eq1⟩ := knownListTotal_single_result c body aenv g0 g1 ea1 h1
    subst ea1
    have r1 := bodyIH [(e1, a1)] g1 ⟨h1, by simpa using bothSafe.1, envSafe, globalSafe⟩
    have newEnvSafe : ∀ a ∈ ValApprox.other :: aenv, valApproxSgcFree a := by
      intro a member
      rcases List.mem_cons.mp member with same | old
      · subst a
        simp [valApproxSgcFree]
      · exact envSafe a old
    cases h2 : knownListTotal c [handler] (.other :: aenv) g1 with
    | mk ea2 g2 =>
      obtain ⟨e2, a2, eq2⟩ := knownListTotal_single_result c handler (.other :: aenv) g1 g2 ea2 h2
      subst ea2
      have r2 := handlerIH [(e1, a1)] g1 h1.symm [(e2, a2)] g2
        ⟨h2, by simpa using bothSafe.2, newEnvSafe, r1.2.2.2⟩
      rw [knownListTotal_handle, h1] at run
      dsimp only at run
      rw [h2] at run
      simp [knownSourceHead] at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨?_, ?_, ?_, r2.2.2.2⟩
      · intro i
        have b1 := r1.1 i
        have b2 := r2.1 i
        simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] at b1 b2 ⊢
        omega
      · have s1 : esgcFree e1 := by simpa using r1.2.1
        have s2 : esgcFree e2 := by simpa using r2.2.1
        simpa [esgcFree] using ⟨s1, s2⟩
      · have m := valApproxSgcFreeMerge a1 a2 ⟨by simpa using r1.2.2.1, by simpa using r2.2.2.1⟩
        simpa using m

/-- Direct-call induction case for optimizer global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyCall (c : Config) (trace : BackendCommon.Tra) (ticks dest : Nat)
    (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownSafetyInvariant c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [.call trace ticks dest xs] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.call trace ticks dest xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.call trace ticks dest xs] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have argSafe : ∀ e ∈ xs, esgcFree e := by
    have h := safe (.call trace ticks dest xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using h
  cases hk : knownListTotal c xs aenv g0 with
  | mk ea g1 =>
    have result := argsIH ea g1 ⟨hk, argSafe, envSafe, globalSafe⟩
    rw [knownListTotal_call, hk] at run
    simp at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, result.2.2.2⟩
    · simpa [elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] using result.1
    · simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq, esgcFree, esgcFreeList_iff]
      exact result.2.1
    · simp [valApproxSgcFree]

/-- The optimizer's primitive reconstruction preserves the source operation's
write bag and closure safety. This is Flapjack proof infrastructure. -/
private theorem knownOpResultSafety (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (a : ValApprox) (args : List ClosLang.Exp) :
    let out := match op, a with
      | .globOp (.global _), .int i => ClosLang.Exp.op trace (.intOp (.const i)) args
      | .globOp (.global _), .tuple tag [] => ClosLang.Exp.op trace (.blockOp (.cons tag)) args
      | _, _ => ClosOp.smartOp trace op args
    setGlobals out = setGlobals (.op trace op args) ∧
      (esgcFree out ↔ esgcFree (.op trace op args)) := by
  dsimp only
  split
  · simp [setGlobals, opGlobalBag, esgcFree]
  · simp [setGlobals, opGlobalBag, esgcFree]
  · exact ⟨(ClosOp.smartSimp trace op args).2.1, (ClosOp.smartSimp trace op args).2.2⟩

/-- Primitive-operation induction case for optimizer global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyOp (c : Config) (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (argsIH : KnownSafetyInvariant c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [.op trace op xs] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.op trace op xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.op trace op xs] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have argSafe : ∀ e ∈ xs, esgcFree e := by
    have h := safe (.op trace op xs) (by simp)
    simpa [esgcFree, esgcFreeList_iff] using h
  cases hk : knownListTotal c xs aenv g0 with
  | mk ea g1 =>
    have result := argsIH ea g1 ⟨hk, argSafe, envSafe, globalSafe⟩
    have reverseSafe : ∀ a ∈ (ea.map Prod.snd).reverse, valApproxSgcFree a := by
      intro a member
      exact result.2.2.1 a (List.mem_reverse.mp member)
    cases hop : knownOpHOL op (ea.map Prod.snd).reverse g1 with
    | mk a g2 =>
      have opSafe := knownOpPreservesEsgcFree op (ea.map Prod.snd).reverse g1 a g2
        hop reverseSafe result.2.2.2
      let out := match op, a with
        | .globOp (.global _), .int i => ClosLang.Exp.op trace (.intOp (.const i)) (ea.map Prod.fst)
        | .globOp (.global _), .tuple tag [] => ClosLang.Exp.op trace (.blockOp (.cons tag)) (ea.map Prod.fst)
        | _, _ => ClosOp.smartOp trace op (ea.map Prod.fst)
      have outSafe : setGlobals out = setGlobals (.op trace op (ea.map Prod.fst)) ∧
          (esgcFree out ↔ esgcFree (.op trace op (ea.map Prod.fst))) :=
        knownOpResultSafety trace op a (ea.map Prod.fst)
      rw [knownListTotal_op, hk] at run
      dsimp only at run
      rw [hop] at run
      change ([(out, a)], g2) = (eas, g) at run
      cases run
      refine ⟨?_, ?_, ?_, opSafe.2⟩
      · intro i
        have bound := result.1 i
        have outEq := congrFun outSafe.1 i
        simp only [List.map_cons, List.map_nil, elistGlobals,
          FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag, Nat.add_zero]
        rw [outEq]
        simp only [setGlobals, FlatProps.unionGlobalBag]
        omega
      · have argsSafe : esgcFree (.op trace op (ea.map Prod.fst)) := by
          simpa [esgcFree, esgcFreeList_iff] using result.2.1
        simpa using outSafe.2.mpr argsSafe
      · simpa using opSafe.1

/-- Closure induction case for optimizer global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyFn (c : Config) (name : Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vs : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (aenv : List ValApprox) (g0 : Spt ValApprox)
    (bodyIH : KnownSafetyInvariant c [body] (List.replicate arity .other ++ aenv) g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [.fn name loc vs arity body] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.fn name loc vs arity body], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.fn name loc vs arity body] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have emptyBody : setGlobals body = FlatProps.emptyGlobalBag := by
    have h := safe (.fn name loc vs arity body) (by simp)
    simpa [esgcFree] using h
  have bodySafe : ∀ e ∈ [body], esgcFree e := by
    simpa using setGlobalsEmptyEsgcFree body emptyBody
  have bodyEnvSafe : ∀ a ∈ List.replicate arity ValApprox.other ++ aenv, valApproxSgcFree a := by
    intro a member
    rcases List.mem_append.mp member with replicated | old
    · have equal : a = .other := (List.mem_replicate.mp replicated).2
      subst a
      simp [valApproxSgcFree]
    · exact envSafe a old
  cases hk : knownListTotal c [body] (List.replicate arity .other ++ aenv) g0 with
  | mk ea g1 =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ :=
      knownListTotal_single_result c body (List.replicate arity .other ++ aenv) g0 g1 ea hk
    subst ea
    have result := bodyIH [(bodyExpr, bodyApprox)] g1 ⟨hk, bodySafe, bodyEnvSafe, globalSafe⟩
    have transformedEmpty : setGlobals bodyExpr = FlatProps.emptyGlobalBag := by
      funext i
      have bound := result.1 i
      simp [elistGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] at bound
      have original := congrFun emptyBody i
      simp [FlatProps.emptyGlobalBag] at original
      simp only [FlatProps.emptyGlobalBag]
      omega
    rw [knownListTotal_fn, hk] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, result.2.2.2⟩
    · intro i
      have bound := result.1 i
      simpa [elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] using bound
    · simpa [esgcFree] using transformedEmpty
    · cases loc with
      | none => simp [valApproxSgcFree]
      | some loc =>
        simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq]
        unfold closApproxHOL
        split <;> simp [valApproxSgcFree, emptyBody]

/-- Recursive-closure induction case for optimizer global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyLetrec (c : Config) (names : List Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vs : Option (List Nat)) (fns : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (bodyIH : ∀ (clos : List ValApprox) (newFns : List (Nat × ClosLang.Exp)),
      clos = (match loc with | none => List.replicate fns.length .other | some n => closGenNoInline n 0 fns) ∧
      newFns = fns.map (fun (n, e) =>
        (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ aenv) g0).1).1)) →
      KnownSafetyInvariant c [body] (clos ++ aenv) g0)
    (funsIH : ∀ (clos : List ValApprox) (arity : Nat) (e : ClosLang.Exp) (newEnv : List ValApprox),
      clos = (match loc with | none => List.replicate fns.length .other | some n => closGenNoInline n 0 fns) ∧
      (arity, e) ∈ fns ∧ newEnv = List.replicate arity .other ++ clos ++ aenv →
      KnownSafetyInvariant c [e] newEnv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [.letrec names loc vs fns body] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.letrec names loc vs fns body], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.letrec names loc vs fns body] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have initialSafe := safe (.letrec names loc vs fns body) (by simp)
  simp only [esgcFree] at initialSafe
  let clos := match loc with
    | none => List.replicate fns.length ValApprox.other
    | some n => closGenNoInline n 0 fns
  let newFns := fns.map (fun (n, e) =>
    (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ aenv) g0).1).1))
  have closSafe : ∀ a ∈ clos, valApproxSgcFree a := by
    cases loc with
    | none => simp [clos, valApproxSgcFree]
    | some n => exact closGenNoInlineSafe n 0 fns
  have originalBodies : ∀ e ∈ fns.map Prod.snd, setGlobals e = FlatProps.emptyGlobalBag := by
    apply (elistGlobalsEmpty _).mp
    simpa [funGlobals_eq_elist] using initialSafe.1
  have closEnvSafe : ∀ a ∈ clos ++ aenv, valApproxSgcFree a := by
    intro a member
    rcases List.mem_append.mp member with mem | mem
    · exact closSafe a mem
    · exact envSafe a mem
  have newBodies : ∀ e ∈ newFns.map Prod.snd, setGlobals e = FlatProps.emptyGlobalBag := by
    intro transformed member
    obtain ⟨entry, inNew, valueEq⟩ := List.mem_map.mp member
    obtain ⟨⟨n, e⟩, inFns, entryEq⟩ := List.mem_map.mp inNew
    have originalEmpty : setGlobals e = FlatProps.emptyGlobalBag :=
      originalBodies e (List.mem_map.mpr ⟨(n, e), inFns, rfl⟩)
    have bodyEnvSafe : ∀ a ∈ List.replicate n ValApprox.other ++ clos ++ aenv, valApproxSgcFree a := by
      intro a mem
      rw [List.append_assoc] at mem
      rcases List.mem_append.mp mem with inRep | inRest
      · have eq : a = .other := (List.mem_replicate.mp inRep).2
        subst a
        simp [valApproxSgcFree]
      · exact closEnvSafe a inRest
    have ih := funsIH clos n e (List.replicate n ValApprox.other ++ clos ++ aenv) ⟨by cases loc <;> rfl, inFns, rfl⟩
    cases he : knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ aenv) g0 with
    | mk ea ge =>
      obtain ⟨e', a', eaEq⟩ := knownListTotal_single_result c e _ g0 ge ea he
      subst ea
      have result := ih [(e', a')] ge
        ⟨he, by simpa using setGlobalsEmptyEsgcFree e originalEmpty, bodyEnvSafe, globalSafe⟩
      have transformedEmpty : setGlobals e' = FlatProps.emptyGlobalBag := by
        funext i
        have bound := result.1 i
        simp [elistGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] at bound
        have zero := congrFun originalEmpty i
        simp [FlatProps.emptyGlobalBag] at zero
        simp only [FlatProps.emptyGlobalBag]
        omega
      change (n, (knownSourceHead (knownListTotal c [e] (List.replicate n ValApprox.other ++ clos ++ aenv) g0).1).1) = entry at entryEq
      simp [knownSourceHead] at entryEq
      subst entry
      subst transformed
      simpa [← List.append_assoc, he, knownSourceHead] using transformedEmpty
  have newFnsEmpty : funGlobals newFns = FlatProps.emptyGlobalBag := by
    rw [funGlobals_eq_elist, elistGlobalsEmpty]
    exact newBodies
  cases hb : knownListTotal c [body] (clos ++ aenv) g0 with
  | mk ea gb =>
    obtain ⟨bodyExpr, bodyApprox, bodyEq⟩ := knownListTotal_single_result c body (clos ++ aenv) g0 gb ea hb
    subst ea
    have result := bodyIH clos newFns ⟨by cases loc <;> rfl, rfl⟩ [(bodyExpr, bodyApprox)] gb
      ⟨hb, by simpa using initialSafe.2, closEnvSafe, globalSafe⟩
    rw [knownListTotal_letrec] at run
    change (let (ea, g) := knownListTotal c [body] (clos ++ aenv) g0
      let (e, a) := knownSourceHead ea
      ([(.letrec names loc none newFns e, a)], g)) = (eas, g) at run
    rw [hb] at run
    simp [knownSourceHead] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, result.2.2.2⟩
    · intro i
      have b := result.1 i
      simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag,
        newFnsEmpty, initialSafe.1] at b ⊢
      exact b
    · have bodyOutSafe : esgcFree bodyExpr := by simpa using result.2.1
      simpa [esgcFree, newFnsEmpty] using bodyOutSafe
    · simpa using result.2.2.1

/-- Application induction case for optimizer global safety. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_preserves_esgc_free_0"]
theorem knownPreservesSafetyApp (c : Config) (trace : BackendCommon.Tra) (loc : Option Nat)
    (x : ClosLang.Exp) (xs : List ClosLang.Exp) (aenv : List ValApprox) (g0 : Spt ValApprox)
    (inlineIH : ∀ (ea2 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox)
      (ea1 : List (ClosLang.Exp × ValApprox)) (g2 : Spt ValApprox)
      (e1 : ClosLang.Exp) (a1 : ValApprox) (body : ClosLang.Exp),
      (ea2, g1) = knownListTotal c xs aenv g0 ∧
      (ea1, g2) = knownListTotal c [x] aenv g1 ∧
      (e1, a1) = knownSourceHead ea1 ∧ decideInlineHOL c a1 loc xs.length = .letInline body →
      KnownSafetyInvariant (decInlineFactor c) [body] (ea2.map Prod.snd) g2)
    (functionIH : ∀ (ea2 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox),
      (ea2, g1) = knownListTotal c xs aenv g0 → KnownSafetyInvariant c [x] aenv g1)
    (argsIH : KnownSafetyInvariant c xs aenv g0)
    (eas : List (ClosLang.Exp × ValApprox)) (g : Spt ValApprox)
    (h : knownListTotal c [.app trace loc x xs] aenv g0 = (eas, g) ∧
      (∀ e ∈ [ClosLang.Exp.app trace loc x xs], esgcFree e) ∧
      (∀ a ∈ aenv, valApproxSgcFree a) ∧ globalsApproxSgcFree g0) :
    (∀ i, elistGlobals (eas.map Prod.fst) i ≤ elistGlobals [.app trace loc x xs] i) ∧
      (∀ e ∈ eas.map Prod.fst, esgcFree e) ∧
      (∀ a ∈ eas.map Prod.snd, valApproxSgcFree a) ∧ globalsApproxSgcFree g := by
  rcases h with ⟨run, safe, envSafe, globalSafe⟩
  have inputSafe := safe (.app trace loc x xs) (by simp)
  simp only [esgcFree, esgcFreeList_iff] at inputSafe
  cases ha : knownListTotal c xs aenv g0 with
  | mk ea2 g1 =>
    have rArgs := argsIH ea2 g1 ⟨ha, inputSafe.2, envSafe, globalSafe⟩
    cases hf : knownListTotal c [x] aenv g1 with
    | mk ea1 g2 =>
      obtain ⟨e1, a1, eq1⟩ := knownListTotal_single_result c x aenv g1 g2 ea1 hf
      subst ea1
      have rFun := functionIH ea2 g1 ha.symm [(e1, a1)] g2
        ⟨hf, by simpa using inputSafe.1, envSafe, rArgs.2.2.2⟩
      have e1Safe : esgcFree e1 := by simpa using rFun.2.1
      have a1Safe : valApproxSgcFree a1 := by simpa using rFun.2.2.1
      have argsSafe : ∀ e ∈ ea2.map Prod.fst, esgcFree e := rArgs.2.1
      rw [knownListTotal_app, ha] at run
      dsimp only at run
      rw [hf] at run
      simp only [knownSourceHead, List.headD_cons] at run
      cases decision : decideInlineHOL c a1 loc xs.length with
      | nothing =>
        simp only [decision, Prod.mk.injEq] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨?_, ?_, ?_, rFun.2.2.2⟩
        · intro i
          have b1 := rArgs.1 i
          have b2 := rFun.1 i
          simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] at b2 ⊢
          omega
        · simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq, esgcFree, esgcFreeList_iff]
          exact ⟨e1Safe, argsSafe⟩
        · simp [valApproxSgcFree]
      | annotate target =>
        simp only [decision, Prod.mk.injEq] at run
        rcases run with ⟨rfl, rfl⟩
        refine ⟨?_, ?_, ?_, rFun.2.2.2⟩
        · intro i
          have b1 := rArgs.1 i
          have b2 := rFun.1 i
          simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] at b2 ⊢
          omega
        · simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq, esgcFree, esgcFreeList_iff]
          exact ⟨e1Safe, argsSafe⟩
        · simp [valApproxSgcFree]
      | letInline body =>
        obtain ⟨target, size, eq⟩ := decideInlineLetInlineImpClos c a1 loc xs.length body decision
        have bodyEmpty : setGlobals body = FlatProps.emptyGlobalBag := by
          simpa [eq, valApproxSgcFree] using a1Safe
        have inlineSafe : ∀ e ∈ [body], esgcFree e := by
          simpa using setGlobalsEmptyEsgcFree body bodyEmpty
        have bodyInvariant := inlineIH ea2 g1 [(e1, a1)] g2 e1 a1 body
          ⟨ha.symm, hf.symm, by simp [knownSourceHead], decision⟩
        cases hb : knownListTotal (decInlineFactor c) [body] (ea2.map Prod.snd) g2 with
        | mk inlineEa inlineG =>
          obtain ⟨inlineExpr, inlineApprox, eqBody⟩ :=
            knownListTotal_single_result (decInlineFactor c) body (ea2.map Prod.snd) g2 inlineG inlineEa hb
          subst inlineEa
          have rBody := bodyInvariant [(inlineExpr, inlineApprox)] inlineG
            ⟨hb, inlineSafe, rArgs.2.2.1, rFun.2.2.2⟩
          have outEmpty : setGlobals inlineExpr = FlatProps.emptyGlobalBag := by
            funext i
            have bound := rBody.1 i
            simp [elistGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag] at bound
            have original := congrFun bodyEmpty i
            simp [FlatProps.emptyGlobalBag] at original
            simp only [FlatProps.emptyGlobalBag]
            omega
          have inlineExprSafe : esgcFree inlineExpr := by simpa using rBody.2.1
          simp only [decision] at run
          rw [hb] at run
          simp at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨?_, ?_, ?_, rFun.2.2.2⟩
          · intro i
            have b1 := rArgs.1 i
            have b2 := rFun.1 i
            cases pureX : ClosLang.pure x <;>
              simp [elistGlobals, setGlobals, FlatProps.unionGlobalBag, FlatProps.emptyGlobalBag,
                elistGlobals_append, ticksSetGlobals, outEmpty] at b2 ⊢ <;> omega
          · have tickSafe := (ticksEsgcFree trace 1 xs.length inlineExpr).mpr inlineExprSafe
            simp only [List.map_cons, List.map_nil, List.mem_singleton, forall_eq, esgcFree, esgcFreeList_iff]
            constructor
            · cases pureX : ClosLang.pure x with
              | false =>
                simp only [Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton,
                  or_imp, forall_and, forall_eq]
                exact ⟨argsSafe, e1Safe⟩
              | true => exact argsSafe
            · exact tickSafe
          · simpa using rBody.2.2.1

end Flapjack.Compiler.Backend.ClosKnown.PreserveSafety
