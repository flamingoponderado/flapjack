module

public import Flapjack.HolRef
public import Flapjack.Compiler.Backend.ClosCall.Proofs.DoApp
public import Flapjack.Compiler.Backend.ClosCall.Proofs.PureCorrect
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Purity
public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueExistence
public import Flapjack.Compiler.Backend.ClosInterp.Proofs.PrimitiveRelation
public import Flapjack.Compiler.Backend.Semantics.ClosProps.PrimitiveBoolean
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CallsWellformed
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CallsExtension
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelOrigins
public import Flapjack.Compiler.Backend.ClosCall.Proofs.DomainLocations
public import Flapjack.Misc.Sptree.Subspt.DomainSubset
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Environment
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeIncludes
public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueRelation
public import Flapjack.Compiler.Backend.ClosCall.Proofs.InstallSimulation
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateRelation
public import Flapjack.SemanticPrimitivesProps.ResultRelation
public import Flapjack.Compiler.Backend.ClosCall.Proofs.ValueWellFormed
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockSource
public import Flapjack.Compiler.Backend.Semantics.ClosProps.ClockShift
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeGrowth
public import Flapjack.Compiler.Backend.Semantics.ClosProps.EvaluateAppend
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
public import Flapjack.Compiler.Backend.ClosCall.Proofs.ClosureLookup
public import Flapjack.Compiler.Backend.ClosCall.Proofs.ClosureWellFormed
public import Flapjack.Compiler.Backend.ClosCall.Proofs.IndexedCalls
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeLookup
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StubInvariants
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StubEvaluation
public import Flapjack.Compiler.Backend.ClosCall.Proofs.FreeCorrect
public import Flapjack.Compiler.Backend.ClosCall.Proofs.InsertWithCode
public import Flapjack.Compiler.Backend.ClosCall.Proofs.SuffixReplacement
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Direct-call compiler correctness for closure expressions and application. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps ClosSem SemanticPrimitivesHOL SemanticPrimitivesProps

namespace CallsCorrectPort
/-- The closure-state finite maps use the canonical lookup/support codec. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end CallsCorrectPort

private theorem listSplitInvariants (x y : ClosLang.Exp) (xs : List ClosLang.Exp) (g0 gm g : State)
    (out : ClosLang.Exp) (tail : List ClosLang.Exp)
    (headRun : calls [x] g0 = ([out], gm))
    (tailRun : calls (y :: xs) gm = (tail, g))
    (distinct : (codeLocations (x :: y :: xs)).Nodup)
    (fresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (x :: y :: xs)} ∧
      label ∈ g0.2.map Prod.fst))
    (annotations : everyFnLocationSome (x :: y :: xs)) (well : wellFormed g0) :
    wellFormed gm ∧ stateExtends gm g ∧ (codeLocations (y :: xs)).Nodup ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (y :: xs)} ∧
        label ∈ gm.2.map Prod.fst)) ∧ everyFnLocationSome (y :: xs) := by
  have locations : codeLocations (x :: y :: xs) = codeLocations [x] ++ codeLocations (y :: xs) := by
    simp [codeLocations]
  rw [locations, List.nodup_append] at distinct
  obtain ⟨headDistinct, tailDistinct, apart⟩ := distinct
  have headFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations [x]} ∧
      label ∈ g0.2.map Prod.fst) := by
    intro label ⟨⟨n, hn, eq⟩, old⟩
    apply fresh label
    exact ⟨⟨n, by rw [locations]; exact List.mem_append_left _ hn, eq⟩, old⟩
  have headAnnotations : everyFnLocationSome [x] := by
    simp only [everyFnLocationSome] at annotations ⊢
    exact ⟨annotations.1, trivial⟩
  have middleWell := calls_wellFormed [x] g0 [out] gm
    ⟨headRun, headDistinct, headFresh, headAnnotations, well⟩
  have origin := calls_addSucc_codeLocations [x] g0 [out] gm headRun
  have tailFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (y :: xs)} ∧
      label ∈ gm.2.map Prod.fst) := by
    intro label ⟨⟨n, hn, eq⟩, member⟩
    rcases origin member with old | ⟨m, hm, equal⟩
    · apply fresh label
      exact ⟨⟨n, by rw [locations]; exact List.mem_append_right _ hn, eq⟩, old⟩
    · have same : m = n := Nat.succ.inj (equal.trans eq.symm)
      exact apart m hm n hn same
  refine ⟨middleWell, calls_subg (y :: xs) gm tail g
    ⟨tailRun, middleWell.2, tailDistinct, tailFresh⟩, tailDistinct, tailFresh, ?_⟩
  simp only [everyFnLocationSome] at annotations ⊢
  exact annotations.2
private theorem listHeadLocationBound (x y : ClosLang.Exp) (xs : List ClosLang.Exp) (gm g : State) (tail : List ClosLang.Exp)
    (tailRun : calls (y :: xs) gm = (tail, g))
    (distinct : (codeLocations (x :: y :: xs)).Nodup) (well : wellFormed gm) :
    Set.Subset (Set.diff {n | n ∈ codeLocations [x]} (sptDomain gm.1))
      (Set.diff {n | n ∈ codeLocations (x :: y :: xs)} (sptDomain g.1)) := by
  have locations : codeLocations (x :: y :: xs) = codeLocations [x] ++ codeLocations (y :: xs) := by
    simp [codeLocations]
  intro key ⟨inHead, fresh⟩
  have unique : (codeLocations [x] ++ codeLocations (y :: xs)).Nodup := by
    simpa only [← locations] using distinct
  have finalFresh := calls_preservesFreshLocation [x] (y :: xs) gm tail g key unique tailRun well inHead fresh
  exact ⟨by rw [locations]; exact List.mem_append_left _ inHead, finalFresh⟩
private theorem listTailLocationBound (x y : ClosLang.Exp) (xs : List ClosLang.Exp) (g g2 : State)
    (allowed allowed2 : Set Nat)
    (whole : Set.Subset (Set.diff {n | n ∈ codeLocations (x :: y :: xs)} (sptDomain g.1)) allowed)
    (growth : stateExtends g g2) (allowedGrowth : Set.Subset allowed allowed2) :
    Set.Subset (Set.diff {n | n ∈ codeLocations (y :: xs)} (sptDomain g2.1)) allowed2 := by
  intro key ⟨inTail, fresh⟩
  apply allowedGrowth
  apply whole
  refine ⟨?_, ?_⟩
  · simp only [codeLocations, List.mem_append]
    exact Or.inr (by simpa [codeLocations] using inTail)
  · intro old
    exact fresh (sptSubspt_domainSubset g.1 g2.1 growth.1 old)
private theorem envRel_of_subset {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (offset : Nat) (small large : List (Nat × ClosLang.Exp))
    (subset : ∀ fn, fn ∈ small → fn ∈ large) (related : envRel R env1 env2 offset large) :
    envRel R env1 env2 offset small := by
  unfold envRel at related ⊢
  by_cases same : env1.length = env2.length
  · simpa only [same, ↓reduceIte] using related
  · simp only [same, ↓reduceIte] at related ⊢
    intro x ⟨fn, member, used⟩
    exact related x ⟨fn, subset fn member, used⟩
private theorem envRel_split {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (head : ClosLang.Exp) (tail : List ClosLang.Exp)
    (related : envRel R env1 env2 0 ((head :: tail).map (fun e => (0, e)))) :
    envRel R env1 env2 0 ([(0, head)]) ∧
      envRel R env1 env2 0 (tail.map (fun e => (0, e))) := by
  constructor
  · apply envRel_of_subset R env1 env2 0 _ _ ?_ related
    intro fn member
    simp only [List.mem_singleton] at member
    subst fn
    simp
  · apply envRel_of_subset R env1 env2 0 _ _ ?_ related
    intro fn member
    simp only [List.map_cons, List.mem_cons]
    exact Or.inr member
private theorem listHeadSafe {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List ClosSem.Value) (s0 middle last : ClosSem.State C F)
    (headResult result : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (headRun : ClosSem.evaluate [x] env s0 = (headResult, middle))
    (wholeRun : ClosSem.evaluate (x :: y :: xs) env s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError)) :
    headResult ≠ .err (.abort .typeError) := by
  intro bad
  subst headResult
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate_source, headRun] at wholeRun
  exact safe (congrArg Prod.fst wholeRun).symm

private theorem listTailSafe {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List ClosSem.Value) (s0 middle last tailLast : ClosSem.State C F)
    (values : List ClosSem.Value)
    (tailResult result : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (headRun : ClosSem.evaluate [x] env s0 = (.val values, middle))
    (tailRun : ClosSem.evaluate (y :: xs) env middle = (tailResult, tailLast))
    (wholeRun : ClosSem.evaluate (x :: y :: xs) env s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError)) :
    tailResult ≠ .err (.abort .typeError) := by
  intro bad
  subst tailResult
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate_source, headRun, tailRun] at wholeRun
  exact safe (congrArg Prod.fst wholeRun).symm
private theorem composeListRuns {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List ClosSem.Value) (s0 middle last : ClosSem.State C F)
    (ck ck2 : Nat) (value : ClosSem.Value)
    (result : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (headRun : ClosSem.evaluate [x] env {s0 with clock := s0.clock + ck} = (.val [value], middle))
    (tailRun : ClosSem.evaluate (y :: xs) env {middle with clock := middle.clock + ck2} = (result, last)) :
    ClosSem.evaluate (x :: y :: xs) env {s0 with clock := s0.clock + (ck + ck2)} =
      (match result with | .val values => (.val (value :: values), last) | .err err => (.err err, last)) := by
  have shifted := ClosProps.ClockShiftPort.evaluate_addClock middle
    {s0 with clock := s0.clock + ck} (.val [value]) [x] env ⟨headRun, by simp⟩ ck2
  have headShift : ClosSem.evaluate [x] env {s0 with clock := s0.clock + (ck + ck2)} =
      (.val [value], {middle with clock := middle.clock + ck2}) := by
    simpa only [Nat.add_assoc] using shifted
  cases result <;> simp [ClosProps.evaluateCons, headShift, tailRun, Flapjack.holHd]
private theorem composeListError {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env : List ClosSem.Value) (s0 last : ClosSem.State C F)
    (err : Flapjack.SemanticPrimitivesHOL.ErrorResult ClosSem.Value)
    (headRun : ClosSem.evaluate [x] env s0 = (.err err, last)) :
    ClosSem.evaluate (x :: y :: xs) env s0 = (.err err, last) := by
  rw [ClosProps.evaluateCons, headRun]
private theorem splitCompiledList (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (g0 g : State) (out : List ClosLang.Exp)
    (run : calls (x :: y :: xs) g0 = (out, g)) :
    ∃ head tailHead tailRest middle,
      calls [x] g0 = ([head], middle) ∧
      calls (y :: xs) middle = (tailHead :: tailRest, g) ∧
      out = head :: tailHead :: tailRest := by
  cases hHead : calls [x] g0 with
  | mk heads middle =>
    obtain ⟨head, rfl⟩ := calls_sing x g0 heads middle hHead
    cases hTail : calls (y :: xs) middle with
    | mk tail final =>
      have combined := (calls_list_equations x y xs g0).2
      simp only [hHead, hTail] at combined
      have outputs := run.symm.trans combined
      cases tail with
      | nil =>
        have len := calls_length (y :: xs) middle [] final hTail
        simp at len
      | cons tailHead tailRest =>
        simp only [List.singleton_append, Prod.mk.injEq] at outputs
        obtain ⟨outEq, finalEq⟩ := outputs
        subst final
        exact ⟨head, tailHead, tailRest, middle, rfl, hTail, outEq⟩
private theorem listHeadStructural {A B : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (g0 gm g g1 : State) (out tailHead : ClosLang.Exp) (tailRest : List ClosLang.Exp)
    (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (headRun : calls [x] g0 = ([out], gm))
    (tailRun : calls (y :: xs) gm = (tailHead :: tailRest, g))
    (distinct : (codeLocations (x :: y :: xs)).Nodup)
    (fresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (x :: y :: xs)} ∧
      label ∈ g0.2.map Prod.fst))
    (annotations : everyFnLocationSome (x :: y :: xs)) (well : wellFormed g0)
    (wholeBound : Set.Subset (Set.diff {n | n ∈ codeLocations (x :: y :: xs)} (sptDomain g.1)) allowed)
    (growth : stateExtends g g1) (included : codeIncludes g.2 code)
    (related : envRel R env1 env2 0 ((out :: tailHead :: tailRest).map (fun e => (0, e)))) :
    stateExtends gm g1 ∧
      Set.Subset (Set.diff {n | n ∈ codeLocations [x]} (sptDomain gm.1)) allowed ∧
      codeIncludes gm.2 code ∧ envRel R env1 env2 0 [(0, out)] := by
  obtain ⟨middleWell, middleGrowth, _, _, _⟩ :=
    listSplitInvariants x y xs g0 gm g out (tailHead :: tailRest) headRun tailRun distinct fresh annotations well
  refine ⟨stateExtends_trans gm g g1 middleGrowth growth, ?_, codeIncludes_subg gm g code middleGrowth included, ?_⟩
  · exact Set.Subset.trans (listHeadLocationBound x y xs gm g (tailHead :: tailRest) tailRun distinct middleWell) wholeBound
  · exact (envRel_split R env1 env2 out (tailHead :: tailRest) related).1
private theorem listTailStructural (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (g g1 g2 : State) (out tailHead : ClosLang.Exp) (tailRest : List ClosLang.Exp)
    (allowed allowed2 : Set Nat) (code code2 : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (env1 env2 : List ClosSem.Value)
    (wholeBound : Set.Subset (Set.diff {n | n ∈ codeLocations (x :: y :: xs)} (sptDomain g.1)) allowed)
    (growth : stateExtends g g1) (growth2 : stateExtends g1 g2)
    (allowedGrowth : Set.Subset allowed allowed2) (codeGrowth : code.submap code2)
    (included : codeIncludes g.2 code)
    (envWell : ∀ value ∈ env1, valueWellFormed g1 allowed code value)
    (related : envRel (valueRel g1 allowed code) env1 env2 0
      ((out :: tailHead :: tailRest).map (fun e => (0, e)))) :
    stateExtends g g2 ∧
      Set.Subset (Set.diff {n | n ∈ codeLocations (y :: xs)} (sptDomain g2.1)) allowed2 ∧
      codeIncludes g.2 code2 ∧
      (∀ value ∈ env1, valueWellFormed g2 allowed2 code2 value) ∧
      envRel (valueRel g2 allowed2 code2) env1 env2 0
        ((tailHead :: tailRest).map (fun e => (0, e))) := by
  have growthAll := stateExtends_trans g g1 g2 growth growth2
  refine ⟨growthAll, listTailLocationBound x y xs g g2 allowed allowed2 wholeBound growthAll allowedGrowth,
    codeIncludes_submap g.2 code code2 ⟨included, codeGrowth⟩,
    everyValueWellFormed_subg g1 allowed code env1 code2 g2 allowed2
      ⟨envWell, codeGrowth, growth2, allowedGrowth⟩, ?_⟩
  exact envValueRel_subg g1 allowed code env1 env2 0 _ g2 allowed2 code2
    ⟨(envRel_split _ env1 env2 out (tailHead :: tailRest) related).2, growth2, allowedGrowth, codeGrowth⟩
private theorem listHeadSyntax (x y : ClosLang.Exp) (xs : List ClosLang.Exp) (g0 : State)
    (distinct : (codeLocations (x :: y :: xs)).Nodup)
    (fresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (x :: y :: xs)} ∧
      label ∈ g0.2.map Prod.fst))
    (annotations : everyFnLocationSome (x :: y :: xs))
    (noVars : everyFnVarsNone (x :: y :: xs)) :
    (codeLocations [x]).Nodup ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations [x]} ∧
        label ∈ g0.2.map Prod.fst)) ∧ everyFnLocationSome [x] ∧ everyFnVarsNone [x] ∧
      everyFnVarsNone (y :: xs) := by
  have locations : codeLocations (x :: y :: xs) = codeLocations [x] ++ codeLocations (y :: xs) := by
    simp [codeLocations]
  have headDistinct : (codeLocations [x]).Nodup := by
    rw [locations, List.nodup_append] at distinct
    exact distinct.1
  have headFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations [x]} ∧
      label ∈ g0.2.map Prod.fst) := by
    intro label ⟨⟨n, hn, eq⟩, old⟩
    apply fresh label
    exact ⟨⟨n, by rw [locations]; exact List.mem_append_left _ hn, eq⟩, old⟩
  refine ⟨headDistinct, headFresh, ?_, ?_, ?_⟩
  · simp only [everyFnLocationSome] at annotations ⊢
    exact ⟨annotations.1, trivial⟩
  · simp only [everyFnVarsNone] at noVars ⊢
    exact ⟨noVars.1, trivial⟩
  · simp only [everyFnVarsNone] at noVars ⊢
    exact noVars.2
private theorem listTailFromHeadRun {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (g g1 g2 : State) (out tailHead : ClosLang.Exp) (tailRest : List ClosLang.Exp)
    (allowed allowed2 : Set Nat) (env1 env2 : List ClosSem.Value)
    (t0 t : ClosSem.State C F) (ck : Nat)
    (headResult : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (headRun : ClosSem.evaluate [out] env2 {t0 with clock := t0.clock + ck} = (headResult, t))
    (wholeBound : Set.Subset (Set.diff {n | n ∈ codeLocations (x :: y :: xs)} (sptDomain g.1)) allowed)
    (growth : stateExtends g g1) (growth2 : stateExtends g1 g2)
    (allowedGrowth : Set.Subset allowed allowed2) (included : codeIncludes g.2 t0.code)
    (envWell : ∀ value ∈ env1, valueWellFormed g1 allowed t0.code value)
    (related : envRel (valueRel g1 allowed t0.code) env1 env2 0
      ((out :: tailHead :: tailRest).map (fun e => (0, e)))) :
    stateExtends g g2 ∧
      Set.Subset (Set.diff {n | n ∈ codeLocations (y :: xs)} (sptDomain g2.1)) allowed2 ∧
      codeIncludes g.2 t.code ∧
      (∀ value ∈ env1, valueWellFormed g2 allowed2 t.code value) ∧
      envRel (valueRel g2 allowed2 t.code) env1 env2 0
        ((tailHead :: tailRest).map (fun e => (0, e))) := by
  have codeGrowth : t0.code.submap t.code := by
    simpa using ClosProps.CodeGrowthPort.evaluate_mono [out] env2
      {t0 with clock := t0.clock + ck} headResult t headRun
  exact listTailStructural x y xs g g1 g2 out tailHead tailRest allowed allowed2 t0.code t.code
    env1 env2 wholeBound growth growth2 allowedGrowth codeGrowth included envWell related
private def ExprMotive {C F : Type} (xs : List ClosLang.Exp) (env1 : List ClosSem.Value)
    (s0 : ClosSem.State (NumSet × C) F) : Prop :=
  ∀ (tmp : List ClosLang.Exp × List ClosSem.Value × ClosSem.State (NumSet × C) F)
    (g0 g : State) (env2 : List ClosSem.Value) (t0 : ClosSem.State C F) (ys : List ClosLang.Exp)
    (res : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (s : ClosSem.State (NumSet × C) F) (l l1 : Set Nat) (g1 : State),
    tmp = (xs, env1, s0) ∧ ClosSem.evaluate xs env1 s0 = (res, s) ∧
      res ≠ .err (.abort .typeError) ∧ calls xs g0 = (ys, g) ∧
      codeInv (some g1) l1 s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle ∧
      everyFnLocationSome xs ∧ everyFnVarsNone xs ∧
      (∀ v ∈ env1, valueWellFormed g1 l1 t0.code v) ∧ stateValuesWellFormed g1 l1 t0.code s0 ∧
      wellFormed g0 ∧ (codeLocations xs).Nodup ∧
      Disjoint (Set.image Nat.succ {x | x ∈ codeLocations xs}) {x | x ∈ g0.2.map Prod.fst} ∧
      l = {x | x ∈ codeLocations xs} \ sptDomain g.1 ∧
      stateExtends g g1 ∧ l ⊆ l1 ∧ Disjoint l1 (sptDomain g1.1) ∧ wellFormed g1 ∧
      envRel (valueRel g1 l1 t0.code) env1 env2 0 (ys.map (fun x => (0, x))) ∧
      stateRel g1 l1 s0 t0 ∧ codeIncludes g.2 t0.code →
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 s.code s.compile s.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code s ∧
      stateExtends g1 g2 ∧ wellFormed g2 ∧ l1 ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      Flapjack.SemanticPrimitivesProps.everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) res ∧
      ClosSem.evaluate ys env2 {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 s t ∧
      Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (valueRel g2 l2 t.code))
        (valueRel g2 l2 t.code) res res'
private theorem applyListHeadIH {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (s0 middle last : ClosSem.State (NumSet × C) F)
    (g0 gm g g1 : State) (out tailHead : ClosLang.Exp) (tailRest : List ClosLang.Exp)
    (t0 : ClosSem.State C F) (l1 : Set Nat)
    (headResult result : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (ih : ExprMotive [x] env1 s0)
    (headRun : ClosSem.evaluate [x] env1 s0 = (headResult, middle))
    (wholeRun : ClosSem.evaluate (x :: y :: xs) env1 s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (headCompile : calls [x] g0 = ([out], gm))
    (tailCompile : calls (y :: xs) gm = (tailHead :: tailRest, g))
    (invariant : codeInv (some g1) l1 s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle)
    (annotations : everyFnLocationSome (x :: y :: xs)) (noVars : everyFnVarsNone (x :: y :: xs))
    (envWell : ∀ v ∈ env1, valueWellFormed g1 l1 t0.code v)
    (stateWell : stateValuesWellFormed g1 l1 t0.code s0)
    (well0 : wellFormed g0) (distinct : (codeLocations (x :: y :: xs)).Nodup)
    (fresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (x :: y :: xs)} ∧
      label ∈ g0.2.map Prod.fst))
    (wholeBound : Set.Subset (Set.diff {n | n ∈ codeLocations (x :: y :: xs)} (sptDomain g.1)) l1)
    (growth : stateExtends g g1) (disjoint : Disjoint l1 (sptDomain g1.1)) (well1 : wellFormed g1)
    (related : envRel (valueRel g1 l1 t0.code) env1 env2 0
      ((out :: tailHead :: tailRest).map (fun e => (0, e))))
    (stateRelated : stateRel g1 l1 s0 t0) (included : codeIncludes g.2 t0.code) :
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 middle.code middle.compile middle.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code middle ∧
      stateExtends g1 g2 ∧ wellFormed g2 ∧ l1 ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      Flapjack.SemanticPrimitivesProps.everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) headResult ∧
      ClosSem.evaluate [out] env2 {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 middle t ∧
      Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (valueRel g2 l2 t.code))
        (valueRel g2 l2 t.code) headResult res' := by
  have headSafe := listHeadSafe x y xs env1 s0 middle last headResult result headRun wholeRun safe
  obtain ⟨headDistinct, headFresh, headAnnotations, headVars, _⟩ :=
    listHeadSyntax x y xs g0 distinct fresh annotations noVars
  obtain ⟨headGrowth, headBound, headIncluded, headRelated⟩ :=
    listHeadStructural x y xs g0 gm g g1 out tailHead tailRest l1 t0.code
      (valueRel g1 l1 t0.code) env1 env2 headCompile tailCompile distinct fresh annotations well0
      wholeBound growth included related
  have headDisjoint : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [x]})
      {n | n ∈ g0.2.map Prod.fst} := by
    apply Set.disjoint_left.mpr
    intro key a b
    exact headFresh key ⟨a, b⟩
  exact ih ([x], env1, s0) g0 gm env2 t0 [out] headResult middle
    ({n | n ∈ codeLocations [x]} \ sptDomain gm.1) l1 g1
    ⟨rfl, headRun, headSafe, headCompile, invariant, headAnnotations, headVars,
      envWell, stateWell, well0, headDistinct, headDisjoint, rfl, headGrowth, headBound,
      disjoint, well1, by simpa using headRelated, stateRelated, headIncluded⟩
private theorem applyListTailIH {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (s0 middle last tailLast : ClosSem.State (NumSet × C) F)
    (g0 gm g g1 g2 : State) (out tailHead : ClosLang.Exp) (tailRest : List ClosLang.Exp)
    (t0 t : ClosSem.State C F) (l1 l2 : Set Nat) (ck : Nat) (headValues : List ClosSem.Value)
    (headTarget tailResult result : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (ih : ExprMotive (y :: xs) env1 middle)
    (headRun : ClosSem.evaluate [x] env1 s0 = (.val headValues, middle))
    (tailRun : ClosSem.evaluate (y :: xs) env1 middle = (tailResult, tailLast))
    (wholeRun : ClosSem.evaluate (x :: y :: xs) env1 s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (headCompile : calls [x] g0 = ([out], gm))
    (tailCompile : calls (y :: xs) gm = (tailHead :: tailRest, g))
    (headTargetRun : ClosSem.evaluate [out] env2 {t0 with clock := t0.clock + ck} = (headTarget, t))
    (invariant : codeInv (some g2) l2 middle.code middle.compile middle.compileOracle t.code t.compile t.compileOracle)
    (annotations : everyFnLocationSome (x :: y :: xs)) (noVars : everyFnVarsNone (x :: y :: xs))
    (envWell : ∀ v ∈ env1, valueWellFormed g1 l1 t0.code v)
    (stateWell : stateValuesWellFormed g2 l2 t.code middle)
    (well0 : wellFormed g0) (distinct : (codeLocations (x :: y :: xs)).Nodup)
    (fresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (x :: y :: xs)} ∧
      label ∈ g0.2.map Prod.fst))
    (wholeBound : Set.Subset (Set.diff {n | n ∈ codeLocations (x :: y :: xs)} (sptDomain g.1)) l1)
    (growth : stateExtends g g1) (growth2 : stateExtends g1 g2) (allowedGrowth : l1 ⊆ l2)
    (disjoint : Disjoint l2 (sptDomain g2.1)) (well2 : wellFormed g2)
    (related : envRel (valueRel g1 l1 t0.code) env1 env2 0
      ((out :: tailHead :: tailRest).map (fun e => (0, e))))
    (stateRelated : stateRel g2 l2 middle t) (included : codeIncludes g.2 t0.code) :
    ∃ ck2 res' t2 g3 l3,
      codeInv (some g3) l3 tailLast.code tailLast.compile tailLast.compileOracle t2.code t2.compile t2.compileOracle ∧
      stateValuesWellFormed g3 l3 t2.code tailLast ∧
      stateExtends g2 g3 ∧ wellFormed g3 ∧ l2 ⊆ l3 ∧ Disjoint l3 (sptDomain g3.1) ∧
      Flapjack.SemanticPrimitivesProps.everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g3 l3 t2.code v)
        (valueWellFormed g3 l3 t2.code) tailResult ∧
      ClosSem.evaluate (tailHead :: tailRest) env2 {t with clock := t.clock + ck2} = (res', t2) ∧
      stateRel g3 l3 tailLast t2 ∧
      Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (valueRel g3 l3 t2.code))
        (valueRel g3 l3 t2.code) tailResult res' := by
  have tailSafe := listTailSafe x y xs env1 s0 middle last tailLast headValues tailResult result
    headRun tailRun wholeRun safe
  obtain ⟨middleWell, _, tailDistinct, tailFresh, tailAnnotations⟩ :=
    listSplitInvariants x y xs g0 gm g out (tailHead :: tailRest) headCompile tailCompile
      distinct fresh annotations well0
  obtain ⟨_, _, _, _, tailVars⟩ := listHeadSyntax x y xs g0 distinct fresh annotations noVars
  obtain ⟨tailGrowth, _, tailIncluded, tailEnvWell, tailRelated⟩ :=
    listTailFromHeadRun x y xs g g1 g2 out tailHead tailRest l1 l2 env1 env2 t0 t ck headTarget
      headTargetRun wholeBound growth growth2 allowedGrowth included envWell related
  have tailBound : Set.Subset (Set.diff {n | n ∈ codeLocations (y :: xs)} (sptDomain g.1)) l2 := by
    intro key ⟨member, notIn⟩
    apply allowedGrowth
    apply wholeBound
    refine ⟨?_, notIn⟩
    simp only [codeLocations, List.mem_append]
    exact Or.inr (by simpa [codeLocations] using member)
  have tailDisjoint : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations (y :: xs)})
      {n | n ∈ gm.2.map Prod.fst} := by
    apply Set.disjoint_left.mpr
    intro key a b
    exact tailFresh key ⟨a, b⟩
  exact ih (y :: xs, env1, middle) gm g env2 t (tailHead :: tailRest) tailResult tailLast
    ({n | n ∈ codeLocations (y :: xs)} \ sptDomain g.1) l2 g2
    ⟨rfl, tailRun, tailSafe, tailCompile, invariant, tailAnnotations, tailVars,
      tailEnvWell, stateWell, middleWell, tailDistinct, tailDisjoint, rfl, tailGrowth, tailBound,
      disjoint, well2, tailRelated, stateRelated, tailIncluded⟩
private theorem combineListResults {A B : Type} (P : A → Prop) (R : A → B → Prop)
    (head : A) (head' : B)
    (tail : Flapjack.SemanticPrimitivesHOL.Result (List A) A)
    (tail' : Flapjack.SemanticPrimitivesHOL.Result (List B) B)
    (headWell : P head) (headRelated : R head head')
    (tailWell : Flapjack.SemanticPrimitivesProps.everyResult (fun vs => ∀ v ∈ vs, P v) P tail)
    (tailRelated : Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ R) R tail tail') :
    Flapjack.SemanticPrimitivesProps.everyResult (fun vs => ∀ v ∈ vs, P v) P
      (match tail with | .val vs => .val (head :: vs) | .err error => .err error) ∧
    Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ R) R
      (match tail with | .val vs => .val (head :: vs) | .err error => .err error)
      (match tail' with | .val vs => .val (head' :: vs) | .err error => .err error) := by
  cases tail with
  | val values =>
    cases tail' with
    | val values' =>
      change (∀ v ∈ values, P v) at tailWell
      change List.Forall₂ R values values' at tailRelated
      constructor
      · change ∀ v ∈ head :: values, P v
        intro v member
        rcases List.mem_cons.mp member with rfl | member
        · exact headWell
        · exact tailWell v member
      · exact List.Forall₂.cons headRelated tailRelated
    | err error =>
      change False at tailRelated
      exact tailRelated.elim
  | err error =>
    cases tail' with
    | val values' =>
      change False at tailRelated
      exact tailRelated.elim
    | err error' => exact ⟨tailWell, tailRelated⟩
private theorem combineListResultsAfterTail {C F : Type} (g2 g3 : State) (l2 l3 : Set Nat)
    (t t2 : ClosSem.State C F) (env : List ClosSem.Value) (tailCode : List ClosLang.Exp) (ck : Nat)
    (v v' : ClosSem.Value)
    (tail tail' : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (tailRun : ClosSem.evaluate tailCode env {t with clock := t.clock + ck} = (tail', t2))
    (growth : stateExtends g2 g3) (allowedGrowth : l2 ⊆ l3)
    (headWell : valueWellFormed g2 l2 t.code v) (headRelated : valueRel g2 l2 t.code v v')
    (tailWell : Flapjack.SemanticPrimitivesProps.everyResult
      (fun vs => ∀ v ∈ vs, valueWellFormed g3 l3 t2.code v) (valueWellFormed g3 l3 t2.code) tail)
    (tailRelated : Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (valueRel g3 l3 t2.code))
      (valueRel g3 l3 t2.code) tail tail') :
    Flapjack.SemanticPrimitivesProps.everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g3 l3 t2.code v)
      (valueWellFormed g3 l3 t2.code)
      (match tail with | .val vs => .val (v :: vs) | .err error => .err error) ∧
    Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (valueRel g3 l3 t2.code))
      (valueRel g3 l3 t2.code)
      (match tail with | .val vs => .val (v :: vs) | .err error => .err error)
      (match tail' with | .val vs => .val (v' :: vs) | .err error => .err error) := by
  have codeGrowth : t.code.submap t2.code := by
    simpa using ClosProps.CodeGrowthPort.evaluate_mono tailCode env
      {t with clock := t.clock + ck} tail' t2 tailRun
  have finalWell := valueWellFormed_subg g2 l2 t.code v g3 l3 t2.code
    ⟨headWell, codeGrowth, growth, allowedGrowth⟩
  have finalRelated := valueRel_submapSubg g2 l2 t.code v v' t2.code l3 g3
    ⟨headRelated, codeGrowth, allowedGrowth, growth⟩
  cases tail <;> cases tail' <;>
    exact combineListResults (valueWellFormed g3 l3 t2.code) (valueRel g3 l3 t2.code)
      v v' _ _ finalWell finalRelated tailWell tailRelated
private theorem listCase {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (headIH : ExprMotive [x] env1 s0)
    (tailIH : ∀ (middle : ClosSem.State (NumSet × C) F),
      middle.clock ≤ s0.clock → ExprMotive (y :: xs) env1 middle) :
    ExprMotive (x :: y :: xs) env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, wholeRun, safe, compiled, invariant, annotations, noVars, envWell,
    stateWell, well0, distinct, fresh, lEq, growth, wholeBound, disjoint, well1,
    related, stateRelated, included⟩
  subst l
  have freshPointwise : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (x :: y :: xs)} ∧
      label ∈ g0.2.map Prod.fst) := by
    intro label ⟨a, b⟩
    exact Set.disjoint_left.mp fresh a b
  obtain ⟨out, tailHead, tailRest, gm, headCompile, tailCompile, rfl⟩ :=
    splitCompiledList x y xs g0 g ys compiled
  cases headRun : ClosSem.evaluate [x] env1 s0 with
  | mk headResult middle =>
    obtain ⟨ck, headTarget, t, g2, l2, headInvariant, headStateWell, headGrowth, well2,
      allowedGrowth, disjoint2, headWell, headTargetRun, headStateRelated, headRelated⟩ :=
      applyListHeadIH x y xs env1 env2 s0 middle s g0 gm g g1 out tailHead tailRest t0 l1
        headResult res headIH headRun wholeRun safe headCompile tailCompile invariant annotations noVars
        envWell stateWell well0 distinct freshPointwise wholeBound growth disjoint well1 related stateRelated included
    cases headResult with
    | err error =>
      cases headTarget with
      | val vs =>
        change False at headRelated
        exact headRelated.elim
      | err error' =>
        have sourceEq : (res, s) = (.err error, middle) := by
          rw [ClosProps.evaluateCons, headRun] at wholeRun
          exact wholeRun.symm
        cases sourceEq
        refine ⟨ck, .err error', t, g2, l2, headInvariant, headStateWell, headGrowth, well2,
          allowedGrowth, disjoint2, headWell, ?_, headStateRelated, headRelated⟩
        exact composeListError out tailHead tailRest env2 {t0 with clock := t0.clock + ck} t error' headTargetRun
    | val headValues =>
      cases headTarget with
      | err error' =>
        change False at headRelated
        exact headRelated.elim
      | val targetValues =>
        obtain ⟨value, rfl⟩ := ClosProps.evaluateSing x env1 s0 middle headValues headRun
        obtain ⟨targetValue, rfl⟩ := ClosProps.evaluateSing out env2
          {t0 with clock := t0.clock + ck} t targetValues headTargetRun
        change List.Forall₂ (valueRel g2 l2 t.code) [value] [targetValue] at headRelated
        cases headRelated with
        | cons valueRelated rest =>
          cases rest
          change ∀ v ∈ [value], valueWellFormed g2 l2 t.code v at headWell
          have valueWell := headWell value (by simp)
          cases tailRun : ClosSem.evaluate (y :: xs) env1 middle with
          | mk tailResult tailLast =>
            have middleClock : middle.clock ≤ s0.clock :=
              ClosSem.evaluate_clock_source.1 [x] env1 s0 (.val [value]) middle headRun
            obtain ⟨ck2, targetTail, t2, g3, l3, tailInvariant, tailStateWell, tailGrowth, well3,
              allowedGrowth2, disjoint3, tailWell, tailTargetRun, tailStateRelated, tailRelated⟩ :=
              applyListTailIH x y xs env1 env2 s0 middle s tailLast g0 gm g g1 g2 out tailHead tailRest
                t0 t l1 l2 ck [value] (.val [targetValue]) tailResult res (tailIH middle middleClock)
                headRun tailRun wholeRun safe headCompile tailCompile headTargetRun headInvariant annotations noVars
                envWell headStateWell well0 distinct freshPointwise wholeBound growth headGrowth allowedGrowth
                disjoint2 well2 related headStateRelated included
            have combined := combineListResultsAfterTail g2 g3 l2 l3 t t2 env2 (tailHead :: tailRest) ck2
              value targetValue tailResult targetTail tailTargetRun tailGrowth allowedGrowth2 valueWell valueRelated
              tailWell tailRelated
            have targetRun := composeListRuns out tailHead tailRest env2 t0 t t2 ck ck2 targetValue targetTail
              headTargetRun tailTargetRun
            have sourceEq : (res, s) = (match tailResult with
                | .val vs => (.val (value :: vs), tailLast) | .err error => (.err error, tailLast)) := by
              rw [ClosProps.evaluateCons] at wholeRun
              simp only [headRun, tailRun] at wholeRun
              cases tailResult <;> simpa [Flapjack.holHd] using wholeRun.symm
            cases tailResult <;> cases targetTail <;>
              simp only [Prod.mk.injEq] at sourceEq <;>
              obtain ⟨rfl, rfl⟩ := sourceEq <;>
              exact ⟨ck + ck2, _, t2, g3, l3, tailInvariant, tailStateWell,
                stateExtends_trans g1 g2 g3 headGrowth tailGrowth, well3,
                Set.Subset.trans allowedGrowth allowedGrowth2, disjoint3, combined.1,
                targetRun, tailStateRelated, combined.2⟩
private theorem listCaseFromWeight {C F : Type} (x y : ClosLang.Exp) (xs : List ClosLang.Exp)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (smaller : ∀ (es : List ClosLang.Exp) (state : ClosSem.State (NumSet × C) F),
      state.clock ≤ s0.clock → ClosSem.expsWeight es < ClosSem.expsWeight (x :: y :: xs) →
      ExprMotive es env1 state) : ExprMotive (x :: y :: xs) env1 s0 := by
  apply listCase x y xs env1 s0
  · apply smaller [x] s0 (Nat.le_refl _)
    simp only [ClosSem.expsWeight]
    have positive := ClosSem.expWeight_pos y
    omega
  · intro middle clockBound
    apply smaller (y :: xs) middle clockBound
    simp only [ClosSem.expsWeight]
    have positive := ClosSem.expWeight_pos x
    omega
private theorem nilCase {C F : Type}
    (tmp : List ClosLang.Exp × List ClosSem.Value × ClosSem.State (NumSet × C) F)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F) (g0 g : State)
    (env2 : List ClosSem.Value) (t0 : ClosSem.State C F) (ys : List ClosLang.Exp)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State (NumSet × C) F)
    (l l1 : Set Nat) (g1 : State)
    (h : tmp = ([], env1, s0) ∧
      ClosSem.evaluate [] env1 s0 = (res, s) ∧
      res ≠ .err (.abort .typeError) ∧
      calls [] g0 = (ys, g) ∧
      codeInv (some g1) l1 s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle ∧
      everyFnLocationSome [] ∧ everyFnVarsNone [] ∧
      (∀ v ∈ env1, valueWellFormed g1 l1 t0.code v) ∧ stateValuesWellFormed g1 l1 t0.code s0 ∧
      wellFormed g0 ∧ (codeLocations []).Nodup ∧
      Disjoint (Set.image Nat.succ {x | x ∈ codeLocations []}) {x | x ∈ g0.2.map Prod.fst} ∧
      l = {x | x ∈ codeLocations []} \ sptDomain g.1 ∧
      stateExtends g g1 ∧ l ⊆ l1 ∧ Disjoint l1 (sptDomain g1.1) ∧ wellFormed g1 ∧
      envRel (valueRel g1 l1 t0.code) env1 env2 0 (ys.map (fun x => (0, x))) ∧
      stateRel g1 l1 s0 t0 ∧ codeIncludes g.2 t0.code) :
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 s.code s.compile s.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code s ∧
      stateExtends g1 g2 ∧ wellFormed g2 ∧ l1 ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) res ∧
      ClosSem.evaluate ys env2 {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 s t ∧
      resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) res res' := by
  rcases h with ⟨_, sourceRun, _, compileRun, invariant, _, _, _, wellState,
    _, _, _, _, _, _, disjoint, well, _, related, _⟩
  rw [ClosSem.evaluate] at sourceRun
  cases sourceRun
  simp only [calls, callsSingList, Prod.mk.injEq] at compileRun
  rcases compileRun with ⟨rfl, rfl⟩
  refine ⟨0, .val [], t0, g1, l1, invariant, wellState, stateExtends_refl g1 well.2,
    well, Set.Subset.rfl, disjoint, ?_, ?_, related, ?_⟩
  · simp [everyResult]
  · simp [ClosSem.evaluate]
  · exact List.Forall₂.nil
private theorem appPartialCase {C F L : Type} (arg : ClosSem.Value) (args : List ClosSem.Value) (partialValue : ClosSem.Value)
    (loco : Option Nat) (f : ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F) (_loc : L)
    (g : State) (l : Set Nat) (t0 : ClosSem.State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State (NumSet × C) F)
    (f' : ClosSem.Value) (args' : List ClosSem.Value)
    (partialRun : destClosure s0.maxApp loco f (arg :: args) = some (.partialApp partialValue))
    (h : ClosSem.evaluateApp loco f (arg :: args) s0 = (res, s) ∧
      res ≠ .err (.abort .typeError) ∧
      codeInv (some g) l s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle ∧
      valueWellFormed g l t0.code f ∧ (∀ a ∈ (arg :: args), valueWellFormed g l t0.code a) ∧
      stateValuesWellFormed g l t0.code s0 ∧ wellFormed g ∧ Disjoint l (sptDomain g.1) ∧
      valueRel g l t0.code f f' ∧ List.Forall₂ (valueRel g l t0.code) (arg :: args) args' ∧
      stateRel g l s0 t0) :
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 s.code s.compile s.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code s ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) res ∧
      ClosSem.evaluateApp loco f' args' {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 s t ∧ stateExtends g g2 ∧ wellFormed g2 ∧ l ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) res res' := by
  rcases h with ⟨run, notType, inv, wf, wfArgs, wfState, well, disjoint, valRel, argsRel, states⟩
  have maxEq := stateRel_maxApp g l s0 t0 states
  have clockEq := stateRel_clock g l s0 t0 states
  obtain ⟨targetKind, targetDest, targetRel⟩ := destClosure_valueRel s0.maxApp loco f (arg :: args)
    (.partialApp partialValue) g l t0.code f' args' ⟨partialRun, valRel, argsRel⟩
  obtain ⟨targetValue, rfl, relatedValue⟩ := targetRel
  have targetDest : destClosure t0.maxApp loco f' args' = some (.partialApp targetValue) := by
    simpa [← maxEq] using targetDest
  have partialWF := destClosure_partialWellFormed s0.maxApp loco f (arg :: args) partialValue g l t0.code
    ⟨partialRun, wfArgs, wf⟩
  have lengthEq := argsRel.length_eq
  cases args' with
  | nil => simp at lengthEq
  | cons targetArg targetArgs =>
    rw [ClosSem.evaluateApp] at run
    split at run <;> simp_all only [Option.some.injEq, AppKind.partialApp.injEq, reduceCtorEq]
    split at run
    next timeout =>
      simp only [ClosSem.timeoutError, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨0, .err (.abort .timeoutError), {t0 with clock := 0}, g, l, ?_, ?_, ?_, ?_, ?_,
        stateExtends_refl g well.2, well, Set.Subset.rfl, disjoint, ?_⟩
      · simpa using inv
      · simpa [stateValuesWellFormed] using wfState
      · simp [everyResult, everyErrorResult]
      · simp only [Nat.add_zero]
        rw [ClosSem.evaluateApp]
        split <;> simp_all only [Option.some.injEq, AppKind.partialApp.injEq, reduceCtorEq]
        simp_all [ClosSem.timeoutError]
      · simpa only [maxEq] using stateRel_withClock g l s0 t0 0 states
      · simp [resultRel, excRel]
    next enough =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨0, .val [targetValue], decClock (arg :: args).length t0, g, l, ?_, ?_, ?_, ?_, ?_,
        stateExtends_refl g well.2, well, Set.Subset.rfl, disjoint, ?_⟩
      · simpa [decClock] using inv
      · simpa [decClock, stateValuesWellFormed] using wfState
      · simpa [decClock, everyResult] using partialWF
      · simp only [Nat.add_zero]
        rw [ClosSem.evaluateApp]
        split <;> simp_all only [Option.some.injEq, AppKind.partialApp.injEq, reduceCtorEq]
        simp_all [decClock]
      · simpa [decClock, clockEq, lengthEq] using stateRel_withClock g l s0 t0 (s0.clock - (arg :: args).length) states
      · change List.Forall₂ _ _ _
        simpa [decClock] using List.Forall₂.cons relatedValue .nil

private theorem appNilCase {C F L : Type}
    (loco : Option Nat) (f : ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F) (_loc : L)
    (g : State) (l : Set Nat) (t0 : ClosSem.State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State (NumSet × C) F)
    (f' : ClosSem.Value) (args' : List ClosSem.Value)
    (h : ClosSem.evaluateApp loco f [] s0 = (res, s) ∧
      res ≠ .err (.abort .typeError) ∧
      codeInv (some g) l s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle ∧
      valueWellFormed g l t0.code f ∧ (∀ a ∈ ([] : List ClosSem.Value), valueWellFormed g l t0.code a) ∧
      stateValuesWellFormed g l t0.code s0 ∧ wellFormed g ∧ Disjoint l (sptDomain g.1) ∧
      valueRel g l t0.code f f' ∧ List.Forall₂ (valueRel g l t0.code) [] args' ∧
      stateRel g l s0 t0) :
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 s.code s.compile s.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code s ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) res ∧
      ClosSem.evaluateApp loco f' args' {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 s t ∧ stateExtends g g2 ∧ wellFormed g2 ∧ l ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) res res' := by
  rcases h with ⟨run, _, inv, wf, _, wfState, well, disjoint, valRel, argsRel, states⟩
  rw [ClosSem.evaluateApp] at run
  cases run
  cases argsRel
  refine ⟨0, .val [f'], t0, g, l, inv, wfState, ?_, ?_, states,
    stateExtends_refl g well.2, well, Set.Subset.rfl, disjoint, ?_⟩
  · simpa [everyResult] using wf
  · simp [ClosSem.evaluateApp]
  · exact List.Forall₂.cons valRel .nil
private theorem appFullTimeoutCase {C F L : Type} (arg : ClosSem.Value) (args : List ClosSem.Value) (body : ClosLang.Exp) (bodyEnv rest : List ClosSem.Value)
    (loco : Option Nat) (f : ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F) (_loc : L)
    (g : State) (l : Set Nat) (t0 : ClosSem.State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State (NumSet × C) F)
    (f' : ClosSem.Value) (args' : List ClosSem.Value)
    (fullRun : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (timeout : s0.clock < (arg :: args).length - rest.length)
    (h : ClosSem.evaluateApp loco f (arg :: args) s0 = (res, s) ∧
      res ≠ .err (.abort .typeError) ∧
      codeInv (some g) l s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle ∧
      valueWellFormed g l t0.code f ∧ (∀ a ∈ (arg :: args), valueWellFormed g l t0.code a) ∧
      stateValuesWellFormed g l t0.code s0 ∧ wellFormed g ∧ Disjoint l (sptDomain g.1) ∧
      valueRel g l t0.code f f' ∧ List.Forall₂ (valueRel g l t0.code) (arg :: args) args' ∧
      stateRel g l s0 t0) :
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 s.code s.compile s.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code s ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) res ∧
      ClosSem.evaluateApp loco f' args' {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 s t ∧ stateExtends g g2 ∧ wellFormed g2 ∧ l ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) res res' := by
  rcases h with ⟨run, _, inv, _, _, wfState, well, disjoint, valRel, argsRel, states⟩
  have maxEq := stateRel_maxApp g l s0 t0 states
  have clockEq := stateRel_clock g l s0 t0 states
  obtain ⟨targetKind, targetDest, targetRel⟩ := destClosure_valueRel s0.maxApp loco f (arg :: args)
    (.fullApp body bodyEnv rest) g l t0.code f' args' ⟨fullRun, valRel, argsRel⟩
  obtain ⟨fns1, location, i, fns2, args2, rest2, n, rfl, _, restRel, _, _, _⟩ := targetRel
  have targetDest : destClosure t0.maxApp loco f' args' = some (.fullApp (holEl i fns2).2 args2 rest2) := by
    simpa [← maxEq] using targetDest
  have targetTimeout : t0.clock < args'.length - rest2.length := by
    have aLen := argsRel.length_eq
    have rLen := restRel.length_eq
    omega
  have sourceEval : ClosSem.evaluateApp loco f (arg :: args) s0 =
      (.err (.abort .timeoutError), {s0 with clock := 0}) := by
    rw [ClosSem.evaluateApp]
    split <;> simp_all [ClosSem.timeoutError]
    omega
  have resultEq := run.symm.trans sourceEval
  simp only [Prod.mk.injEq] at resultEq
  obtain ⟨rfl, rfl⟩ := resultEq
  have targetEval : ClosSem.evaluateApp loco f' args' t0 =
      (.err (.abort .timeoutError), {t0 with clock := 0}) := by
    cases args' with
    | nil => simp at argsRel
    | cons targetArg targetArgs =>
      rw [ClosSem.evaluateApp]
      split <;> simp_all [ClosSem.timeoutError]
  refine ⟨0, .err (.abort .timeoutError), {t0 with clock := 0}, g, l, ?_, ?_, ?_, ?_, ?_,
    stateExtends_refl g well.2, well, Set.Subset.rfl, disjoint, ?_⟩
  · simpa using inv
  · simpa [stateValuesWellFormed] using wfState
  · simp [everyResult, everyErrorResult]
  · simpa using targetEval
  · exact stateRel_withClock g l s0 t0 0 states
  · simp [resultRel, excRel]

private theorem appMissingClosureImpossible {C F : Type} (arg : ClosSem.Value)
    (args : List ClosSem.Value) (loco : Option Nat) (f : ClosSem.Value)
    (s0 s : ClosSem.State (NumSet × C) F) (res : Result (List ClosSem.Value) ClosSem.Value)
    (missing : destClosure s0.maxApp loco f (arg :: args) = none)
    (run : ClosSem.evaluateApp loco f (arg :: args) s0 = (res, s))
    (safe : res ≠ .err (.abort .typeError)) : False := by
  rw [ClosSem.evaluateApp] at run
  split at run <;> simp_all [ClosSem.typeError]
private def AppMotive {C F : Type} (loco : Option Nat) (f : ClosSem.Value)
    (args : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F) : Prop :=
  ∀ {L : Type} (_loc : L) (g : State) (l : Set Nat) (t0 : ClosSem.State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State (NumSet × C) F)
    (f' : ClosSem.Value) (args' : List ClosSem.Value),
    ClosSem.evaluateApp loco f args s0 = (res, s) ∧ res ≠ .err (.abort .typeError) ∧
      codeInv (some g) l s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle ∧
      valueWellFormed g l t0.code f ∧ (∀ a ∈ args, valueWellFormed g l t0.code a) ∧
      stateValuesWellFormed g l t0.code s0 ∧ wellFormed g ∧ Disjoint l (sptDomain g.1) ∧
      valueRel g l t0.code f f' ∧ List.Forall₂ (valueRel g l t0.code) args args' ∧ stateRel g l s0 t0 →
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 s.code s.compile s.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code s ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) res ∧
      ClosSem.evaluateApp loco f' args' {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 s t ∧ stateExtends g g2 ∧ wellFormed g2 ∧ l ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) res res'
private theorem appNilMotive {C F : Type} (loco : Option Nat) (f : ClosSem.Value)
    (s0 : ClosSem.State (NumSet × C) F) : AppMotive loco f [] s0 := by
  intro L loc g l t0 res s f' args' h
  exact appNilCase loco f s0 loc g l t0 res s f' args' h

private theorem appPartialMotive {C F : Type} (loco : Option Nat) (f : ClosSem.Value)
    (arg : ClosSem.Value) (args : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (partialValue : ClosSem.Value)
    (partialRun : destClosure s0.maxApp loco f (arg :: args) = some (.partialApp partialValue)) :
    AppMotive loco f (arg :: args) s0 := by
  intro L loc g l t0 res s f' args' h
  exact appPartialCase arg args partialValue loco f s0 loc g l t0 res s f' args' partialRun h

private theorem appFullTimeoutMotive {C F : Type} (loco : Option Nat) (f : ClosSem.Value)
    (arg : ClosSem.Value) (args : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (body : ClosLang.Exp) (bodyEnv rest : List ClosSem.Value)
    (fullRun : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (timeout : s0.clock < (arg :: args).length - rest.length) :
    AppMotive loco f (arg :: args) s0 := by
  intro L loc g l t0 res s f' args' h
  exact appFullTimeoutCase arg args body bodyEnv rest loco f s0 loc g l t0 res s f' args' fullRun timeout h
private theorem fullCallBodySafe {C F : Type} (loco : Option Nat) (f arg : ClosSem.Value)
    (args bodyEnv rest : List ClosSem.Value) (body : ClosLang.Exp)
    (s0 middle last : ClosSem.State (NumSet × C) F)
    (bodyResult result : Result (List ClosSem.Value) ClosSem.Value)
    (fullRun : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (enoughClock : (arg :: args).length - rest.length ≤ s0.clock)
    (bodyRun : ClosSem.evaluate [body] bodyEnv
      (ClosSem.decClock ((arg :: args).length - rest.length) s0) = (bodyResult, middle))
    (run : ClosSem.evaluateApp loco f (arg :: args) s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError)) : bodyResult ≠ .err (.abort .typeError) := by
  intro bad
  subst bodyResult
  rw [ClosSem.evaluateApp] at run
  split at run <;> simp_all only [Option.some.injEq, AppKind.fullApp.injEq, reduceCtorEq]
  split at run
  · omega
  · simp only [ClosSem.fixClock, Prod.mk.injEq] at run
    exact safe run.1.symm
private theorem expressionSyntaxOfMember (expressions : List ClosLang.Exp) (body : ClosLang.Exp)
    (member : body ∈ expressions) (locations : everyFnLocationSome expressions)
    (noVars : everyFnVarsNone expressions) (distinct : (codeLocations expressions).Nodup) :
    everyFnLocationSome [body] ∧ everyFnVarsNone [body] ∧ (codeLocations [body]).Nodup := by
  induction expressions with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    simp only [everyFnLocationSome] at locations
    simp only [everyFnVarsNone] at noVars
    have distinct' : (codeLocationsExp first ++ codeLocations rest).Nodup := by
      simpa [codeLocations] using distinct
    rcases member with rfl | member
    · refine ⟨?_, ?_, ?_⟩
      · simpa [everyFnLocationSome] using locations.1
      · simpa [everyFnVarsNone] using noVars.1
      · simpa [codeLocations] using List.Nodup.of_append_left distinct'
    · exact ih member locations.2 noVars.2 (List.Nodup.of_append_right distinct')
private theorem recursiveBodySyntax (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (i : Nat) (well : recClosureWellFormed loc fns) (bound : i < fns.length) :
    everyFnLocationSome [(holEl i fns).2] ∧ everyFnVarsNone [(holEl i fns).2] ∧
      (codeLocations [(holEl i fns).2]).Nodup := by
  have member : (holEl i fns).2 ∈ fns.map Prod.snd := by
    apply List.mem_map.mpr
    refine ⟨holEl i fns, ?_, rfl⟩
    rw [holEl_eq_getElem i fns bound]
    exact List.getElem_mem bound
  exact expressionSyntaxOfMember (fns.map Prod.snd) (holEl i fns).2 member well.1 well.2.1 well.2.2.2
private theorem fullCallBodyFacts (maxApp : Nat) (loco : Option Nat) (f f' : ClosSem.Value)
    (args bodyEnv rest args' : List ClosSem.Value) (body : ClosLang.Exp)
    (g : State) (l : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (fullRun : destClosure maxApp loco f args = some (.fullApp body bodyEnv rest))
    (functionWell : valueWellFormed g l code f)
    (argumentsWell : ∀ a ∈ args, valueWellFormed g l code a)
    (functionRelated : valueRel g l code f f')
    (argumentsRelated : List.Forall₂ (valueRel g l code) args args') :
    ∃ fns1 loc i fns2 targetEnv targetRest n,
      destClosure maxApp loco f' args' = some (.fullApp (holEl i fns2).2 targetEnv targetRest) ∧
      (let m := if isRecClosure f' then fns2.length else 0
       n + m ≤ bodyEnv.length ∧ n + m ≤ targetEnv.length ∧
       List.Forall₂ (valueRel g l code) (bodyEnv.take (n + m)) (targetEnv.take (n + m)) ∧
       envRel (valueRel g l code) (bodyEnv.drop (n + m)) (targetEnv.drop (n + m)) m [holEl i fns2]) ∧
      List.Forall₂ (valueRel g l code) rest targetRest ∧
      recClosureRel g l code loc fns1 fns2 ∧ i < fns1.length ∧ holEl i fns1 = (n, body) ∧
      (∀ a ∈ bodyEnv, valueWellFormed g l code a) ∧
      (∀ a ∈ rest, valueWellFormed g l code a) ∧
      everyFnLocationSome [body] ∧ everyFnVarsNone [body] ∧ (codeLocations [body]).Nodup := by
  obtain ⟨targetKind, targetDest, targetFacts⟩ :=
    destClosure_valueRel maxApp loco f args (.fullApp body bodyEnv rest) g l code f' args'
      ⟨fullRun, functionRelated, argumentsRelated⟩
  obtain ⟨fns1, loc, i, fns2, targetEnv, targetRest, n, rfl, envRelated, restRelated,
    groupRelated, bound, selected⟩ := targetFacts
  obtain ⟨_, _, _, _, _, _, bodyEnvWell, restWell, _, _, _⟩ :=
    destClosure_fullWellFormed (A := Unit) (B := Unit) maxApp loco f args body bodyEnv rest g l code
      ⟨fullRun, functionWell, argumentsWell⟩
  have groupWell : recClosureWellFormed loc fns1 := by
    obtain ⟨_, groupWell, _⟩ := groupRelated
    exact groupWell
  have bodySyntax := recursiveBodySyntax loc fns1 i groupWell bound
  have bodyEq : (holEl i fns1).2 = body := congrArg Prod.snd selected
  rw [bodyEq] at bodySyntax
  exact ⟨fns1, loc, i, fns2, targetEnv, targetRest, n, targetDest, envRelated, restRelated,
    groupRelated, bound, selected, bodyEnvWell, restWell, bodySyntax⟩
private theorem fullCallBodyEnvRelated (g : State) (l : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc i n : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (f' : ClosSem.Value)
    (bodyEnv targetEnv : List ClosSem.Value)
    (group : recClosureRel g l code loc fns1 fns2) (bound : i < fns1.length)
    (selected : (holEl i fns1).1 = n)
    (envRelated : let m := if isRecClosure f' then fns2.length else 0
      n + m ≤ bodyEnv.length ∧ n + m ≤ targetEnv.length ∧
      List.Forall₂ (valueRel g l code) (bodyEnv.take (n + m)) (targetEnv.take (n + m)) ∧
      envRel (valueRel g l code) (bodyEnv.drop (n + m)) (targetEnv.drop (n + m)) m [holEl i fns2]) :
    envRel (valueRel g l code) bodyEnv targetEnv 0 [(0, (holEl i fns2).2)] := by
  have arities := recClosureRel_arities g l code loc fns1 fns2 group
  have lengths : fns2.length = fns1.length := by
    have h := congrArg List.length arities
    simpa using h
  have bound2 : i < fns2.length := by omega
  have targetArity : (holEl i fns2).1 = n := by
    have same := congrArg (fun values : List Nat => values[i]?) arities
    simp only [List.getElem?_map, List.getElem?_eq_getElem bound, List.getElem?_eq_getElem bound2,
      Option.map_some, Option.some.injEq] at same
    have sourceArity : fns1[i].1 = n := by simpa [holEl_eq_getElem i fns1 bound] using selected
    simpa [holEl_eq_getElem i fns2 bound2] using same.trans sourceArity
  let m := if isRecClosure f' then fns2.length else 0
  obtain ⟨bound1, bound2, prefixRel, suffix⟩ := envRelated
  have adjusted : envRel (valueRel g l code) (bodyEnv.drop (n + m)) (targetEnv.drop (n + m))
      0 [(n + m, (holEl i fns2).2)] := by
    cases entry : holEl i fns2 with
    | mk arity body =>
      have arityEq : arity = n := by simpa [entry] using targetArity
      subst arity
      simpa [envRel, m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, entry] using suffix
  exact envRel_dropArgs (valueRel g l code) (n + m) bodyEnv targetEnv 0 (holEl i fns2).2
    ⟨adjusted, prefixRel, bound1, bound2⟩
private theorem selectedGroupBodyCall (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (i n : Nat)
    (body : ClosLang.Exp) (g0 g : State) (converted : List ClosLang.Exp)
    (groupWell : recClosureWellFormed loc fns) (initialWell : wellFormed g0)
    (fresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {k | k ∈ codeLocations (fns.map Prod.snd)} ∧
      label ∈ g0.2.map Prod.fst))
    (run : calls (fns.map Prod.snd) g0 = (converted, g))
    (bound : i < fns.length) (selected : holEl i fns = (n, body)) :
    ∃ ga gb,
      calls [body] ga = ([holEl i converted], gb) ∧
      stateExtends g0 ga ∧ stateExtends ga gb ∧ stateExtends gb g ∧ wellFormed ga ∧ wellFormed gb ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {x | x ∈ codeLocations [body]} ∧ label ∈ ga.2.map Prod.fst)) ∧
      Set.Subset {x | x ∈ ga.2.map Prod.fst} (Set.union {x | x ∈ g0.2.map Prod.fst}
        (Set.image Nat.succ {x | x ∈ codeLocations ((fns.map Prod.snd).take i)})) ∧
      Set.Subset (Set.diff {x | x ∈ codeLocations [body]} (sptDomain gb.1))
        (Set.diff {x | x ∈ codeLocations (fns.map Prod.snd)} (sptDomain g.1)) := by
  have mapBound : i < (fns.map Prod.snd).length := by simpa using bound
  have bodyEq : holEl i (fns.map Prod.snd) = body := by
    rw [holEl_eq_getElem i _ mapBound]
    simpa [holEl_eq_getElem i fns bound] using congrArg Prod.snd selected
  have isolated := calls_el_sing (fns.map Prod.snd) g0 converted g i
    ⟨run, mapBound, initialWell.2, groupWell.2.2.2, fresh, initialWell, groupWell.1⟩
  simpa only [bodyEq] using isolated
private theorem indexedConvertedBody (fns : List (Nat × ClosLang.Exp)) (es : List ClosLang.Exp)
    (i : Nat) (lengthEq : es.length = fns.length) (bound : i < fns.length) :
    (holEl i ((fns.map Prod.fst).zip es)).2 = holEl i es := by
  have esBound : i < es.length := by omega
  have zipBound : i < ((fns.map Prod.fst).zip es).length := by simp [lengthEq, bound]
  rw [holEl_eq_getElem i _ zipBound, holEl_eq_getElem i es esBound]
  simp
private theorem ordinaryGroupBodyCall (loc : Nat) (fns1 fns2 : List (Nat × ClosLang.Exp))
    (i n : Nat) (body : ClosLang.Exp) (g0 gEnd g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (es : List ClosLang.Exp)
    (groupWell : recClosureWellFormed loc fns1) (initialWell : wellFormed g0)
    (fresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {k | k ∈ codeLocations (fns1.map Prod.snd)} ∧
      label ∈ g0.2.map Prod.fst))
    (run : calls (fns1.map Prod.snd) g0 = (es, gEnd))
    (targetGroup : fns2 = (fns1.map Prod.fst).zip es)
    (growth : stateExtends gEnd g)
    (locationsAllowed : Set.Subset (Set.diff {x | x ∈ codeLocations (fns1.map Prod.snd)} (sptDomain gEnd.1)) allowed)
    (included : codeIncludes gEnd.2 code)
    (bound : i < fns1.length) (selected : holEl i fns1 = (n, body)) :
    ∃ ga gb,
      calls [body] ga = ([(holEl i fns2).2], gb) ∧
      stateExtends gb g ∧ wellFormed ga ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {x | x ∈ codeLocations [body]} ∧ label ∈ ga.2.map Prod.fst)) ∧
      Set.Subset (Set.diff {x | x ∈ codeLocations [body]} (sptDomain gb.1)) allowed ∧
      codeIncludes gb.2 code := by
  obtain ⟨ga, gb, isolated, _, _, finalGrowth, gaWell, _, localFresh, _, localBound⟩ :=
    selectedGroupBodyCall loc fns1 i n body g0 gEnd es groupWell initialWell fresh run bound selected
  have lengthEq : es.length = fns1.length := by
    simpa using calls_length (fns1.map Prod.snd) g0 es gEnd run
  have targetBody : (holEl i fns2).2 = holEl i es := by
    rw [targetGroup]
    exact indexedConvertedBody fns1 es i lengthEq bound
  refine ⟨ga, gb, ?_, stateExtends_trans gb gEnd g finalGrowth growth, gaWell,
    localFresh, Set.Subset.trans localBound locationsAllowed, ?_⟩
  · simpa only [targetBody] using isolated
  · exact codeIncludes_subg gb gEnd code finalGrowth included

private theorem applyOrdinaryBodyIH {C F : Type} (loco : Option Nat) (f f' arg : ClosSem.Value)
    (args bodyEnv rest targetEnv : List ClosSem.Value) (body : ClosLang.Exp)
    (s0 middle last : ClosSem.State (NumSet × C) F) (t0 : ClosSem.State C F)
    (g0 gEnd g : State) (allowed : Set Nat) (es : List ClosLang.Exp)
    (loc i n : Nat) (fns1 fns2 : List (Nat × ClosLang.Exp))
    (bodyResult result : Result (List ClosSem.Value) ClosSem.Value)
    (ih : ∀ (e : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock < s0.clock → ExprMotive [e] env state)
    (fullRun : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (enoughClock : (arg :: args).length - rest.length ≤ s0.clock)
    (bodyRun : ClosSem.evaluate [body] bodyEnv
      (ClosSem.decClock ((arg :: args).length - rest.length) s0) = (bodyResult, middle))
    (run : ClosSem.evaluateApp loco f (arg :: args) s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (invariant : codeInv (some g) allowed s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle)
    (stateWell : stateValuesWellFormed g allowed t0.code s0)
    (group : recClosureRel g allowed t0.code loc fns1 fns2)
    (groupWell : recClosureWellFormed loc fns1) (initialWell : wellFormed g0)
    (fresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {k | k ∈ codeLocations (fns1.map Prod.snd)} ∧
      label ∈ g0.2.map Prod.fst))
    (groupRun : calls (fns1.map Prod.snd) g0 = (es, gEnd))
    (targetGroup : fns2 = (fns1.map Prod.fst).zip es)
    (growth : stateExtends gEnd g)
    (locationsAllowed : Set.Subset (Set.diff {x | x ∈ codeLocations (fns1.map Prod.snd)} (sptDomain gEnd.1)) allowed)
    (included : codeIncludes gEnd.2 t0.code) (bound : i < fns1.length) (selected : holEl i fns1 = (n, body))
    (envWell : ∀ v ∈ bodyEnv, valueWellFormed g allowed t0.code v)
    (envRelated : let m := if isRecClosure f' then fns2.length else 0
      n + m ≤ bodyEnv.length ∧ n + m ≤ targetEnv.length ∧
      List.Forall₂ (valueRel g allowed t0.code) (bodyEnv.take (n + m)) (targetEnv.take (n + m)) ∧
      envRel (valueRel g allowed t0.code) (bodyEnv.drop (n + m)) (targetEnv.drop (n + m)) m [holEl i fns2])
    (disjoint : Disjoint allowed (sptDomain g.1)) (well : wellFormed g)
    (states : stateRel g allowed s0 t0) :
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 middle.code middle.compile middle.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code middle ∧
      stateExtends g g2 ∧ wellFormed g2 ∧ allowed ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) bodyResult ∧
      ClosSem.evaluate [(holEl i fns2).2] targetEnv
        {ClosSem.decClock ((arg :: args).length - rest.length) t0 with
          clock := (ClosSem.decClock ((arg :: args).length - rest.length) t0).clock + ck} = (res', t) ∧
      stateRel g2 l2 middle t ∧
      resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) bodyResult res' := by
  have bodySafe := fullCallBodySafe loco f arg args bodyEnv rest body s0 middle last bodyResult result
    fullRun enoughClock bodyRun run safe
  have remaining := ClosSem.destClosure_full_remaining_lt s0.maxApp loco f (arg :: args) bodyEnv rest body fullRun
  have clockLess : (ClosSem.decClock ((arg :: args).length - rest.length) s0).clock < s0.clock := by
    simp only [ClosSem.decClock]
    omega
  obtain ⟨ga, gb, bodyCompile, bodyGrowth, gaWell, bodyFresh, bodyBound, bodyIncluded⟩ :=
    ordinaryGroupBodyCall loc fns1 fns2 i n body g0 gEnd g allowed t0.code es groupWell initialWell fresh
      groupRun targetGroup growth locationsAllowed included bound selected
  have sourceSyntax := recursiveBodySyntax loc fns1 i groupWell bound
  have bodyEq : (holEl i fns1).2 = body := congrArg Prod.snd selected
  rw [bodyEq] at sourceSyntax
  have sourceArity : (holEl i fns1).1 = n := congrArg Prod.fst selected
  have targetRelated := fullCallBodyEnvRelated g allowed t0.code loc i n fns1 fns2 f' bodyEnv targetEnv
    group bound sourceArity envRelated
  have startStates : stateRel g allowed (ClosSem.decClock ((arg :: args).length - rest.length) s0)
      (ClosSem.decClock ((arg :: args).length - rest.length) t0) := by
    have same := stateRel_withClock g allowed s0 t0
      (s0.clock - ((arg :: args).length - rest.length)) states
    have clockEq := stateRel_clock g allowed s0 t0 states
    simpa only [ClosSem.decClock, ← clockEq] using same
  have freshDisjoint : Disjoint (Set.image Nat.succ {x | x ∈ codeLocations [body]})
      {x | x ∈ ga.2.map Prod.fst} := by
    apply Set.disjoint_left.mpr
    intro key a b
    exact bodyFresh key ⟨a, b⟩
  have result := ih body bodyEnv (ClosSem.decClock ((arg :: args).length - rest.length) s0) clockLess
    ([body], bodyEnv, ClosSem.decClock ((arg :: args).length - rest.length) s0)
    ga gb targetEnv (ClosSem.decClock ((arg :: args).length - rest.length) t0) [(holEl i fns2).2]
    bodyResult middle ({x | x ∈ codeLocations [body]} \ sptDomain gb.1) allowed g
    ⟨rfl, bodyRun, bodySafe, bodyCompile, by simpa [ClosSem.decClock] using invariant,
      sourceSyntax.1, sourceSyntax.2.1, by simpa [ClosSem.decClock] using envWell,
      by simpa [ClosSem.decClock, stateValuesWellFormed] using stateWell,
      gaWell, sourceSyntax.2.2, freshDisjoint, rfl, bodyGrowth, bodyBound, disjoint, well,
      by simpa [ClosSem.decClock] using targetRelated, startStates, by simpa [ClosSem.decClock] using bodyIncluded⟩
  exact result
private theorem optimizedGroupCodeLookup (loc i n : Nat) (fns : List (Nat × ClosLang.Exp))
    (es : List ClosLang.Exp) (endState : State)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (lengthEq : es.length = fns.length) (bound : i < fns.length)
    (arity : (holEl i fns).1 = n)
    (included : codeIncludes (codeListSource loc ((fns.map Prod.fst).zip es) endState).2 code) :
    code.lookup (loc + 2 * i + 1) = some (n, holEl i es) := by
  let entries := (fns.map Prod.fst).zip es
  have entriesLength : entries.length = fns.length := by simp [entries, lengthEq]
  have entryBound : i < entries.length := by omega
  have esBound : i < es.length := by omega
  have lookup : holALookup (codeListSource loc entries endState).2 (loc + 2 * i + 1) =
      some (holEl i entries) := by
    rw [codeListSource_alookup]
    have unique : ∀ a b, (a < entries.length ∧ loc + 2 * i + 1 = loc + 2 * a + 1) →
        (b < entries.length ∧ loc + 2 * i + 1 = loc + 2 * b + 1) → a = b := by
      intro a b ha hb
      omega
    have choice : holOptionSome (fun j => j < entries.length ∧ loc + 2 * i + 1 = loc + 2 * j + 1) = some i :=
      (holOptionSome_eq_some_iff _ unique i).2 ⟨entryBound, rfl⟩
    rw [choice]
  have entryEq : holEl i entries = (n, holEl i es) := by
    rw [holEl_eq_getElem i entries entryBound, holEl_eq_getElem i es esBound]
    have arity' : fns[i].1 = n := by simpa [holEl_eq_getElem i fns bound] using arity
    simp [entries, arity']
  rw [← entryEq]
  exact codeIncludes_lookup _ code _ _ ⟨included, lookup⟩
private theorem optimizedGroupStub (trace : BackendCommon.Tra) (start loc i n : Nat)
    (fns : List (Nat × ClosLang.Exp)) (bound : i < fns.length)
    (arity : (holEl i fns).1 = n) :
    (holEl i (callsListSource trace start loc fns)).2 =
      .call trace 0 (loc + 2 * i + 1) (variablesSource trace 1 n) := by
  have mapEq := callsListSource_mapIdx (A := Unit) (B := ClosLang.Exp) trace loc () start
  have stubEq := congrFun mapEq fns
  rw [stubEq]
  rw [holEl_eq_getElem i _ (by simpa using bound)]
  simp only [List.getElem_mapIdx]
  have arity' : fns[i].1 = n := by simpa [holEl_eq_getElem i fns bound] using arity
  simp [arity']
private theorem evaluateOptimizedStub {C F : Type} (trace : BackendCommon.Tra)
    (label n : Nat) (compiled : ClosLang.Exp) (env : List ClosSem.Value)
    (state : ClosSem.State C F) (enough : n ≤ env.length)
    (lookup : state.code.lookup label = some (n, compiled)) :
    ClosSem.evaluate [.call trace 0 label (variablesSource trace 1 n)] env
      {state with clock := state.clock + 1} = ClosSem.evaluate [compiled] (env.take n) state := by
  rw [ClosSem.evaluate]
  rw [ClosSem.fixClock_evaluate_source]
  rw [evaluate_variables env _ n trace 1]
  simp only [enough, ↓reduceIte]
  simp [ClosSem.findCode, lookup, List.length_take, Nat.min_eq_left enough, ClosSem.decClock]
private theorem evaluateOptimizedGroupBody {C F : Type} (trace : BackendCommon.Tra)
    (start loc i n : Nat) (fns : List (Nat × ClosLang.Exp)) (es : List ClosLang.Exp)
    (endState : State) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (lengthEq : es.length = fns.length) (bound : i < fns.length)
    (arity : (holEl i fns).1 = n) (enough : n ≤ env.length)
    (included : codeIncludes (codeListSource loc ((fns.map Prod.fst).zip es) endState).2 state.code) :
    ClosSem.evaluate [(holEl i (callsListSource trace start loc fns)).2] env
      {state with clock := state.clock + 1} = ClosSem.evaluate [holEl i es] (env.take n) state := by
  rw [optimizedGroupStub trace start loc i n fns bound arity]
  apply evaluateOptimizedStub trace (loc + 2 * i + 1) n (holEl i es) env state enough
  exact optimizedGroupCodeLookup loc i n fns es endState state.code lengthEq bound arity included
private theorem envRel_takeTarget {A B : Type} (R : A → B → Prop) (n : Nat)
    (source : List A) (target : List B) (body : ClosLang.Exp)
    (enough : n ≤ target.length)
    (whole : envRel R source target 0 [(0, body)])
    (prefixRel : List.Forall₂ R (source.take n) (target.take n))
    (freeBound : ∀ i, ClosProps.freeVar i body → i < n) :
    envRel R source (target.take n) 0 [(0, body)] := by
  unfold envRel at whole ⊢
  have targetLen : (target.take n).length = n := by simp [enough]
  by_cases targetSame : source.length = (target.take n).length
  · rw [if_pos targetSame]
    have sourceShort : source.length ≤ n := by omega
    simpa [List.take_of_length_le sourceShort] using prefixRel
  · rw [if_neg targetSame]
    intro i used
    obtain ⟨fn, mem, free⟩ := used
    simp only [List.mem_singleton] at mem
    subst fn
    simp only [Nat.zero_add] at free
    have below : i < n := freeBound i free
    have targetBound : i < target.length := by omega
    have takeBound : i < (target.take n).length := by omega
    by_cases same : source.length = target.length
    · rw [if_pos same] at whole
      have sourceBound : i < source.length := by omega
      have value := whole.get sourceBound targetBound
      refine ⟨sourceBound, takeBound, ?_⟩
      simpa using value
    · rw [if_neg same] at whole
      obtain ⟨sourceBound, _, value⟩ := whole i ⟨(0, body), by simp, by simpa using free⟩
      refine ⟨sourceBound, takeBound, ?_⟩
      simpa using value
private theorem freeGuardBoundsBody (body : ClosLang.Exp) (n : Nat)
    (guard : ∀ i, DbVars.hasVar i (free [body]).2 = true → i < n) :
    ∀ i, ClosProps.freeVar i body → i < n := by
  intro i used
  have agreement := freeThm [body]
  cases analyzed : free [body] with
  | mk result vars =>
    simp only [analyzed] at agreement guard
    apply guard i
    apply (agreement i).2.mp
    exact used
private theorem optimizedBodyEnvRel (R : ClosSem.Value → ClosSem.Value → Prop)
    (n m : Nat) (source target : List ClosSem.Value) (body : ClosLang.Exp)
    (enough : n + m ≤ target.length)
    (whole : envRel R source target 0 [(0, body)])
    (longPrefix : List.Forall₂ R (source.take (n + m)) (target.take (n + m)))
    (guard : ∀ i, DbVars.hasVar i (free [body]).2 = true → i < n) :
    envRel R source (target.take n) 0 [(0, body)] := by
  have prefixRel := List.forall₂_take n longPrefix
  simp only [List.take_take, Nat.min_eq_left (Nat.le_add_right n m)] at prefixRel
  exact envRel_takeTarget R n source target body (by omega) whole prefixRel (freeGuardBoundsBody body n guard)
private theorem optimizedSelectedFreeGuard (fns : List (Nat × ClosLang.Exp)) (es : List ClosLang.Exp)
    (i n : Nat) (body : ClosLang.Exp) (bound : i < fns.length)
    (selected : holEl i fns = (n, body))
    (guard : List.Forall₂ (fun fn converted => ∀ v, DbVars.hasVar v (free [converted]).2 = true → v < fn.1)
      fns es) :
    ∀ v, DbVars.hasVar v (free [holEl i es]).2 = true → v < n := by
  have esBound : i < es.length := by have lengths := guard.length_eq; omega
  have entry := guard.get bound esBound
  have arity : fns[i].1 = n := by
    simpa [holEl_eq_getElem i fns bound] using congrArg Prod.fst selected
  simpa [holEl_eq_getElem i es esBound, arity] using
    (show ∀ v, DbVars.hasVar v (free [es[i]]).2 = true → v < fns[i].1 from entry)
private theorem envRel_replaceBody {A B : Type} (R : A → B → Prop) (source : List A) (target : List B)
    (oldBody newBody : ClosLang.Exp)
    (related : envRel R source target 0 [(0, oldBody)])
    (uses : ∀ i, ClosProps.freeVar i newBody → ClosProps.freeVar i oldBody) :
    envRel R source target 0 [(0, newBody)] := by
  unfold envRel at related ⊢
  by_cases same : source.length = target.length
  · simpa [same] using related
  · simp only [same, ↓reduceIte] at related ⊢
    intro i ⟨fn, mem, used⟩
    simp only [List.mem_singleton] at mem
    subst fn
    simp only [Nat.zero_add] at used
    exact related i ⟨(0, oldBody), by simp, by simpa using uses i used⟩

private theorem optimizedBodyFullEnvRel {A B : Type} (R : A → B → Prop)
    (source : List A) (target : List B) (trace : BackendCommon.Tra) (label n : Nat)
    (body : ClosLang.Exp)
    (stubRelated : envRel R source target 0 [(0, .call trace 0 label (variablesSource trace 1 n))])
    (guard : ∀ i, DbVars.hasVar i (free [body]).2 = true → i < n) :
    envRel R source target 0 [(0, body)] := by
  apply envRel_replaceBody R source target _ body stubRelated
  intro i used
  have below := freeGuardBoundsBody body n guard i used
  simp only [ClosProps.freeVar, ClosProps.freeVars, ClosProps.freeVarExp, or_false]
  exact (freeVars_variables i n trace 1).2 below
private theorem optimizedCallBodyEnvRel (g : State) (l : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc i n start : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (es : List ClosLang.Exp)
    (trace : BackendCommon.Tra) (f' : ClosSem.Value) (body : ClosLang.Exp)
    (bodyEnv targetEnv : List ClosSem.Value)
    (group : recClosureRel g l code loc fns1 fns2) (bound : i < fns1.length)
    (selected : holEl i fns1 = (n, body))
    (targetGroup : fns2 = callsListSource trace start loc fns1)
    (guard : List.Forall₂ (fun fn converted => ∀ v, DbVars.hasVar v (free [converted]).2 = true → v < fn.1)
      fns1 es)
    (envRelated : let m := if isRecClosure f' then fns2.length else 0
      n + m ≤ bodyEnv.length ∧ n + m ≤ targetEnv.length ∧
      List.Forall₂ (valueRel g l code) (bodyEnv.take (n + m)) (targetEnv.take (n + m)) ∧
      envRel (valueRel g l code) (bodyEnv.drop (n + m)) (targetEnv.drop (n + m)) m [holEl i fns2]) :
    envRel (valueRel g l code) bodyEnv (targetEnv.take n) 0 [(0, holEl i es)] := by
  have sourceArity : (holEl i fns1).1 = n := congrArg Prod.fst selected
  have wholeStub := fullCallBodyEnvRelated g l code loc i n fns1 fns2 f' bodyEnv targetEnv
    group bound sourceArity envRelated
  rw [targetGroup, optimizedGroupStub trace start loc i n fns1 bound sourceArity] at wholeStub
  have freeBound := optimizedSelectedFreeGuard fns1 es i n body bound selected guard
  have wholeBody := optimizedBodyFullEnvRel (valueRel g l code) bodyEnv targetEnv trace
    (loc + 2 * i + 1) n (holEl i es) wholeStub freeBound
  let m := if isRecClosure f' then fns2.length else 0
  exact optimizedBodyEnvRel (valueRel g l code) n m bodyEnv targetEnv (holEl i es)
    envRelated.2.1 wholeBody envRelated.2.2.1 freeBound
private theorem rerunOptimizedGroup (loc count : Nat) (g0 gEnd : State)
    (replacement : List (Nat × Nat × ClosLang.Exp)) (bodies es : List ClosLang.Exp)
    (run : calls bodies (insertEachSource loc count g0) = (es, gEnd)) :
    ∃ added,
      gEnd.2 = added ++ (insertEachSource loc count g0).2 ∧
      calls bodies (insertWithCode replacement loc count g0) =
        (es, (gEnd.1, added ++ (insertWithCode replacement loc count g0).2)) := by
  obtain ⟨added, suffix⟩ := calls_suffix bodies (insertEachSource loc count g0) es gEnd run
  refine ⟨added, suffix.symm, ?_⟩
  apply calls_replace_snd bodies (insertEachSource loc count g0) es gEnd
    (insertWithCode replacement loc count g0) added
  exact ⟨run, (insertWithCode_fst replacement loc count g0).symm, suffix.symm⟩
private theorem optimizedInitialFacts (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (g0 : State) (replacement : List (Nat × Nat × ClosLang.Exp))
    (groupWell : recClosureWellFormed loc fns) (well : wellFormed g0)
    (freshCode : ∀ label, ¬ (label ∈ Set.image Nat.succ {k | k ∈ codeLocations (fns.map Prod.snd)} ∧
      label ∈ g0.2.map Prod.fst))
    (freshSlots : ∀ label, ¬ (label ∈ (List.range fns.length).map (fun i => 2 * i + loc + 1) ∧
      label ∈ g0.2.map Prod.fst)) :
    wellFormed (insertWithCode replacement loc fns.length g0) ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {k | k ∈ codeLocations (fns.map Prod.snd)} ∧
        label ∈ (insertWithCode replacement loc fns.length g0).2.map Prod.fst)) := by
  have freshDomain : ∀ x, ¬ (x ∈ (List.range fns.length).map (fun i => loc + 2 * i) ∧
      sptDomain g0.1 x) := by
    intro x ⟨generated, known⟩
    obtain ⟨i, ibound, eq⟩ := List.mem_map.mp generated
    have oldLabel : Nat.succ x ∈ g0.2.map Prod.fst := by
      change Nat.succ x ∈ {label | label ∈ g0.2.map Prod.fst}
      rw [well.1]
      exact ⟨x, known, rfl⟩
    apply freshSlots (Nat.succ x)
    refine ⟨List.mem_map.mpr ⟨i, ibound, ?_⟩, oldLabel⟩
    omega
  refine ⟨insertWithCode_wellFormed replacement loc fns.length g0 ⟨well, freshDomain⟩, ?_⟩
  intro label ⟨⟨x, codeMember, labelEq⟩, inserted⟩
  rw [insertWithCode_labels] at inserted
  rcases List.mem_append.mp inserted with generated | old
  · obtain ⟨i, ibound, eq⟩ := List.mem_map.mp (List.mem_reverse.mp generated)
    apply groupWell.2.2.1 x
    refine ⟨List.mem_map.mpr ⟨i, ibound, ?_⟩, codeMember⟩
    omega
  · exact freshCode label ⟨⟨x, codeMember, labelEq⟩, old⟩
private theorem optimizedGeneratedLookup (loc i : Nat) (fns : List (Nat × ClosLang.Exp))
    (es : List ClosLang.Exp) (endState current : State)
    (lengthEq : es.length = fns.length) (bound : i < fns.length)
    (growth : stateExtends (codeListSource loc ((fns.map Prod.fst).zip es) endState) current) :
    holALookup current.2 (2 * i + loc + 1) = some ((holEl i fns).1, holEl i es) := by
  let entries := (fns.map Prod.fst).zip es
  have entriesLength : entries.length = fns.length := by simp [entries, lengthEq]
  have entryBound : i < entries.length := by omega
  have esBound : i < es.length := by omega
  have lookup : holALookup (codeListSource loc entries endState).2 (2 * i + loc + 1) =
      some (holEl i entries) := by
    rw [codeListSource_alookup]
    have unique : ∀ a b, (a < entries.length ∧ 2 * i + loc + 1 = loc + 2 * a + 1) →
        (b < entries.length ∧ 2 * i + loc + 1 = loc + 2 * b + 1) → a = b := by
      intro a b ha hb
      omega
    have choice : holOptionSome (fun j => j < entries.length ∧ 2 * i + loc + 1 = loc + 2 * j + 1) = some i :=
      (holOptionSome_eq_some_iff _ unique i).2 ⟨entryBound, by omega⟩
    rw [choice]
  have entryEq : holEl i entries = ((holEl i fns).1, holEl i es) := by
    rw [holEl_eq_getElem i entries entryBound, holEl_eq_getElem i es esBound,
      holEl_eq_getElem i fns bound]
    simp [entries]
  rw [← entryEq]
  exact growth.2.1 _ _ lookup
private theorem optimizedInsertionFreshness (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (g0 : State) (replacement added : List (Nat × Nat × ClosLang.Exp))
    (well : wellFormed g0)
    (freshSlots : ∀ label, ¬ (label ∈ (List.range fns.length).map (fun i => 2 * i + loc + 1) ∧
      label ∈ g0.2.map Prod.fst))
    (distinct : ((added ++ (insertWithCode replacement loc fns.length g0).2).map Prod.fst).Nodup) :
    (∀ x, ¬ (x ∈ (List.range fns.length).map (fun i => 2 * i + loc + 1) ∧
      x ∈ Set.image Nat.succ (sptDomain g0.1))) ∧
    (∀ x, ¬ (x ∈ added.map Prod.fst ∧ x ∈ Set.image Nat.succ (sptDomain g0.1))) := by
  constructor
  · intro x ⟨generated, oldDomain⟩
    apply freshSlots x
    refine ⟨generated, ?_⟩
    change x ∈ {label | label ∈ g0.2.map Prod.fst}
    rw [well.1]
    exact oldDomain
  · intro x ⟨newLabel, oldDomain⟩
    have oldLabel : x ∈ g0.2.map Prod.fst := by
      change x ∈ {label | label ∈ g0.2.map Prod.fst}
      rw [well.1]
      exact oldDomain
    simp only [List.map_append, insertWithCode_labels] at distinct
    have apart := (List.nodup_append.mp distinct).2.2
    apply apart x newLabel x ?_ rfl
    exact List.mem_append_right _ oldLabel
private theorem optimizedGroupBodyCall (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (i n : Nat) (body : ClosLang.Exp) (g0 gEnd g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (es : List ClosLang.Exp)
    (groupWell : recClosureWellFormed loc fns) (initialWell : wellFormed g0)
    (freshCode : ∀ label, ¬ (label ∈ Set.image Nat.succ {k | k ∈ codeLocations (fns.map Prod.snd)} ∧
      label ∈ g0.2.map Prod.fst))
    (freshSlots : ∀ label, ¬ (label ∈ (List.range fns.length).map (fun i => 2 * i + loc + 1) ∧
      label ∈ g0.2.map Prod.fst))
    (run : calls (fns.map Prod.snd) (insertEachSource loc fns.length g0) = (es, gEnd))
    (growth : stateExtends (codeListSource loc ((fns.map Prod.fst).zip es) gEnd) g)
    (locationsAllowed : Set.Subset (Set.diff {x | x ∈ codeLocations (fns.map Prod.snd)} (sptDomain gEnd.1)) allowed)
    (included : codeIncludes (codeListSource loc ((fns.map Prod.fst).zip es) gEnd).2 code)
    (bound : i < fns.length) (selected : holEl i fns = (n, body)) :
    ∃ ga gb,
      calls [body] ga = ([holEl i es], gb) ∧
      stateExtends gb g ∧ wellFormed ga ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {x | x ∈ codeLocations [body]} ∧ label ∈ ga.2.map Prod.fst)) ∧
      Set.Subset (Set.diff {x | x ∈ codeLocations [body]} (sptDomain gb.1)) allowed ∧
      codeIncludes gb.2 code := by
  obtain ⟨added, suffix, rerun⟩ := rerunOptimizedGroup loc fns.length g0 gEnd g.2 (fns.map Prod.snd) es run
  have oldCode : gEnd.2 = added ++ g0.2 := by simpa [insertEach_snd] using suffix
  have lengthEq : es.length = fns.length := by
    simpa using calls_length (fns.map Prod.snd) (insertEachSource loc fns.length g0) es gEnd run
  obtain ⟨newWell, newFresh⟩ := optimizedInitialFacts loc fns g0 g.2 groupWell initialWell freshCode freshSlots
  obtain ⟨ga, gb, bodyCompile, _, _, bodyGrowth, gaWell, _, bodyFresh, _, bodyBound⟩ :=
    selectedGroupBodyCall loc fns i n body (insertWithCode g.2 loc fns.length g0)
      (gEnd.1, added ++ (insertWithCode g.2 loc fns.length g0).2) es
      groupWell newWell newFresh rerun bound selected
  have distinct : ((added ++ (insertWithCode g.2 loc fns.length g0).2).map Prod.fst).Nodup := bodyGrowth.2.2
  obtain ⟨slotsFresh, addedFresh⟩ := optimizedInsertionFreshness loc fns g0 g.2 added initialWell freshSlots distinct
  have lookups : ∀ j, j < fns.length → holALookup g.2 (2 * j + loc + 1) =
      some ((holEl j fns).1, holEl j es) := by
    intro j jbound
    exact optimizedGeneratedLookup loc j fns es gEnd g lengthEq jbound growth
  have replacementGrowth := stateExtends_insertWithCode gEnd added loc g0 gb fns es g.2
    ⟨bodyGrowth, oldCode, lengthEq.symm, initialWell, slotsFresh, addedFresh, lookups⟩
  have codeGrowth := stateExtends_trans gb _ _ bodyGrowth replacementGrowth
  have finalGrowth := stateExtends_trans gb _ g codeGrowth growth
  refine ⟨ga, gb, bodyCompile, finalGrowth, gaWell, bodyFresh, ?_, ?_⟩
  · exact Set.Subset.trans bodyBound locationsAllowed
  · exact codeIncludes_subg gb _ code codeGrowth included
private theorem applyOptimizedBodyIH {C F : Type} (loco : Option Nat) (f f' arg : ClosSem.Value)
    (args bodyEnv rest targetEnv : List ClosSem.Value) (body : ClosLang.Exp)
    (s0 middle last : ClosSem.State (NumSet × C) F) (t0 : ClosSem.State C F)
    (g0 gEnd g : State) (allowed : Set Nat) (es : List ClosLang.Exp)
    (loc i n start : Nat) (fns1 fns2 : List (Nat × ClosLang.Exp)) (trace : BackendCommon.Tra)
    (bodyResult result : Result (List ClosSem.Value) ClosSem.Value)
    (ih : ∀ (e : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock < s0.clock → ExprMotive [e] env state)
    (fullRun : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (enoughClock : (arg :: args).length - rest.length ≤ s0.clock)
    (bodyRun : ClosSem.evaluate [body] bodyEnv
      (ClosSem.decClock ((arg :: args).length - rest.length) s0) = (bodyResult, middle))
    (run : ClosSem.evaluateApp loco f (arg :: args) s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (invariant : codeInv (some g) allowed s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle)
    (stateWell : stateValuesWellFormed g allowed t0.code s0)
    (group : recClosureRel g allowed t0.code loc fns1 fns2)
    (groupWell : recClosureWellFormed loc fns1) (initialWell : wellFormed g0)
    (freshCode : ∀ label, ¬ (label ∈ Set.image Nat.succ {k | k ∈ codeLocations (fns1.map Prod.snd)} ∧
      label ∈ g0.2.map Prod.fst))
    (freshSlots : ∀ label, ¬ (label ∈ (List.range fns1.length).map (fun i => 2 * i + loc + 1) ∧
      label ∈ g0.2.map Prod.fst))
    (groupRun : calls (fns1.map Prod.snd) (insertEachSource loc fns1.length g0) = (es, gEnd))
    (targetGroup : fns2 = callsListSource trace start loc fns1)
    (guard : List.Forall₂ (fun fn converted => ∀ v, DbVars.hasVar v (free [converted]).2 = true → v < fn.1)
      fns1 es)
    (growth : stateExtends (codeListSource loc ((fns1.map Prod.fst).zip es) gEnd) g)
    (locationsAllowed : Set.Subset (Set.diff {x | x ∈ codeLocations (fns1.map Prod.snd)} (sptDomain gEnd.1)) allowed)
    (included : codeIncludes (codeListSource loc ((fns1.map Prod.fst).zip es) gEnd).2 t0.code)
    (bound : i < fns1.length) (selected : holEl i fns1 = (n, body))
    (envWell : ∀ v ∈ bodyEnv, valueWellFormed g allowed t0.code v)
    (envRelated : let m := if isRecClosure f' then fns2.length else 0
      n + m ≤ bodyEnv.length ∧ n + m ≤ targetEnv.length ∧
      List.Forall₂ (valueRel g allowed t0.code) (bodyEnv.take (n + m)) (targetEnv.take (n + m)) ∧
      envRel (valueRel g allowed t0.code) (bodyEnv.drop (n + m)) (targetEnv.drop (n + m)) m [holEl i fns2])
    (disjoint : Disjoint allowed (sptDomain g.1)) (well : wellFormed g)
    (states : stateRel g allowed s0 t0) :
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 middle.code middle.compile middle.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code middle ∧
      stateExtends g g2 ∧ wellFormed g2 ∧ allowed ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) bodyResult ∧
      ClosSem.evaluate [holEl i es] (targetEnv.take n)
        {ClosSem.decClock ((arg :: args).length - rest.length) t0 with
          clock := (ClosSem.decClock ((arg :: args).length - rest.length) t0).clock + ck} = (res', t) ∧
      stateRel g2 l2 middle t ∧
      resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) bodyResult res' := by
  have bodySafe := fullCallBodySafe loco f arg args bodyEnv rest body s0 middle last bodyResult result
    fullRun enoughClock bodyRun run safe
  have remaining := ClosSem.destClosure_full_remaining_lt s0.maxApp loco f (arg :: args) bodyEnv rest body fullRun
  have clockLess : (ClosSem.decClock ((arg :: args).length - rest.length) s0).clock < s0.clock := by
    simp only [ClosSem.decClock]
    omega
  obtain ⟨ga, gb, bodyCompile, bodyGrowth, gaWell, bodyFresh, bodyBound, bodyIncluded⟩ :=
    optimizedGroupBodyCall loc fns1 i n body g0 gEnd g allowed t0.code es groupWell initialWell freshCode freshSlots
      groupRun growth locationsAllowed included bound selected
  have sourceSyntax := recursiveBodySyntax loc fns1 i groupWell bound
  have bodyEq : (holEl i fns1).2 = body := congrArg Prod.snd selected
  rw [bodyEq] at sourceSyntax
  have targetRelated := optimizedCallBodyEnvRel g allowed t0.code loc i n start fns1 fns2 es trace f' body
    bodyEnv targetEnv group bound selected targetGroup guard envRelated
  have startStates : stateRel g allowed (ClosSem.decClock ((arg :: args).length - rest.length) s0)
      (ClosSem.decClock ((arg :: args).length - rest.length) t0) := by
    have same := stateRel_withClock g allowed s0 t0
      (s0.clock - ((arg :: args).length - rest.length)) states
    have clockEq := stateRel_clock g allowed s0 t0 states
    simpa only [ClosSem.decClock, ← clockEq] using same
  have freshDisjoint : Disjoint (Set.image Nat.succ {x | x ∈ codeLocations [body]})
      {x | x ∈ ga.2.map Prod.fst} := by
    apply Set.disjoint_left.mpr
    intro key a b
    exact bodyFresh key ⟨a, b⟩
  have result := ih body bodyEnv (ClosSem.decClock ((arg :: args).length - rest.length) s0) clockLess
    ([body], bodyEnv, ClosSem.decClock ((arg :: args).length - rest.length) s0)
    ga gb (targetEnv.take n) (ClosSem.decClock ((arg :: args).length - rest.length) t0) [holEl i es]
    bodyResult middle ({x | x ∈ codeLocations [body]} \ sptDomain gb.1) allowed g
    ⟨rfl, bodyRun, bodySafe, bodyCompile, by simpa [ClosSem.decClock] using invariant,
      sourceSyntax.1, sourceSyntax.2.1, by simpa [ClosSem.decClock] using envWell,
      by simpa [ClosSem.decClock, stateValuesWellFormed] using stateWell,
      gaWell, sourceSyntax.2.2, freshDisjoint, rfl, bodyGrowth, bodyBound, disjoint, well,
      by simpa [ClosSem.decClock] using targetRelated, startStates, by simpa [ClosSem.decClock] using bodyIncluded⟩
  exact result
private theorem evaluateFullCallError {C F : Type} (loco : Option Nat) (f arg : ClosSem.Value)
    (args bodyEnv rest : List ClosSem.Value) (body : ClosLang.Exp)
    (s0 middle : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (fullRun : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (enoughClock : (arg :: args).length - rest.length ≤ s0.clock)
    (bodyRun : ClosSem.evaluate [body] bodyEnv
      (ClosSem.decClock ((arg :: args).length - rest.length) s0) = (.err error, middle)) :
    ClosSem.evaluateApp loco f (arg :: args) s0 = (.err error, middle) := by
  have fixed : ClosSem.fixClock (ClosSem.decClock ((arg :: args).length - rest.length) s0)
      ((Result.err error : Result (List ClosSem.Value) ClosSem.Value), middle) =
        ((Result.err error : Result (List ClosSem.Value) ClosSem.Value), middle) := by
    rw [← bodyRun]
    exact ClosSem.fixClock_evaluate_source _ _ _
  rw [ClosSem.evaluateApp]
  split <;> simp_all only [Option.some.injEq, AppKind.fullApp.injEq, reduceCtorEq]
  split
  · omega
  · rfl

private theorem evaluateFullCallValue {C F : Type} (loco : Option Nat) (f arg : ClosSem.Value)
    (args bodyEnv rest : List ClosSem.Value) (body : ClosLang.Exp)
    (s0 middle last : ClosSem.State C F) (value : ClosSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (fullRun : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (enoughClock : (arg :: args).length - rest.length ≤ s0.clock)
    (bodyRun : ClosSem.evaluate [body] bodyEnv
      (ClosSem.decClock ((arg :: args).length - rest.length) s0) = (.val [value], middle))
    (restRun : ClosSem.evaluateApp loco value rest middle = (result, last)) :
    ClosSem.evaluateApp loco f (arg :: args) s0 = (result, last) := by
  have fixed : ClosSem.fixClock (ClosSem.decClock ((arg :: args).length - rest.length) s0)
      ((Result.val [value] : Result (List ClosSem.Value) ClosSem.Value), middle) =
        ((Result.val [value] : Result (List ClosSem.Value) ClosSem.Value), middle) := by
    rw [← bodyRun]
    exact ClosSem.fixClock_evaluate_source _ _ _
  rw [ClosSem.evaluateApp]
  split <;> simp_all only [Option.some.injEq, AppKind.fullApp.injEq, reduceCtorEq]
  split
  · omega
  · rfl
private theorem decClock_add {C F : Type} (state : ClosSem.State C F) (cost extra : Nat)
    (enough : cost ≤ state.clock) :
    ClosSem.decClock cost {state with clock := state.clock + extra} =
      {ClosSem.decClock cost state with clock := (ClosSem.decClock cost state).clock + extra} := by
  simp only [ClosSem.decClock]
  congr 1
  omega
private theorem composeFullCallValue {C F : Type} (loco : Option Nat) (f arg : ClosSem.Value)
    (args bodyEnv rest : List ClosSem.Value) (body : ClosLang.Exp)
    (s0 middle last : ClosSem.State C F) (value : ClosSem.Value) (ck ck2 : Nat)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (fullRun : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (enoughClock : (arg :: args).length - rest.length ≤ s0.clock)
    (bodyRun : ClosSem.evaluate [body] bodyEnv
      {ClosSem.decClock ((arg :: args).length - rest.length) s0 with
        clock := (ClosSem.decClock ((arg :: args).length - rest.length) s0).clock + ck} =
        (.val [value], middle))
    (restRun : ClosSem.evaluateApp loco value rest {middle with clock := middle.clock + ck2} = (result, last)) :
    ClosSem.evaluateApp loco f (arg :: args) {s0 with clock := s0.clock + (ck + ck2)} = (result, last) := by
  let cost := (arg :: args).length - rest.length
  let base := ClosSem.decClock cost s0
  let boosted := {s0 with clock := s0.clock + (ck + ck2)}
  have boostedDest : destClosure boosted.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest) := by
    simpa [boosted] using fullRun
  have boostedEnough : (arg :: args).length - rest.length ≤ boosted.clock := by
    simp only [boosted]
    omega
  have shifted := ClosProps.ClockShiftPort.evaluate_addClock middle
    {base with clock := base.clock + ck} (.val [value]) [body] bodyEnv ⟨bodyRun, by simp⟩ ck2
  have boostedBody : ClosSem.evaluate [body] bodyEnv (ClosSem.decClock cost boosted) =
      (.val [value], {middle with clock := middle.clock + ck2}) := by
    rw [show ClosSem.decClock cost boosted = {base with clock := base.clock + (ck + ck2)} by
      simpa [boosted, base, cost] using decClock_add s0 cost (ck + ck2) enoughClock]
    simpa only [Nat.add_assoc] using shifted
  exact evaluateFullCallValue loco f arg args bodyEnv rest body boosted
    {middle with clock := middle.clock + ck2} last value result boostedDest boostedEnough boostedBody restRun
private theorem applyRemainingAppIH {C F : Type} (loco : Option Nat) (f arg value targetValue : ClosSem.Value)
    (args bodyEnv rest targetRest targetEnv : List ClosSem.Value) (body targetBody : ClosLang.Exp)
    (s0 middle last tailLast : ClosSem.State (NumSet × C) F) (t0 t : ClosSem.State C F)
    (g g2 : State) (allowed allowed2 : Set Nat) (ck : Nat)
    (result tailResult : Result (List ClosSem.Value) ClosSem.Value)
    (ih : ∀ (f : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock < s0.clock → AppMotive loco f args state)
    (fullRun : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (enoughClock : (arg :: args).length - rest.length ≤ s0.clock)
    (bodyRun : ClosSem.evaluate [body] bodyEnv
      (ClosSem.decClock ((arg :: args).length - rest.length) s0) = (.val [value], middle))
    (restRun : ClosSem.evaluateApp loco value rest middle = (tailResult, tailLast))
    (run : ClosSem.evaluateApp loco f (arg :: args) s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (targetBodyRun : ClosSem.evaluate [targetBody] targetEnv
      {ClosSem.decClock ((arg :: args).length - rest.length) t0 with
        clock := (ClosSem.decClock ((arg :: args).length - rest.length) t0).clock + ck} = (.val [targetValue], t))
    (invariant : codeInv (some g2) allowed2 middle.code middle.compile middle.compileOracle t.code t.compile t.compileOracle)
    (stateWell : stateValuesWellFormed g2 allowed2 t.code middle)
    (growth : stateExtends g g2) (allowedGrowth : allowed ⊆ allowed2)
    (well : wellFormed g2) (disjoint : Disjoint allowed2 (sptDomain g2.1))
    (valueWell : valueWellFormed g2 allowed2 t.code value)
    (valueRelated : valueRel g2 allowed2 t.code value targetValue)
    (restWell : ∀ a ∈ rest, valueWellFormed g allowed t0.code a)
    (restRelated : List.Forall₂ (valueRel g allowed t0.code) rest targetRest)
    (states : stateRel g2 allowed2 middle t) :
    ∃ ck2 res' t2 g3 l3,
      codeInv (some g3) l3 tailLast.code tailLast.compile tailLast.compileOracle t2.code t2.compile t2.compileOracle ∧
      stateValuesWellFormed g3 l3 t2.code tailLast ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g3 l3 t2.code v)
        (valueWellFormed g3 l3 t2.code) tailResult ∧
      ClosSem.evaluateApp loco targetValue targetRest {t with clock := t.clock + ck2} = (res', t2) ∧
      stateRel g3 l3 tailLast t2 ∧ stateExtends g2 g3 ∧ wellFormed g3 ∧ allowed2 ⊆ l3 ∧
      Disjoint l3 (sptDomain g3.1) ∧
      resultRel (List.Forall₂ (valueRel g3 l3 t2.code)) (valueRel g3 l3 t2.code) tailResult res' := by
  have sourceRun := evaluateFullCallValue loco f arg args bodyEnv rest body s0 middle tailLast value tailResult
    fullRun enoughClock bodyRun restRun
  have same := run.symm.trans sourceRun
  have tailSafe : tailResult ≠ .err (.abort .typeError) := by
    intro bad
    apply safe
    exact (congrArg Prod.fst same).trans bad
  have remaining := ClosSem.destClosure_full_remaining_lt s0.maxApp loco f (arg :: args) bodyEnv rest body fullRun
  have bodyClock := ClosSem.evaluate_clock_source.1 [body] bodyEnv
    (ClosSem.decClock ((arg :: args).length - rest.length) s0) (.val [value]) middle bodyRun
  have clockLess : middle.clock < s0.clock := by
    simp only [ClosSem.decClock] at bodyClock
    omega
  have codeGrowth : t0.code.submap t.code := by
    have sub := ClosProps.CodeGrowthPort.evaluate_mono [targetBody] targetEnv
      {ClosSem.decClock ((arg :: args).length - rest.length) t0 with
        clock := (ClosSem.decClock ((arg :: args).length - rest.length) t0).clock + ck}
      (.val [targetValue]) t targetBodyRun
    simpa [ClosSem.decClock] using sub
  have restWell' := everyValueWellFormed_subg g allowed t0.code rest t.code g2 allowed2
    ⟨restWell, codeGrowth, growth, allowedGrowth⟩
  have restRelated' := listValueRel_subg g allowed t0.code rest targetRest g2 allowed2 t.code
    ⟨restRelated, growth, allowedGrowth, codeGrowth⟩
  exact ih value rest middle clockLess (L := Unit) () g2 allowed2 t tailResult tailLast targetValue targetRest
    ⟨restRun, tailSafe, invariant, valueWell, restWell', stateWell, well, disjoint,
      valueRelated, restRelated', states⟩
private theorem composeFullCallError {C F : Type} (loco : Option Nat) (f arg : ClosSem.Value)
    (args bodyEnv rest : List ClosSem.Value) (body : ClosLang.Exp)
    (s0 middle : ClosSem.State C F) (error : ErrorResult ClosSem.Value) (ck : Nat)
    (fullRun : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (enoughClock : (arg :: args).length - rest.length ≤ s0.clock)
    (bodyRun : ClosSem.evaluate [body] bodyEnv
      {ClosSem.decClock ((arg :: args).length - rest.length) s0 with
        clock := (ClosSem.decClock ((arg :: args).length - rest.length) s0).clock + ck} =
        (.err error, middle)) :
    ClosSem.evaluateApp loco f (arg :: args) {s0 with clock := s0.clock + ck} = (.err error, middle) := by
  let cost := (arg :: args).length - rest.length
  let boosted := {s0 with clock := s0.clock + ck}
  have boostedDest : destClosure boosted.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest) := by
    simpa [boosted] using fullRun
  have boostedEnough : (arg :: args).length - rest.length ≤ boosted.clock := by
    simp only [boosted]
    omega
  have boostedBody : ClosSem.evaluate [body] bodyEnv (ClosSem.decClock cost boosted) = (.err error, middle) := by
    rw [show ClosSem.decClock cost boosted =
        {ClosSem.decClock cost s0 with clock := (ClosSem.decClock cost s0).clock + ck} by
      simpa [boosted, cost] using decClock_add s0 cost ck enoughClock]
    exact bodyRun
  exact evaluateFullCallError loco f arg args bodyEnv rest body boosted middle error
    boostedDest boostedEnough boostedBody
private theorem finishOrdinaryFullApplication {C F : Type} (loco : Option Nat)
    (f f' arg targetArg : ClosSem.Value) (args args' bodyEnv targetEnv rest targetRest : List ClosSem.Value)
    (body targetBody : ClosLang.Exp) (s0 middle last : ClosSem.State (NumSet × C) F) (t0 : ClosSem.State C F)
    (g g2 : State) (allowed allowed2 : Set Nat) (ck : Nat) (t : ClosSem.State C F)
    (bodyResult targetBodyResult result : Result (List ClosSem.Value) ClosSem.Value)
    (appIH : ∀ (f : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock < s0.clock → AppMotive loco f args state)
    (sourceDest : destClosure s0.maxApp loco f (arg :: args) = some (.fullApp body bodyEnv rest))
    (targetDest : destClosure t0.maxApp loco f' (targetArg :: args') = some (.fullApp targetBody targetEnv targetRest))
    (enough : (arg :: args).length - rest.length ≤ s0.clock)
    (argsRelated : List.Forall₂ (valueRel g allowed t0.code) (arg :: args) (targetArg :: args'))
    (restRelated : List.Forall₂ (valueRel g allowed t0.code) rest targetRest)
    (restWell : ∀ v ∈ rest, valueWellFormed g allowed t0.code v)
    (sourceRun : ClosSem.evaluateApp loco f (arg :: args) s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (bodyRun : ClosSem.evaluate [body] bodyEnv (ClosSem.decClock ((arg :: args).length - rest.length) s0) =
      (bodyResult, middle))
    (bodyInvariant : codeInv (some g2) allowed2 middle.code middle.compile middle.compileOracle t.code t.compile t.compileOracle)
    (bodyStateWell : stateValuesWellFormed g2 allowed2 t.code middle)
    (growth : stateExtends g g2) (well2 : wellFormed g2) (allowedGrowth : allowed ⊆ allowed2)
    (disjoint : Disjoint allowed2 (sptDomain g2.1))
    (bodyWell : everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 allowed2 t.code v)
      (valueWellFormed g2 allowed2 t.code) bodyResult)
    (targetBodyRun : ClosSem.evaluate [targetBody] targetEnv
      {ClosSem.decClock ((arg :: args).length - rest.length) t0 with
        clock := (ClosSem.decClock ((arg :: args).length - rest.length) t0).clock + ck} = (targetBodyResult, t))
    (bodyStates : stateRel g2 allowed2 middle t)
    (bodyRelated : resultRel (List.Forall₂ (valueRel g2 allowed2 t.code))
      (valueRel g2 allowed2 t.code) bodyResult targetBodyResult)
    (initialStates : stateRel g allowed s0 t0) :
    ∃ ck' res' t2 g3 l3,
      codeInv (some g3) l3 last.code last.compile last.compileOracle t2.code t2.compile t2.compileOracle ∧
      stateValuesWellFormed g3 l3 t2.code last ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g3 l3 t2.code v)
        (valueWellFormed g3 l3 t2.code) result ∧
      ClosSem.evaluateApp loco f' (targetArg :: args') {t0 with clock := t0.clock + ck'} = (res', t2) ∧
      stateRel g3 l3 last t2 ∧ stateExtends g g3 ∧ wellFormed g3 ∧ allowed ⊆ l3 ∧
      Disjoint l3 (sptDomain g3.1) ∧
      resultRel (List.Forall₂ (valueRel g3 l3 t2.code)) (valueRel g3 l3 t2.code) result res' := by
  have costEq : (arg :: args).length - rest.length = (targetArg :: args').length - targetRest.length := by
    have argsLen := argsRelated.length_eq
    have restLen := restRelated.length_eq
    omega
  have clockEq := stateRel_clock g allowed s0 t0 initialStates
  have targetEnough : (targetArg :: args').length - targetRest.length ≤ t0.clock := by omega
  cases bodyResult with
  | err error =>
    cases targetBodyResult with
    | val values =>
      change False at bodyRelated
      exact bodyRelated.elim
    | err targetError =>
      have sourceEq := sourceRun.symm.trans
        (evaluateFullCallError loco f arg args bodyEnv rest body s0 middle error sourceDest enough bodyRun)
      simp only [Prod.mk.injEq] at sourceEq
      obtain ⟨rfl, rfl⟩ := sourceEq
      have targetRun := composeFullCallError loco f' targetArg args' targetEnv targetRest targetBody t0 t
        targetError ck targetDest targetEnough (by simpa only [← costEq] using targetBodyRun)
      exact ⟨ck, .err targetError, t, g2, allowed2, bodyInvariant, bodyStateWell, bodyWell,
        targetRun, bodyStates, growth, well2, allowedGrowth, disjoint, bodyRelated⟩
  | val values =>
    cases targetBodyResult with
    | err error =>
      change False at bodyRelated
      exact bodyRelated.elim
    | val targetValues =>
      obtain ⟨value, rfl⟩ := ClosProps.evaluateSing body bodyEnv _ middle values bodyRun
      obtain ⟨targetValue, rfl⟩ := ClosProps.evaluateSing targetBody targetEnv _ t targetValues targetBodyRun
      change List.Forall₂ (valueRel g2 allowed2 t.code) [value] [targetValue] at bodyRelated
      cases bodyRelated with
      | cons valueRelated remaining =>
        cases remaining
        change ∀ v ∈ [value], valueWellFormed g2 allowed2 t.code v at bodyWell
        have valueWell := bodyWell value (by simp)
        cases restRun : ClosSem.evaluateApp loco value rest middle with
        | mk tailResult tailLast =>
          have sourceEq := sourceRun.symm.trans
            (evaluateFullCallValue loco f arg args bodyEnv rest body s0 middle tailLast value tailResult
              sourceDest enough bodyRun restRun)
          simp only [Prod.mk.injEq] at sourceEq
          obtain ⟨rfl, rfl⟩ := sourceEq
          obtain ⟨ck2, res', t2, g3, l3, inv3, wf3, resultWell, restTargetRun, states3,
            growth3, well3, allowedGrowth3, disjoint3, related3⟩ :=
            applyRemainingAppIH loco f arg value targetValue args bodyEnv rest targetRest targetEnv body targetBody
              s0 middle last last t0 t g g2 allowed allowed2 ck result result appIH
              sourceDest enough bodyRun restRun sourceRun safe targetBodyRun bodyInvariant bodyStateWell
              growth allowedGrowth well2 disjoint valueWell valueRelated restWell restRelated bodyStates
          have targetRun := composeFullCallValue loco f' targetArg args' targetEnv targetRest targetBody
            t0 t t2 targetValue ck ck2 res' targetDest targetEnough (by simpa only [← costEq] using targetBodyRun)
            restTargetRun
          exact ⟨ck + ck2, res', t2, g3, l3, inv3, wf3, resultWell, targetRun, states3,
            stateExtends_trans g g2 g3 growth growth3, well3, Set.Subset.trans allowedGrowth allowedGrowth3,
            disjoint3, related3⟩
private theorem optimizedBodyRunAsStub {C F : Type} (trace : BackendCommon.Tra)
    (start loc i n cost ck : Nat) (fns : List (Nat × ClosLang.Exp)) (es : List ClosLang.Exp)
    (endState : State) (env : List ClosSem.Value) (state last : ClosSem.State C F)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (lengthEq : es.length = fns.length) (bound : i < fns.length)
    (arity : (holEl i fns).1 = n) (enough : n ≤ env.length)
    (included : codeIncludes (codeListSource loc ((fns.map Prod.fst).zip es) endState).2 state.code)
    (bodyRun : ClosSem.evaluate [holEl i es] (env.take n)
      {ClosSem.decClock cost state with clock := (ClosSem.decClock cost state).clock + ck} = (result, last)) :
    ClosSem.evaluate [(holEl i (callsListSource trace start loc fns)).2] env
      {ClosSem.decClock cost state with clock := (ClosSem.decClock cost state).clock + (ck + 1)} = (result, last) := by
  let startState := {ClosSem.decClock cost state with clock := (ClosSem.decClock cost state).clock + ck}
  have included' : codeIncludes (codeListSource loc ((fns.map Prod.fst).zip es) endState).2 startState.code := by
    simpa [startState, ClosSem.decClock] using included
  have run := evaluateOptimizedGroupBody trace start loc i n fns es endState env startState
    lengthEq bound arity enough included'
  simpa [startState, Nat.add_assoc, bodyRun] using run
private theorem appCase {C F : Type} (loco : Option Nat) (f : ClosSem.Value)
    (args : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (bodyIH : ∀ (e : ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock < s0.clock → ExprMotive [e] env state)
    (appIH : ∀ (f : ClosSem.Value) (args : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock < s0.clock → AppMotive loco f args state) : AppMotive loco f args s0 := by
  cases args with
  | nil => exact appNilMotive loco f s0
  | cons arg args =>
    cases dest : destClosure s0.maxApp loco f (arg :: args) with
    | none =>
      intro L loc g allowed t0 res last f' args' h
      exact (appMissingClosureImpossible arg args loco f s0 last res dest h.1 h.2.1).elim
    | some kind =>
      cases kind with
      | partialApp value => exact appPartialMotive loco f arg args s0 value dest
      | fullApp body bodyEnv rest =>
        by_cases timeout : s0.clock < (arg :: args).length - rest.length
        · exact appFullTimeoutMotive loco f arg args s0 body bodyEnv rest dest timeout
        · have enough : (arg :: args).length - rest.length ≤ s0.clock := by omega
          intro locVar g allowed t0 res last f' args' h
          rcases h with ⟨sourceRun, safe, invariant, functionWell, argsWell, stateWell,
            well, disjoint, functionRelated, argsRelated, states⟩
          obtain ⟨fns1, loc, i, fns2, targetEnv, targetRest, n, targetDest, envRelated,
            restRelated, group, bound, selected, bodyEnvWell, restWell, bodySyntax⟩ :=
            fullCallBodyFacts s0.maxApp loco f f' (arg :: args) bodyEnv rest args' body g allowed t0.code
              dest functionWell argsWell functionRelated argsRelated
          have maxEq := stateRel_maxApp g allowed s0 t0 states
          have targetDest : destClosure t0.maxApp loco f' args' =
              some (.fullApp (holEl i fns2).2 targetEnv targetRest) := by simpa [← maxEq] using targetDest
          cases args' with
          | nil => simp at argsRelated
          | cons targetArg targetArgs =>
            have originalGroup := group
            unfold recClosureRel at group
            obtain ⟨g0, groupWell, initialWell, freshCode, freshSlots, group⟩ := group
            dsimp only at group
            split at group
            · rename_i guard
              cases groupRun : calls (fns1.map Prod.snd) (insertEachSource loc fns1.length g0) with
              | mk es gEnd =>
                simp only [groupRun] at guard group
                obtain ⟨⟨trace, start, targetGroup⟩, growth, locationsAllowed, included⟩ := group
                cases bodyRun : ClosSem.evaluate [body] bodyEnv
                    (ClosSem.decClock ((arg :: args).length - rest.length) s0) with
                | mk bodyResult middle =>
                  obtain ⟨ck, bodyRes, t, g2, l2, bodyInv, bodyStateWell, growth2, well2,
                    allowedGrowth, disjoint2, bodyWell, targetBodyRun, bodyStates, bodyRelated⟩ :=
                    applyOptimizedBodyIH loco f f' arg args bodyEnv rest targetEnv body s0 middle last t0
                      g0 gEnd g allowed es loc i n start fns1 fns2 trace bodyResult res bodyIH dest enough
                      bodyRun sourceRun safe invariant stateWell originalGroup groupWell initialWell freshCode
                      freshSlots groupRun targetGroup guard growth locationsAllowed included bound selected
                      bodyEnvWell envRelated disjoint well states
                  have lengthEq : es.length = fns1.length := by
                    simpa using calls_length (fns1.map Prod.snd) (insertEachSource loc fns1.length g0) es gEnd groupRun
                  have arity : (holEl i fns1).1 = n := congrArg Prod.fst selected
                  have targetEnough : n ≤ targetEnv.length := by
                    dsimp only at envRelated
                    omega
                  have stubRun := optimizedBodyRunAsStub trace start loc i n
                    ((arg :: args).length - rest.length) ck fns1 es gEnd targetEnv t0 t bodyRes
                    lengthEq bound arity targetEnough included targetBodyRun
                  have actualBodyRun : ClosSem.evaluate [(holEl i fns2).2] targetEnv
                      {ClosSem.decClock ((arg :: args).length - rest.length) t0 with
                        clock := (ClosSem.decClock ((arg :: args).length - rest.length) t0).clock + (ck + 1)} =
                      (bodyRes, t) := by simpa only [targetGroup] using stubRun
                  exact finishOrdinaryFullApplication loco f f' arg targetArg args targetArgs bodyEnv targetEnv
                    rest targetRest body (holEl i fns2).2 s0 middle last t0 g g2 allowed l2 (ck + 1) t
                    bodyResult bodyRes res appIH dest targetDest enough argsRelated restRelated restWell sourceRun
                    safe bodyRun bodyInv bodyStateWell growth2 well2 allowedGrowth disjoint2 bodyWell actualBodyRun
                    bodyStates bodyRelated states
            · rename_i guard
              cases groupRun : calls (fns1.map Prod.snd) g0 with
              | mk es gEnd =>
                simp only [groupRun] at group
                obtain ⟨targetGroup, growth, locationsAllowed, _, included⟩ := group
                cases bodyRun : ClosSem.evaluate [body] bodyEnv
                    (ClosSem.decClock ((arg :: args).length - rest.length) s0) with
                | mk bodyResult middle =>
                  obtain ⟨ck, bodyRes, t, g2, l2, bodyInv, bodyStateWell, growth2, well2,
                    allowedGrowth, disjoint2, bodyWell, targetBodyRun, bodyStates, bodyRelated⟩ :=
                    applyOrdinaryBodyIH loco f f' arg args bodyEnv rest targetEnv body s0 middle last t0
                      g0 gEnd g allowed es loc i n fns1 fns2 bodyResult res bodyIH dest enough bodyRun
                      sourceRun safe invariant stateWell originalGroup groupWell initialWell freshCode groupRun
                      targetGroup growth locationsAllowed included bound selected bodyEnvWell envRelated disjoint well states
                  exact finishOrdinaryFullApplication loco f f' arg targetArg args targetArgs bodyEnv targetEnv
                    rest targetRest body (holEl i fns2).2 s0 middle last t0 g g2 allowed l2 ck t
                    bodyResult bodyRes res appIH dest targetDest enough argsRelated restRelated restWell sourceRun
                    safe bodyRun bodyInv bodyStateWell growth2 well2 allowedGrowth disjoint2 bodyWell targetBodyRun
                    bodyStates bodyRelated states
private theorem varCase {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F) :
    ExprMotive [.var trace index] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, _, _, envWell, wellState,
    _, _, _, _, _, _, disjoint, well, envRelated, states, _⟩
  simp only [calls, callsSingList, callsSing, Prod.mk.injEq] at compileRun
  rcases compileRun with ⟨rfl, rfl⟩
  cases found : env1[index]? with
  | none =>
    simp [ClosSem.evaluate, found, ClosSem.typeError] at sourceRun
    obtain ⟨rfl, rfl⟩ := sourceRun
    exact (safe rfl).elim
  | some value =>
    simp only [ClosSem.evaluate, found, Prod.mk.injEq] at sourceRun
    obtain ⟨rfl, rfl⟩ := sourceRun
    obtain ⟨leftBound, leftValue⟩ := List.getElem?_eq_some_iff.mp found
    have related : ∃ (rightBound : index < env2.length),
        valueRel g1 l1 t0.code value env2[index] := by
      unfold envRel at envRelated
      split at envRelated
      · rename_i same
        have rightBound : index < env2.length := by omega
        have rel := envRelated.get leftBound rightBound
        change valueRel g1 l1 t0.code env1[index] env2[index] at rel
        exact ⟨rightBound, by simpa only [leftValue] using rel⟩
      · have used : ∃ fn ∈ ([(0, ClosLang.Exp.var trace index)] : List (Nat × ClosLang.Exp)),
            freeVar (fn.1 + 0 + index) fn.2 := by
          simp [freeVar, freeVars, freeVarExp]
        obtain ⟨_, rightBound, rel⟩ := envRelated index (by simpa using used)
        exact ⟨rightBound, by simpa only [leftValue] using rel⟩
    obtain ⟨rightBound, related⟩ := related
    refine ⟨0, .val [env2[index]], t0, g1, l1, invariant, wellState,
      stateExtends_refl g1 well.2, well, Set.Subset.rfl, disjoint, ?_, ?_, states, ?_⟩
    · simpa [everyResult] using envWell value (by rw [← leftValue]; exact List.getElem_mem leftBound)
    · simp [ClosSem.evaluate, List.getElem?_eq_getElem rightBound]
    · exact .cons related .nil
private theorem raiseCase {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (ih : ExprMotive [body] env1 s0) : ExprMotive [.raise trace body] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, wellState,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases bodyCompile : calls [body] g0 with
  | mk output next =>
    have single := calls_sing body g0 output next bodyCompile
    obtain ⟨out, rfl⟩ := single
    have sing : callsSing body g0 = (out, next) := by
      have eq := bodyCompile
      simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
      exact Prod.ext eq.1 eq.2
    simp only [calls, callsSingList, callsSing, sing, Prod.mk.injEq] at compileRun
    obtain ⟨rfl, rfl⟩ := compileRun
    cases childRun : ClosSem.evaluate [body] env1 s0 with
    | mk childResult middle =>
      have childSafe : childResult ≠ .err (.abort .typeError) := by
        intro bad
        subst childResult
        simp [ClosSem.evaluate, childRun] at sourceRun
        obtain ⟨rfl, rfl⟩ := sourceRun
        exact safe rfl
      have childEnv : envRel (valueRel g1 l1 t0.code) env1 env2 0 [(0, out)] := by
        unfold envRel at envRelated ⊢
        split <;> simp_all [freeVar, freeVars, freeVarExp]
      have childInv := ih ([body], env1, s0) g0 next env2 t0 [out] childResult middle l l1 g1
        ⟨rfl, childRun, childSafe, bodyCompile, invariant,
          by simpa [everyFnLocationSome, fnLocationSomeExp] using annotations,
          by simpa [everyFnVarsNone, fnVarsNoneExp] using varsNone,
          envWell, wellState, initialWell, by simpa [codeLocations, codeLocationsExp] using distinct,
          by simpa [codeLocations, codeLocationsExp] using fresh, by simpa [codeLocations, codeLocationsExp] using locations,
          growth, allowed, disjoint, well, by simpa using childEnv, states, included⟩
      obtain ⟨ck, targetResult, t, g2, l2, inv2, stateWell2, growth2, well2,
        allowed2, disjoint2, resultWell, targetRun, states2, resultRelated⟩ := childInv
      cases childResult with
      | err error =>
        cases targetResult with
        | val values => exact False.elim resultRelated
        | err targetError =>
          simp only [ClosSem.evaluate, childRun, Prod.mk.injEq] at sourceRun
          obtain ⟨rfl, rfl⟩ := sourceRun
          refine ⟨ck, .err targetError, t, g2, l2, inv2, stateWell2, growth2, well2,
            allowed2, disjoint2, resultWell, ?_, states2, resultRelated⟩
          simp only [ClosSem.evaluate, targetRun]
      | val values =>
        cases targetResult with
        | err error => exact False.elim resultRelated
        | val targetValues =>
          obtain ⟨value, rfl⟩ := ClosProps.evaluateSing body env1 s0 middle values childRun
          obtain ⟨targetValue, rfl⟩ := ClosProps.evaluateSing out env2 _ t targetValues targetRun
          simp only [ClosSem.evaluate, childRun, Prod.mk.injEq] at sourceRun
          obtain ⟨rfl, rfl⟩ := sourceRun
          change List.Forall₂ (valueRel g2 l2 t.code) [value] [targetValue] at resultRelated
          cases resultRelated with
          | cons related tail =>
            cases tail
            have valueWell : valueWellFormed g2 l2 t.code value := resultWell value (by simp)
            refine ⟨ck, .err (.raise targetValue), t, g2, l2, inv2, stateWell2, growth2, well2,
              allowed2, disjoint2, valueWell, ?_, states2, related⟩
            simp [ClosSem.evaluate, targetRun]
private theorem tickCase {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (ih : ∀ state : ClosSem.State (NumSet × C) F, state.clock < s0.clock → ExprMotive [body] env1 state) :
    ExprMotive [.tick trace body] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, wellState,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases bodyCompile : calls [body] g0 with
  | mk output next =>
    obtain ⟨out, rfl⟩ := calls_sing body g0 output next bodyCompile
    have sing : callsSing body g0 = (out, next) := by
      have eq := bodyCompile
      simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
      exact Prod.ext eq.1 eq.2
    simp only [calls, callsSingList, callsSing, sing, Prod.mk.injEq] at compileRun
    obtain ⟨rfl, rfl⟩ := compileRun
    have clockEq := stateRel_clock g1 l1 s0 t0 states
    by_cases zero : s0.clock = 0
    · have targetZero : t0.clock = 0 := by omega
      simp only [ClosSem.evaluate, zero, if_true] at sourceRun
      obtain ⟨rfl, rfl⟩ := sourceRun
      refine ⟨0, .err (.abort .timeoutError), t0, g1, l1, invariant, wellState,
        stateExtends_refl g1 well.2, well, Set.Subset.rfl, disjoint, ?_, ?_, states, ?_⟩
      · simp [everyResult, everyErrorResult]
      · simp only [Nat.add_zero, ClosSem.evaluate, targetZero, if_true, ClosSem.timeoutError]
        congr 1
        cases t0
        simp_all
      · simp [resultRel, excRel]
    · have childRun : ClosSem.evaluate [body] env1 (ClosSem.decClock 1 s0) = (res, s) := by
        simpa [ClosSem.evaluate, zero] using sourceRun
      have less : (ClosSem.decClock 1 s0).clock < s0.clock := by simp only [ClosSem.decClock]; omega
      have childEnv : envRel (valueRel g1 l1 t0.code) env1 env2 0 [(0, out)] := by
        unfold envRel at envRelated ⊢
        split <;> simp_all [freeVar, freeVars, freeVarExp]
      have decStates : stateRel g1 l1 (ClosSem.decClock 1 s0) (ClosSem.decClock 1 t0) := by
        have same := stateRel_withClock g1 l1 s0 t0 (s0.clock - 1) states
        simpa [ClosSem.decClock, ← clockEq] using same
      have childInv := ih (ClosSem.decClock 1 s0) less ([body], env1, ClosSem.decClock 1 s0)
        g0 next env2 (ClosSem.decClock 1 t0) [out] res s l l1 g1
        ⟨rfl, childRun, safe, bodyCompile, by simpa [ClosSem.decClock] using invariant,
          by simpa [everyFnLocationSome, fnLocationSomeExp] using annotations,
          by simpa [everyFnVarsNone, fnVarsNoneExp] using varsNone,
          by simpa [ClosSem.decClock] using envWell, by simpa [ClosSem.decClock, stateValuesWellFormed] using wellState,
          initialWell, by simpa [codeLocations, codeLocationsExp] using distinct,
          by simpa [codeLocations, codeLocationsExp] using fresh, by simpa [codeLocations, codeLocationsExp] using locations,
          growth, allowed, disjoint, well, by simpa [ClosSem.decClock] using childEnv, decStates,
          by simpa [ClosSem.decClock] using included⟩
      obtain ⟨ck, res', t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
        resultWell, targetRun, states2, related2⟩ := childInv
      refine ⟨ck, res', t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
        resultWell, ?_, states2, related2⟩
      have targetNonzero : t0.clock ≠ 0 := by omega
      simp only [ClosSem.evaluate]
      simp only [show t0.clock + ck ≠ 0 by omega, if_false]
      have shift := decClock_add t0 1 ck (by omega)
      simpa only [shift] using targetRun
private theorem handleBodyEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (trace : BackendCommon.Tra) (body handler : ClosLang.Exp)
    (related : envRel R env1 env2 0 [(0, .handle trace body handler)]) :
    envRel R env1 env2 0 [(0, body)] := by
  unfold envRel at related ⊢
  split <;> simp_all [freeVar, freeVars, freeVarExp]

private theorem handleHandlerEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (value1 : A) (value2 : B) (trace : BackendCommon.Tra) (body handler : ClosLang.Exp)
    (valueRelated : R value1 value2)
    (related : envRel R env1 env2 0 [(0, .handle trace body handler)]) :
    envRel R (value1 :: env1) (value2 :: env2) 0 [(0, handler)] := by
  unfold envRel at related ⊢
  by_cases same : env1.length = env2.length
  · simp only [same, ↓reduceIte] at related
    simp only [List.length_cons, same, ↓reduceIte]
    exact .cons valueRelated related
  · simp only [same, ↓reduceIte] at related
    simp only [List.length_cons, Nat.succ.injEq, same, ↓reduceIte]
    intro x used
    cases x with
    | zero => exact ⟨by simp, by simp, valueRelated⟩
    | succ x =>
      have h : ∃ fn ∈ ([(0, .handle trace body handler)] : List (Nat × ClosLang.Exp)),
          freeVar (fn.1 + 0 + x) fn.2 := by
        simp only [List.mem_singleton, exists_eq_left, freeVar, freeVars, freeVarExp,
          Nat.zero_add, or_false] at used ⊢
        exact Or.inr (by simpa [Nat.add_comm] using used)
      obtain ⟨left, right, rel⟩ := related x h
      exact ⟨by simpa, by simpa, by simpa using rel⟩
private theorem handleCase {C F : Type} (trace : BackendCommon.Tra) (body handler : ClosLang.Exp)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (bodyIH : ExprMotive [body] env1 s0)
    (handlerIH : ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock ≤ s0.clock → ExprMotive [handler] env state) :
    ExprMotive [.handle trace body handler] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, wellState,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases bodyCompile : calls [body] g0 with
  | mk output gm =>
    obtain ⟨out, rfl⟩ := calls_sing body g0 output gm bodyCompile
    have bodySing : callsSing body g0 = (out, gm) := by
      have eq := bodyCompile
      simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
      exact Prod.ext eq.1 eq.2
    cases handlerCompile : calls [handler] gm with
    | mk output2 next =>
      obtain ⟨hout, rfl⟩ := calls_sing handler gm output2 next handlerCompile
      have handlerSing : callsSing handler gm = (hout, next) := by
        have eq := handlerCompile
        simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
        exact Prod.ext eq.1 eq.2
      simp only [calls, callsSingList, callsSing, bodySing, handlerSing, Prod.mk.injEq] at compileRun
      obtain ⟨rfl, rfl⟩ := compileRun
      have seqDistinct : (codeLocations [body, handler]).Nodup := by
        simpa [codeLocations, codeLocationsExp] using distinct
      have seqFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations [body, handler]} ∧
          label ∈ g0.2.map Prod.fst) := by
        intro label ⟨a, b⟩
        apply Set.disjoint_left.mp fresh
        · simpa [codeLocations, codeLocationsExp] using a
        · exact b
      have seqAnnotations : everyFnLocationSome [body, handler] := by
        simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
      have seqVars : everyFnVarsNone [body, handler] := by
        simpa [everyFnVarsNone, fnVarsNoneExp] using varsNone
      have seqBound : Set.Subset (Set.diff {n | n ∈ codeLocations [body, handler]} (sptDomain next.1)) l1 := by
        intro key hkey
        apply allowed
        rw [locations]
        change (key ∈ codeLocations [body, handler] ∧ ¬ sptDomain next.1 key) at hkey
        change (key ∈ codeLocations [.handle trace body handler] ∧ ¬ sptDomain next.1 key)
        exact ⟨by simpa [codeLocations, codeLocationsExp] using hkey.1, hkey.2⟩
      have ⟨middleWell, middleGrowth, tailDistinct, tailFresh, tailAnnotations⟩ :=
        listSplitInvariants body handler [] g0 gm next out [hout] bodyCompile handlerCompile
          seqDistinct seqFresh seqAnnotations initialWell
      obtain ⟨headDistinct, headFresh, headAnnotations, headVars, tailVars⟩ :=
        listHeadSyntax body handler [] g0 seqDistinct seqFresh seqAnnotations seqVars
      have headBound := Set.Subset.trans
        (listHeadLocationBound body handler [] gm next [hout] handlerCompile seqDistinct middleWell) seqBound
      have headGrowth := stateExtends_trans gm next g1 middleGrowth growth
      have headIncluded := codeIncludes_subg gm next t0.code middleGrowth included
      have headEnv := handleBodyEnvRel (valueRel g1 l1 t0.code) env1 env2 trace out hout (by simpa using envRelated)
      have headDisjoint : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [body]})
          {n | n ∈ g0.2.map Prod.fst} := by
        apply Set.disjoint_left.mpr
        intro key a b
        exact headFresh key ⟨a, b⟩
      cases bodyRun : ClosSem.evaluate [body] env1 s0 with
      | mk bodyResult middle =>
        have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
          intro bad
          subst bodyResult
          simp [ClosSem.evaluate, bodyRun] at sourceRun
          obtain ⟨rfl, rfl⟩ := sourceRun
          exact safe rfl
        have bodySim := bodyIH ([body], env1, s0) g0 gm env2 t0 [out] bodyResult middle
          ({n | n ∈ codeLocations [body]} \ sptDomain gm.1) l1 g1
          ⟨rfl, bodyRun, bodySafe, bodyCompile, invariant, headAnnotations, headVars, envWell, wellState,
            initialWell, headDistinct, headDisjoint, rfl, headGrowth, headBound, disjoint, well,
            by simpa using headEnv, states, headIncluded⟩
        obtain ⟨ck, bodyRes, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
          bodyWell, targetRun, states2, bodyRelated⟩ := bodySim
        have fixedSource : ClosSem.fixClock s0 (bodyResult, middle) = (bodyResult, middle) := by
          rw [← bodyRun]
          exact ClosSem.fixClock_evaluate [body] env1 s0
        have fixedTarget : ClosSem.fixClock {t0 with clock := t0.clock + ck} (bodyRes, t) = (bodyRes, t) := by
          rw [← targetRun]
          exact ClosSem.fixClock_evaluate [out] env2 {t0 with clock := t0.clock + ck}
        cases bodyResult with
        | val values =>
          cases bodyRes with
          | err error => exact False.elim bodyRelated
          | val targetValues =>
            simp only [ClosSem.evaluate, bodyRun, fixedSource, Prod.mk.injEq] at sourceRun
            obtain ⟨rfl, rfl⟩ := sourceRun
            refine ⟨ck, .val targetValues, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2,
              disjoint2, bodyWell, ?_, states2, bodyRelated⟩
            simp only [ClosSem.evaluate, targetRun, fixedTarget]
        | err error =>
          cases bodyRes with
          | val values => exact False.elim bodyRelated
          | err targetError =>
            cases error with
            | abort abort =>
              cases targetError with
              | raise value => exact False.elim bodyRelated
              | abort targetAbort =>
                change abort = targetAbort at bodyRelated
                subst targetAbort
                simp only [ClosSem.evaluate, bodyRun, fixedSource, Prod.mk.injEq] at sourceRun
                obtain ⟨rfl, rfl⟩ := sourceRun
                refine ⟨ck, .err (.abort abort), t, g2, l2, inv2, stateWell2, growth2, well2, allowed2,
                  disjoint2, bodyWell, ?_, states2, by simp [resultRel, excRel]⟩
                simp only [ClosSem.evaluate, targetRun, fixedTarget]
            | raise value =>
              cases targetError with
              | abort targetAbort => exact False.elim bodyRelated
              | raise targetValue =>
                change valueRel g2 l2 t.code value targetValue at bodyRelated
                change valueWellFormed g2 l2 t.code value at bodyWell
                have handlerRun : ClosSem.evaluate [handler] (value :: env1) middle = (res, s) := by
                  simpa only [ClosSem.evaluate, bodyRun, fixedSource] using sourceRun
                have middleClock : middle.clock ≤ s0.clock :=
                  ClosSem.evaluate_clock_source.1 [body] env1 s0 (.err (.raise value)) middle bodyRun
                have codeGrowth : t0.code.submap t.code := by
                  simpa using ClosProps.CodeGrowthPort.evaluate_mono [out] env2
                    {t0 with clock := t0.clock + ck} (.err (.raise targetValue)) t targetRun
                have envWell2 := everyValueWellFormed_subg g1 l1 t0.code env1 t.code g2 l2
                  ⟨envWell, codeGrowth, growth2, allowed2⟩
                have handlerEnvWell : ∀ v ∈ value :: env1, valueWellFormed g2 l2 t.code v := by
                  intro v member
                  simp only [List.mem_cons] at member
                  rcases member with rfl | member
                  · exact bodyWell
                  · exact envWell2 v member
                have originalEnv : envRel (valueRel g2 l2 t.code) env1 env2 0
                    [(0, .handle trace out hout)] :=
                  envValueRel_subg g1 l1 t0.code env1 env2 0 _ g2 l2 t.code
                    ⟨by simpa using envRelated, growth2, allowed2, codeGrowth⟩
                have handlerEnv := handleHandlerEnvRel (valueRel g2 l2 t.code) env1 env2
                  value targetValue trace out hout bodyRelated originalEnv
                have handlerGrowth := stateExtends_trans next g1 g2 growth growth2
                have handlerBound : Set.Subset (Set.diff {n | n ∈ codeLocations [handler]} (sptDomain next.1)) l2 := by
                  intro key hkey
                  apply allowed2
                  apply seqBound
                  simp only [Set.diff, Set.mem_ofPred_eq, codeLocations, List.mem_append] at hkey ⊢
                  exact ⟨Or.inr (by simpa [codeLocations] using hkey.1), hkey.2⟩
                have handlerIncluded := codeIncludes_submap next.2 t0.code t.code ⟨included, codeGrowth⟩
                have handlerDisjoint : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [handler]})
                    {n | n ∈ gm.2.map Prod.fst} := by
                  apply Set.disjoint_left.mpr
                  intro key a b
                  exact tailFresh key ⟨a, b⟩
                obtain ⟨ck2, res2, t2, g3, l3, inv3, stateWell3, growth3, well3, allowed3, disjoint3,
                  resultWell3, handlerTargetRun, states3, related3⟩ :=
                  handlerIH (value :: env1) middle middleClock ([handler], value :: env1, middle)
                    gm next (targetValue :: env2) t [hout] res s
                    ({n | n ∈ codeLocations [handler]} \ sptDomain next.1) l2 g2
                    ⟨rfl, handlerRun, safe, handlerCompile, inv2, tailAnnotations, tailVars, handlerEnvWell,
                      stateWell2, middleWell, tailDistinct, handlerDisjoint, rfl, handlerGrowth, handlerBound,
                      disjoint2, well2, by simpa using handlerEnv, states2, handlerIncluded⟩
                have shifted := ClosProps.ClockShiftPort.evaluate_addClock t
                  {t0 with clock := t0.clock + ck} (.err (.raise targetValue)) [out] env2
                  ⟨targetRun, by simp⟩ ck2
                have shiftedRun : ClosSem.evaluate [out] env2
                    {t0 with clock := t0.clock + (ck + ck2)} =
                    (.err (.raise targetValue), {t with clock := t.clock + ck2}) := by
                  simpa only [Nat.add_assoc] using shifted
                have fixedShift := ClosSem.fixClock_evaluate [out] env2 {t0 with clock := t0.clock + (ck + ck2)}
                rw [shiftedRun] at fixedShift
                have wholeTarget : ClosSem.evaluate [.handle trace out hout] env2
                    {t0 with clock := t0.clock + (ck + ck2)} = (res2, t2) := by
                  simpa only [ClosSem.evaluate, shiftedRun, fixedShift] using handlerTargetRun
                exact ⟨ck + ck2, res2, t2, g3, l3, inv3, stateWell3,
                  stateExtends_trans g1 g2 g3 growth2 growth3, well3, Set.Subset.trans allowed2 allowed3,
                  disjoint3, resultWell3, wholeTarget, states3, related3⟩
private theorem ifEnvironmentRelations {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (trace : BackendCommon.Tra) (cond yes no : ClosLang.Exp)
    (related : envRel R env1 env2 0 [(0, .ifThenElse trace cond yes no)]) :
    envRel R env1 env2 0 [(0, cond)] ∧ envRel R env1 env2 0 [(0, yes)] ∧
      envRel R env1 env2 0 [(0, no)] := by
  unfold envRel at related ⊢
  split <;> simp_all [freeVar, freeVars, freeVarExp]
private theorem ifCase {C F : Type} (trace : BackendCommon.Tra) (cond yes no : ClosLang.Exp)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (condIH : ExprMotive [cond] env1 s0)
    (branchIH : ∀ (branch : ClosLang.Exp) (state : ClosSem.State (NumSet × C) F),
      (branch = yes ∨ branch = no) → state.clock ≤ s0.clock → ExprMotive [branch] env1 state) :
    ExprMotive [.ifThenElse trace cond yes no] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, wellState,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases condCompile : calls [cond] g0 with
  | mk output gc =>
    obtain ⟨cout, rfl⟩ := calls_sing cond g0 output gc condCompile
    have condSing : callsSing cond g0 = (cout, gc) := by
      have eq := condCompile
      simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
      exact Prod.ext eq.1 eq.2
    cases yesCompile : calls [yes] gc with
    | mk output2 gy =>
      obtain ⟨yout, rfl⟩ := calls_sing yes gc output2 gy yesCompile
      have yesSing : callsSing yes gc = (yout, gy) := by
        have eq := yesCompile
        simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
        exact Prod.ext eq.1 eq.2
      cases noCompile : calls [no] gy with
      | mk output3 next =>
        obtain ⟨nout, rfl⟩ := calls_sing no gy output3 next noCompile
        have noSing : callsSing no gy = (nout, next) := by
          have eq := noCompile
          simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
          exact Prod.ext eq.1 eq.2
        have tailCompile : calls [yes, no] gc = ([yout, nout], next) := by
          simp [calls, callsSingList, yesSing, noSing]
        simp only [calls, callsSingList, callsSing, condSing, yesSing, noSing, Prod.mk.injEq] at compileRun
        obtain ⟨rfl, rfl⟩ := compileRun
        have seqDistinct : (codeLocations [cond, yes, no]).Nodup := by
          simpa [codeLocations, codeLocationsExp] using distinct
        have seqFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations [cond, yes, no]} ∧
            label ∈ g0.2.map Prod.fst) := by
          intro label ⟨a, b⟩
          apply Set.disjoint_left.mp fresh
          · simpa [codeLocations, codeLocationsExp] using a
          · exact b
        have seqAnnotations : everyFnLocationSome [cond, yes, no] := by
          simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
        have seqVars : everyFnVarsNone [cond, yes, no] := by
          simpa [everyFnVarsNone, fnVarsNoneExp] using varsNone
        have seqBound : Set.Subset (Set.diff {n | n ∈ codeLocations [cond, yes, no]} (sptDomain next.1)) l1 := by
          intro key hkey
          apply allowed
          rw [locations]
          change (key ∈ codeLocations [cond, yes, no] ∧ ¬ sptDomain next.1 key) at hkey
          change (key ∈ codeLocations [.ifThenElse trace cond yes no] ∧ ¬ sptDomain next.1 key)
          exact ⟨by simpa [codeLocations, codeLocationsExp] using hkey.1, hkey.2⟩
        have ⟨condWell, tailGrowth, tailDistinct, tailFresh, tailAnnotations⟩ :=
          listSplitInvariants cond yes [no] g0 gc next cout [yout, nout] condCompile tailCompile
            seqDistinct seqFresh seqAnnotations initialWell
        obtain ⟨condDistinct, condFresh, condAnnotations, condVars, tailVars⟩ :=
          listHeadSyntax cond yes [no] g0 seqDistinct seqFresh seqAnnotations seqVars
        have condBound := Set.Subset.trans
          (listHeadLocationBound cond yes [no] gc next [yout, nout] tailCompile seqDistinct condWell) seqBound
        have condGrowth := stateExtends_trans gc next g1 tailGrowth growth
        have condIncluded := codeIncludes_subg gc next t0.code tailGrowth included
        have envParts := ifEnvironmentRelations (valueRel g1 l1 t0.code) env1 env2 trace cout yout nout
          (by simpa using envRelated)
        have condDisjoint : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [cond]})
            {n | n ∈ g0.2.map Prod.fst} := by
          apply Set.disjoint_left.mpr
          intro key a b
          exact condFresh key ⟨a, b⟩
        cases condRun : ClosSem.evaluate [cond] env1 s0 with
        | mk condResult middle =>
          have condSafe : condResult ≠ .err (.abort .typeError) := by
            intro bad
            subst condResult
            simp [ClosSem.evaluate, condRun] at sourceRun
            obtain ⟨rfl, rfl⟩ := sourceRun
            exact safe rfl
          have condSim := condIH ([cond], env1, s0) g0 gc env2 t0 [cout] condResult middle
            ({n | n ∈ codeLocations [cond]} \ sptDomain gc.1) l1 g1
            ⟨rfl, condRun, condSafe, condCompile, invariant, condAnnotations, condVars, envWell, wellState,
              initialWell, condDistinct, condDisjoint, rfl, condGrowth, condBound, disjoint, well,
              by simpa using envParts.1, states, condIncluded⟩
          obtain ⟨ck, condRes, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
            condWellResult, targetRun, states2, condRelated⟩ := condSim
          have fixedSource : ClosSem.fixClock s0 (condResult, middle) = (condResult, middle) := by
            rw [← condRun]
            exact ClosSem.fixClock_evaluate [cond] env1 s0
          have fixedTarget : ClosSem.fixClock {t0 with clock := t0.clock + ck} (condRes, t) = (condRes, t) := by
            rw [← targetRun]
            exact ClosSem.fixClock_evaluate [cout] env2 {t0 with clock := t0.clock + ck}
          cases condResult with
          | err error =>
            cases condRes with
            | val values => exact False.elim condRelated
            | err targetError =>
              simp only [ClosSem.evaluate, condRun, fixedSource, Prod.mk.injEq] at sourceRun
              obtain ⟨rfl, rfl⟩ := sourceRun
              refine ⟨ck, .err targetError, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2,
                disjoint2, condWellResult, ?_, states2, condRelated⟩
              simp only [ClosSem.evaluate, targetRun, fixedTarget]
          | val values =>
            cases condRes with
            | err error => exact False.elim condRelated
            | val targetValues =>
              obtain ⟨value, rfl⟩ := ClosProps.evaluateSing cond env1 s0 middle values condRun
              obtain ⟨targetValue, rfl⟩ := ClosProps.evaluateSing cout env2 _ t targetValues targetRun
              change List.Forall₂ (valueRel g2 l2 t.code) [value] [targetValue] at condRelated
              cases condRelated with
              | cons valueRelated tail =>
                cases tail
                have boolEq := ClosProps.PrimitiveBoolean.simpleValRel_asBool (valueRel g2 l2 t.code)
                  (valueRel_simple g2 l2 t.code) value targetValue valueRelated
                cases decision : ClosSem.asBool value with
                | none =>
                  simp [ClosSem.evaluate, condRun, fixedSource, decision, ClosSem.typeError] at sourceRun
                  obtain ⟨rfl, rfl⟩ := sourceRun
                  exact (safe rfl).elim
                | some b =>
                  have targetDecision : ClosSem.asBool targetValue = some b := by simpa [decision] using boolEq.symm
                  have branchRun : ClosSem.evaluate [if b then yes else no] env1 middle = (res, s) := by
                    cases b <;> simpa [ClosSem.evaluate, condRun, fixedSource, decision] using sourceRun
                  have middleClock : middle.clock ≤ s0.clock :=
                    ClosSem.evaluate_clock_source.1 [cond] env1 s0 (.val [value]) middle condRun
                  have codeGrowth : t0.code.submap t.code := by
                    simpa using ClosProps.CodeGrowthPort.evaluate_mono [cout] env2
                      {t0 with clock := t0.clock + ck} (.val [targetValue]) t targetRun
                  have envWell2 := everyValueWellFormed_subg g1 l1 t0.code env1 t.code g2 l2
                    ⟨envWell, codeGrowth, growth2, allowed2⟩
                  have originalEnv : envRel (valueRel g2 l2 t.code) env1 env2 0
                      [(0, .ifThenElse trace cout yout nout)] :=
                    envValueRel_subg g1 l1 t0.code env1 env2 0 _ g2 l2 t.code
                      ⟨by simpa using envRelated, growth2, allowed2, codeGrowth⟩
                  have envParts2 := ifEnvironmentRelations (valueRel g2 l2 t.code) env1 env2 trace cout yout nout originalEnv
                  have finalGrowth := stateExtends_trans next g1 g2 growth growth2
                  have finalIncluded := codeIncludes_submap next.2 t0.code t.code ⟨included, codeGrowth⟩
                  have ⟨yesWell, noGrowth, noDistinct, noFresh, noAnnotations⟩ :=
                    listSplitInvariants yes no [] gc gy next yout [nout] yesCompile noCompile
                      tailDistinct tailFresh tailAnnotations condWell
                  obtain ⟨yesDistinct, yesFresh, yesAnnotations, yesVars, noVars⟩ :=
                    listHeadSyntax yes no [] gc tailDistinct tailFresh tailAnnotations tailVars
                  have branchFacts : ∃ start finish : State,
                      calls [if b then yes else no] start = ([if b then yout else nout], finish) ∧
                      wellFormed start ∧ (codeLocations [if b then yes else no]).Nodup ∧
                      Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [if b then yes else no]})
                        {n | n ∈ start.2.map Prod.fst} ∧
                      everyFnLocationSome [if b then yes else no] ∧ everyFnVarsNone [if b then yes else no] ∧
                      stateExtends finish g2 ∧
                      Set.Subset (Set.diff {n | n ∈ codeLocations [if b then yes else no]} (sptDomain finish.1)) l2 ∧
                      codeIncludes finish.2 t.code := by
                    cases b with
                    | false =>
                      have d : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [no]})
                          {n | n ∈ gy.2.map Prod.fst} := by
                        apply Set.disjoint_left.mpr
                        intro key a c
                        exact noFresh key ⟨a, c⟩
                      refine ⟨gy, next, noCompile, yesWell, noDistinct, d, noAnnotations, noVars,
                        finalGrowth, ?_, finalIncluded⟩
                      intro key hkey
                      apply allowed2
                      apply seqBound
                      simp only [Set.diff, Set.mem_ofPred_eq, codeLocations, List.mem_append] at hkey ⊢
                      exact ⟨Or.inr (Or.inr (by simpa [codeLocations] using hkey.1)), hkey.2⟩
                    | true =>
                      have d : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [yes]})
                          {n | n ∈ gc.2.map Prod.fst} := by
                        apply Set.disjoint_left.mpr
                        intro key a c
                        exact yesFresh key ⟨a, c⟩
                      have yesBound := listHeadLocationBound yes no [] gy next [nout] noCompile tailDistinct yesWell
                      refine ⟨gc, gy, yesCompile, condWell, yesDistinct, d, yesAnnotations, yesVars,
                        stateExtends_trans gy next g2 noGrowth finalGrowth, ?_,
                        codeIncludes_subg gy next t.code noGrowth finalIncluded⟩
                      intro key hkey
                      have tailKey := yesBound hkey
                      apply allowed2
                      apply seqBound
                      simp only [Set.diff, Set.mem_ofPred_eq, codeLocations, List.mem_append] at tailKey ⊢
                      exact ⟨Or.inr tailKey.1, tailKey.2⟩
                  obtain ⟨gb, gf, branchCompile, gbWell, branchDistinct, branchFresh, branchAnnotations,
                    branchVars, branchGrowth, branchBound, branchIncluded⟩ := branchFacts
                  have branchEnv : envRel (valueRel g2 l2 t.code) env1 env2 0
                      [(0, if b then yout else nout)] := by
                    cases b with
                    | false => simpa using envParts2.2.2
                    | true => simpa using envParts2.2.1
                  have branchMember : (if b then yes else no) = yes ∨ (if b then yes else no) = no := by
                    cases b <;> simp
                  obtain ⟨ck2, res2, t2, g3, l3, inv3, stateWell3, growth3, well3, allowed3, disjoint3,
                    resultWell3, branchTargetRun, states3, related3⟩ :=
                    branchIH (if b then yes else no) middle branchMember middleClock
                      ([if b then yes else no], env1, middle) gb gf env2 t [if b then yout else nout] res s
                      ({n | n ∈ codeLocations [if b then yes else no]} \ sptDomain gf.1) l2 g2
                      ⟨rfl, branchRun, safe, branchCompile, inv2, branchAnnotations, branchVars, envWell2,
                        stateWell2, gbWell, branchDistinct, branchFresh, rfl, branchGrowth, branchBound, disjoint2,
                        well2, by simpa using branchEnv, states2, branchIncluded⟩
                  have shifted := ClosProps.ClockShiftPort.evaluate_addClock t
                    {t0 with clock := t0.clock + ck} (.val [targetValue]) [cout] env2
                    ⟨targetRun, by simp⟩ ck2
                  have shiftedRun : ClosSem.evaluate [cout] env2
                      {t0 with clock := t0.clock + (ck + ck2)} =
                      (.val [targetValue], {t with clock := t.clock + ck2}) := by
                    simpa only [Nat.add_assoc] using shifted
                  have fixedShift := ClosSem.fixClock_evaluate [cout] env2 {t0 with clock := t0.clock + (ck + ck2)}
                  rw [shiftedRun] at fixedShift
                  have wholeTarget : ClosSem.evaluate [.ifThenElse trace cout yout nout] env2
                      {t0 with clock := t0.clock + (ck + ck2)} = (res2, t2) := by
                    cases b <;> simpa [ClosSem.evaluate, shiftedRun, fixedShift, targetDecision] using branchTargetRun
                  exact ⟨ck + ck2, res2, t2, g3, l3, inv3, stateWell3,
                    stateExtends_trans g1 g2 g3 growth2 growth3, well3, Set.Subset.trans allowed2 allowed3,
                    disjoint3, resultWell3, wholeTarget, states3, related3⟩
private theorem letBindingsEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (related : envRel R env1 env2 0 [(0, .let trace bindings body)]) :
    envRel R env1 env2 0 (bindings.map (fun e => (0, e))) := by
  have existsFree : ∀ n xs, freeVars n xs ↔ ∃ e ∈ xs, freeVarExp n e := by
    intro n xs
    induction xs with
    | nil => simp [freeVars]
    | cons e es ih => simp [freeVars, ih]
  unfold envRel at related ⊢
  by_cases same : env1.length = env2.length
  · simpa only [same, ↓reduceIte] using related
  · simp only [same, ↓reduceIte] at related ⊢
    simp only [freeVar, freeVars, freeVarExp, Nat.zero_add, List.mem_singleton,
      exists_eq_left, List.mem_map, exists_exists_and_eq_and, or_false] at related ⊢
    simp only [existsFree] at related
    intro x used
    exact related x (Or.inl used)

private theorem letBodyEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (values1 : List A) (values2 : List B) (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp)
    (body : ClosLang.Exp) (len : values1.length = bindings.length)
    (preRel : List.Forall₂ R values1 values2)
    (related : envRel R env1 env2 0 [(0, .let trace bindings body)]) :
    envRel R (values1 ++ env1) (values2 ++ env2) 0 [(0, body)] := by
  have same := preRel.length_eq
  have shifted : envRel R env1 env2 values1.length [(0, body)] := by
    unfold envRel at related ⊢
    by_cases eq : env1.length = env2.length
    · simpa only [eq, ↓reduceIte] using related
    · simp only [eq, ↓reduceIte] at related ⊢
      simp only [freeVar, freeVars, freeVarExp, Nat.zero_add, List.mem_singleton,
        exists_eq_left, or_false] at related ⊢
      intro x used
      apply related x
      exact Or.inr (by simpa [len, Nat.add_comm] using used)
  apply envRel_drop R values1.length (values1 ++ env1) (values2 ++ env2) [(0, body)]
  refine ⟨?_, ?_, by simp, by simp [same]⟩
  · simpa [same] using shifted
  · simpa [same] using preRel
private theorem sequentialCompilationFacts (xs ys : List ClosLang.Exp) (g0 gm g : State)
    (outx outy : List ClosLang.Exp) (allowed : Set Nat)
    (firstRun : calls xs g0 = (outx, gm)) (secondRun : calls ys gm = (outy, g))
    (distinct : (codeLocations xs ++ codeLocations ys).Nodup)
    (fresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations xs ++ codeLocations ys} ∧
      label ∈ g0.2.map Prod.fst))
    (annotations : everyFnLocationSome xs) (well : wellFormed g0)
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations xs ++ codeLocations ys} (sptDomain g.1)) allowed) :
    wellFormed gm ∧ stateExtends gm g ∧ (codeLocations xs).Nodup ∧ (codeLocations ys).Nodup ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations xs} ∧ label ∈ g0.2.map Prod.fst)) ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations ys} ∧ label ∈ gm.2.map Prod.fst)) ∧
      Set.Subset (Set.diff {n | n ∈ codeLocations xs} (sptDomain gm.1)) allowed ∧
      Set.Subset (Set.diff {n | n ∈ codeLocations ys} (sptDomain g.1)) allowed := by
  obtain ⟨firstDistinct, secondDistinct, apart⟩ := List.nodup_append.mp distinct
  have firstFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations xs} ∧
      label ∈ g0.2.map Prod.fst) := by
    intro label ⟨⟨n, hn, eq⟩, old⟩
    exact fresh label ⟨⟨n, List.mem_append_left _ hn, eq⟩, old⟩
  have middleWell := calls_wellFormed xs g0 outx gm ⟨firstRun, firstDistinct, firstFresh, annotations, well⟩
  have origin := calls_addSucc_codeLocations xs g0 outx gm firstRun
  have secondFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations ys} ∧
      label ∈ gm.2.map Prod.fst) := by
    intro label ⟨⟨n, hn, eq⟩, present⟩
    rcases origin present with old | ⟨m, hm, eq'⟩
    · exact fresh label ⟨⟨n, List.mem_append_right _ hn, eq⟩, old⟩
    · exact apart m hm n hn (Nat.succ.inj (eq'.trans eq.symm))
  have growth := calls_subg ys gm outy g ⟨secondRun, middleWell.2, secondDistinct, secondFresh⟩
  refine ⟨middleWell, growth, firstDistinct, secondDistinct, firstFresh, secondFresh, ?_, ?_⟩
  · intro key ⟨member, absent⟩
    apply bound
    exact ⟨List.mem_append_left _ member,
      calls_preservesFreshLocation xs ys gm outy g key distinct secondRun middleWell member absent⟩
  · intro key ⟨member, absent⟩
    exact bound ⟨List.mem_append_right _ member, absent⟩
private theorem letCase {C F : Type} (trace : BackendCommon.Tra) (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (bindingsIH : ExprMotive bindings env1 s0)
    (bodyIH : ∀ (env : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock ≤ s0.clock → ExprMotive [body] env state) :
    ExprMotive [.let trace bindings body] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, wellState,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases bindingsCompile : calls bindings g0 with
  | mk bout gm =>
    have bindingsSing : callsSingList bindings g0 = (bout, gm) := bindingsCompile
    cases bodyCompile : calls [body] gm with
    | mk output next =>
      obtain ⟨out, rfl⟩ := calls_sing body gm output next bodyCompile
      have bodySing : callsSing body gm = (out, next) := by
        have eq := bodyCompile
        simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
        exact Prod.ext eq.1 eq.2
      simp only [calls, callsSingList, callsSing, bindingsSing, bodySing, Prod.mk.injEq] at compileRun
      obtain ⟨rfl, rfl⟩ := compileRun
      have seqDistinct : (codeLocations bindings ++ codeLocations [body]).Nodup := by
        simpa [codeLocations, codeLocationsExp] using distinct
      have seqFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ
          {n | n ∈ codeLocations bindings ++ codeLocations [body]} ∧ label ∈ g0.2.map Prod.fst) := by
        intro label ⟨a, b⟩
        apply Set.disjoint_left.mp fresh
        · simpa [codeLocations, codeLocationsExp] using a
        · exact b
      have annotationParts : fnLocationSomeExp body ∧ everyFnLocationSome bindings := by
        simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
      have varsParts : fnVarsNoneExp body ∧ everyFnVarsNone bindings := by
        simpa [everyFnVarsNone, fnVarsNoneExp] using varsNone
      have bindsAnnotations : everyFnLocationSome bindings := annotationParts.2
      have bodyAnnotations : everyFnLocationSome [body] := by simpa [everyFnLocationSome] using annotationParts.1
      have bindsVars : everyFnVarsNone bindings := varsParts.2
      have bodyVars : everyFnVarsNone [body] := by simpa [everyFnVarsNone] using varsParts.1
      have seqBound : Set.Subset (Set.diff {n | n ∈ codeLocations bindings ++ codeLocations [body]} (sptDomain next.1)) l1 := by
        intro key hkey
        apply allowed
        rw [locations]
        change (key ∈ codeLocations bindings ++ codeLocations [body] ∧ ¬ sptDomain next.1 key) at hkey
        change (key ∈ codeLocations [.let trace bindings body] ∧ ¬ sptDomain next.1 key)
        exact ⟨by simpa [codeLocations, codeLocationsExp] using hkey.1, hkey.2⟩
      obtain ⟨middleWell, middleGrowth, bindsDistinct, bodyDistinct, bindsFresh, bodyFresh, bindsBound, bodyBound⟩ :=
        sequentialCompilationFacts bindings [body] g0 gm next bout [out] l1 bindingsCompile bodyCompile
          seqDistinct seqFresh bindsAnnotations initialWell seqBound
      have bindsGrowth := stateExtends_trans gm next g1 middleGrowth growth
      have bindsIncluded := codeIncludes_subg gm next t0.code middleGrowth included
      have bindsEnv := letBindingsEnvRel (valueRel g1 l1 t0.code) env1 env2 trace bout out (by simpa using envRelated)
      have bindsDisjoint : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations bindings})
          {n | n ∈ g0.2.map Prod.fst} := by
        apply Set.disjoint_left.mpr
        intro key a b
        exact bindsFresh key ⟨a, b⟩
      cases bindingsRun : ClosSem.evaluate bindings env1 s0 with
      | mk bindsResult middle =>
        have bindsSafe : bindsResult ≠ .err (.abort .typeError) := by
          intro bad
          subst bindsResult
          simp [ClosSem.evaluate, bindingsRun] at sourceRun
          obtain ⟨rfl, rfl⟩ := sourceRun
          exact safe rfl
        have bindsSim := bindingsIH (bindings, env1, s0) g0 gm env2 t0 bout bindsResult middle
          ({n | n ∈ codeLocations bindings} \ sptDomain gm.1) l1 g1
          ⟨rfl, bindingsRun, bindsSafe, bindingsCompile, invariant, bindsAnnotations, bindsVars, envWell, wellState,
            initialWell, bindsDistinct, bindsDisjoint, rfl, bindsGrowth, bindsBound, disjoint, well,
            bindsEnv, states, bindsIncluded⟩
        obtain ⟨ck, targetBinds, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
          bindsWell, targetRun, states2, bindsRelated⟩ := bindsSim
        have fixedSource : ClosSem.fixClock s0 (bindsResult, middle) = (bindsResult, middle) := by
          rw [← bindingsRun]
          exact ClosSem.fixClock_evaluate bindings env1 s0
        have fixedTarget : ClosSem.fixClock {t0 with clock := t0.clock + ck} (targetBinds, t) = (targetBinds, t) := by
          rw [← targetRun]
          exact ClosSem.fixClock_evaluate bout env2 {t0 with clock := t0.clock + ck}
        cases bindsResult with
        | err error =>
          cases targetBinds with
          | val values => exact False.elim bindsRelated
          | err targetError =>
            simp only [ClosSem.evaluate, bindingsRun, fixedSource, Prod.mk.injEq] at sourceRun
            obtain ⟨rfl, rfl⟩ := sourceRun
            refine ⟨ck, .err targetError, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2,
              disjoint2, bindsWell, ?_, states2, bindsRelated⟩
            simp only [ClosSem.evaluate, targetRun, fixedTarget]
        | val values =>
          cases targetBinds with
          | err error => exact False.elim bindsRelated
          | val targetValues =>
            change List.Forall₂ (valueRel g2 l2 t.code) values targetValues at bindsRelated
            have bodyRun : ClosSem.evaluate [body] (values ++ env1) middle = (res, s) := by
              simpa only [ClosSem.evaluate, bindingsRun, fixedSource] using sourceRun
            have middleClock : middle.clock ≤ s0.clock :=
              ClosSem.evaluate_clock_source.1 bindings env1 s0 (.val values) middle bindingsRun
            have codeGrowth : t0.code.submap t.code := by
              simpa using ClosProps.CodeGrowthPort.evaluate_mono bout env2
                {t0 with clock := t0.clock + ck} (.val targetValues) t targetRun
            have envWell2 := everyValueWellFormed_subg g1 l1 t0.code env1 t.code g2 l2
              ⟨envWell, codeGrowth, growth2, allowed2⟩
            have bodyEnvWell : ∀ v ∈ values ++ env1, valueWellFormed g2 l2 t.code v := by
              intro v member
              simp only [List.mem_append] at member
              rcases member with member | member
              · exact bindsWell v member
              · exact envWell2 v member
            have originalEnv : envRel (valueRel g2 l2 t.code) env1 env2 0
                [(0, .let trace bout out)] :=
              envValueRel_subg g1 l1 t0.code env1 env2 0 _ g2 l2 t.code
                ⟨by simpa using envRelated, growth2, allowed2, codeGrowth⟩
            have bindLength : values.length = bout.length := by
              have x := ClosProps.evaluateImpLength bindings env1 s0 middle values bindingsRun
              have y := calls_length bindings g0 bout gm bindingsCompile
              omega
            have bodyEnv := letBodyEnvRel (valueRel g2 l2 t.code) env1 env2 values targetValues
              trace bout out bindLength bindsRelated originalEnv
            have bodyGrowth := stateExtends_trans next g1 g2 growth growth2
            have bodyBound2 : Set.Subset (Set.diff {n | n ∈ codeLocations [body]} (sptDomain next.1)) l2 :=
              Set.Subset.trans bodyBound allowed2
            have bodyIncluded := codeIncludes_submap next.2 t0.code t.code ⟨included, codeGrowth⟩
            have bodyDisjoint : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [body]})
                {n | n ∈ gm.2.map Prod.fst} := by
              apply Set.disjoint_left.mpr
              intro key a b
              exact bodyFresh key ⟨a, b⟩
            obtain ⟨ck2, res2, t2, g3, l3, inv3, stateWell3, growth3, well3, allowed3, disjoint3,
              resultWell3, bodyTargetRun, states3, related3⟩ :=
              bodyIH (values ++ env1) middle middleClock ([body], values ++ env1, middle)
                gm next (targetValues ++ env2) t [out] res s
                ({n | n ∈ codeLocations [body]} \ sptDomain next.1) l2 g2
                ⟨rfl, bodyRun, safe, bodyCompile, inv2, bodyAnnotations, bodyVars, bodyEnvWell,
                  stateWell2, middleWell, bodyDistinct, bodyDisjoint, rfl, bodyGrowth, bodyBound2,
                  disjoint2, well2, by simpa using bodyEnv, states2, bodyIncluded⟩
            have shifted := ClosProps.ClockShiftPort.evaluate_addClock t
              {t0 with clock := t0.clock + ck} (.val targetValues) bout env2
              ⟨targetRun, by simp⟩ ck2
            have shiftedRun : ClosSem.evaluate bout env2 {t0 with clock := t0.clock + (ck + ck2)} =
                (.val targetValues, {t with clock := t.clock + ck2}) := by
              simpa only [Nat.add_assoc] using shifted
            have fixedShift := ClosSem.fixClock_evaluate bout env2 {t0 with clock := t0.clock + (ck + ck2)}
            rw [shiftedRun] at fixedShift
            have wholeTarget : ClosSem.evaluate [.let trace bout out] env2
                {t0 with clock := t0.clock + (ck + ck2)} = (res2, t2) := by
              simpa only [ClosSem.evaluate, shiftedRun, fixedShift] using bodyTargetRun
            exact ⟨ck + ck2, res2, t2, g3, l3, inv3, stateWell3,
              stateExtends_trans g1 g2 g3 growth2 growth3, well3, Set.Subset.trans allowed2 allowed3,
              disjoint3, resultWell3, wholeTarget, states3, related3⟩
private theorem fnRecWellFormed (name : Flapjack.Basis.Pure.MlString.MlString)
    (loc arity : Nat) (body : ClosLang.Exp)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (vars : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup) :
    recClosureWellFormed loc [(arity, body)] := by
  unfold recClosureWellFormed
  simp only [List.map_cons, List.map_nil]
  have locationBody : everyFnLocationSome [body] := by
    simpa [everyFnLocationSome, fnLocationSomeExp] using locations
  have varsBody : everyFnVarsNone [body] := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using vars
  have d : (codeLocations [body] ++ [loc]).Nodup := by
    simpa [codeLocations, codeLocationsExp] using distinct
  have ⟨distinctBody, _, apart⟩ := List.nodup_append.mp d
  refine ⟨locationBody, varsBody, ?_, distinctBody⟩
  intro n ⟨member, bodyMember⟩
  have eq : n = loc := by simpa using member
  subst n
  exact apart loc bodyMember loc (by simp) rfl

private theorem fnInitialFacts (name : Flapjack.Basis.Pure.MlString.MlString)
    (loc arity : Nat) (body : ClosLang.Exp) (g0 : State)
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (vars : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.fn name (some loc) none arity body]})
      {n | n ∈ g0.2.map Prod.fst}) (well : wellFormed g0) :
    recClosureWellFormed loc [(arity, body)] ∧
    (∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations [body]} ∧ label ∈ g0.2.map Prod.fst)) ∧
    (∀ label, ¬ (label ∈ (List.range [(arity, body)].length).map (fun i => 2 * i + loc + 1) ∧
      label ∈ g0.2.map Prod.fst)) ∧
    ¬ sptDomain g0.1 loc := by
  have locationIn : loc ∈ codeLocations [.fn name (some loc) none arity body] := by
    simp [codeLocations, codeLocationsExp]
  have freshLocation : loc + 1 ∉ g0.2.map Prod.fst := by
    intro present
    apply Set.disjoint_left.mp fresh (show loc + 1 ∈ Set.image Nat.succ
      {n | n ∈ codeLocations [.fn name (some loc) none arity body]} from ⟨loc, locationIn, rfl⟩) present
  refine ⟨fnRecWellFormed name loc arity body locations vars distinct, ?_, ?_, ?_⟩
  · intro label ⟨⟨n, member, eq⟩, present⟩
    apply Set.disjoint_left.mp fresh
    · refine ⟨n, ?_, eq⟩
      simpa [codeLocations, codeLocationsExp] using Or.inl member
    · exact present
  · intro label ⟨member, present⟩
    have eq : label = loc + 1 := by simpa using member
    exact freshLocation (eq ▸ present)
  · intro member
    apply freshLocation
    have : loc + 1 ∈ Set.image Nat.succ (sptDomain g0.1) := ⟨loc, member, rfl⟩
    rw [← well.1] at this
    exact this

private theorem fnOrdinaryRelation (name : Flapjack.Basis.Pure.MlString.MlString)
    (loc arity : Nat) (body fastOut out : ClosLang.Exp) (g0 fastState g g1 : State)
    (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (vars : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.fn name (some loc) none arity body]})
      {n | n ∈ g0.2.map Prod.fst}) (well : wellFormed g0)
    (fastRun : calls [body] (insertEachSource loc 1 g0) = ([fastOut], fastState))
    (notClosed : closed (.fn name (some loc) none arity fastOut) ≠ true)
    (ordinaryRun : calls [body] g0 = ([out], g)) (growth : stateExtends g g1)
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.fn name (some loc) none arity body]} (sptDomain g.1)) allowed)
    (included : codeIncludes g.2 code) : recClosureRel g1 allowed code loc [(arity, body)] [(arity, out)] := by
  classical
  obtain ⟨groupWell, bodyFresh, slotFresh, initialAbsent⟩ :=
    fnInitialFacts name loc arity body g0 locations vars distinct fresh well
  have locNotBody : loc ∉ codeLocations [body] := by
    have avoid := groupWell.2.2.1 loc
    simpa using avoid
  have finalAbsent : ¬ sptDomain g.1 loc := by
    intro present
    rcases calls_domainLocations [body] g0 [out] g ordinaryRun present with old | new
    · exact initialAbsent old
    · exact locNotBody new
  have bodyBound : Set.Subset (Set.diff {n | n ∈ codeLocations [body]} (sptDomain g.1)) allowed := by
    intro key ⟨member, absent⟩
    apply bound
    refine ⟨?_, absent⟩
    simpa [codeLocations, codeLocationsExp] using Or.inl member
  have locBound : loc ∈ allowed := by
    apply bound
    refine ⟨?_, finalAbsent⟩
    simp [codeLocations, codeLocationsExp]
  have guardFalse : ¬ List.Forall₂
      (fun fn converted => ∀ n, DbVars.hasVar n (free [converted]).2 = true → n < fn.1)
      [(arity, body)] [fastOut] := by
    intro guard
    have closedBody : ∀ n, DbVars.hasVar n (free [fastOut]).2 = true → n < arity := by simpa using guard
    exact notClosed ((closedFn name (some loc) none arity fastOut).mpr closedBody)
  unfold recClosureRel
  refine ⟨g0, groupWell, well, ?_, ?_, ?_⟩
  · simpa using bodyFresh
  · simpa using slotFresh
  · simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
    change (if List.Forall₂ _ [(arity, body)] (calls [body] (insertEachSource loc 1 g0)).1 then _ else _)
    simp only [fastRun, guardFalse, ↓reduceIte, ordinaryRun, List.zip_cons_cons]
    refine ⟨rfl, growth, bodyBound, ?_, included⟩
    simpa using locBound

private theorem fnOptimizedRelation (name : Flapjack.Basis.Pure.MlString.MlString)
    (loc arity : Nat) (body fastOut : ClosLang.Exp) (g0 fastState g1 : State)
    (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (locations : everyFnLocationSome [.fn name (some loc) none arity body])
    (vars : everyFnVarsNone [.fn name (some loc) none arity body])
    (distinct : (codeLocations [.fn name (some loc) none arity body]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.fn name (some loc) none arity body]})
      {n | n ∈ g0.2.map Prod.fst}) (well : wellFormed g0)
    (fastRun : calls [body] (insertEachSource loc 1 g0) = ([fastOut], fastState))
    (isClosed : closed (.fn name (some loc) none arity fastOut) = true)
    (growth : stateExtends (fastState.1, (loc + 1, arity, fastOut) :: fastState.2) g1)
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.fn name (some loc) none arity body]}
      (sptDomain fastState.1)) allowed)
    (included : codeIncludes ((loc + 1, arity, fastOut) :: fastState.2) code) :
    recClosureRel g1 allowed code loc [(arity, body)]
      [(arity, .call .none 0 (loc + 1) (variablesSource .none 1 arity))] := by
  classical
  obtain ⟨groupWell, bodyFresh, slotFresh, _⟩ :=
    fnInitialFacts name loc arity body g0 locations vars distinct fresh well
  have bodyBound : Set.Subset (Set.diff {n | n ∈ codeLocations [body]} (sptDomain fastState.1)) allowed := by
    intro key ⟨member, absent⟩
    apply bound
    refine ⟨?_, absent⟩
    simpa [codeLocations, codeLocationsExp] using Or.inl member
  have guard : List.Forall₂
      (fun fn converted => ∀ n, DbVars.hasVar n (free [converted]).2 = true → n < fn.1)
      [(arity, body)] [fastOut] := by
    simpa using (closedFn name (some loc) none arity fastOut).mp isClosed
  unfold recClosureRel
  refine ⟨g0, groupWell, well, ?_, ?_, ?_⟩
  · simpa using bodyFresh
  · simpa using slotFresh
  · simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil]
    change (if List.Forall₂ _ [(arity, body)] (calls [body] (insertEachSource loc 1 g0)).1 then _ else _)
    simp only [fastRun, guard, ↓reduceIte, List.zip_cons_cons]
    refine ⟨⟨.none, 0, ?_⟩, ?_, bodyBound, ?_⟩
    · simp [callsListSource]
    · simpa [codeListSource] using growth
    · simpa [codeListSource] using included

private theorem finishFnCreation {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (loc arity : Nat) (body out : ClosLang.Exp) (env1 env2 : List ClosSem.Value)
    (s0 : ClosSem.State (NumSet × C) F) (t0 : ClosSem.State C F) (g1 : State) (l1 : Set Nat)
    (validArity : arity ≤ s0.maxApp ∧ arity ≠ 0)
    (invariant : codeInv (some g1) l1 s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle)
    (envWell : ∀ v ∈ env1, valueWellFormed g1 l1 t0.code v)
    (stateWell : stateValuesWellFormed g1 l1 t0.code s0)
    (well : wellFormed g1) (disjoint : Disjoint l1 (sptDomain g1.1))
    (states : stateRel g1 l1 s0 t0)
    (group : recClosureRel g1 l1 t0.code loc [(arity, body)] [(arity, out)])
    (envRelated : envRel (valueRel g1 l1 t0.code) env1 env2 0 [(arity, out)]) :
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 s0.code s0.compile s0.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code s0 ∧ stateExtends g1 g2 ∧ wellFormed g2 ∧
      l1 ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) (.val [.closure (some loc) [] env1 arity body]) ∧
      ClosSem.evaluate [.fn name (some loc) none arity out] env2 {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 s0 t ∧
      resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code)
        (.val [.closure (some loc) [] env1 arity body]) res' := by
  have maxEq := stateRel_maxApp g1 l1 s0 t0 states
  have targetArity : arity ≤ t0.maxApp ∧ arity ≠ 0 := by simpa [← maxEq] using validArity
  have valWell : valueWellFormed g1 l1 t0.code (.closure (some loc) [] env1 arity body) := by
    change valueWellFormed g1 (fun x => x ∈ l1) t0.code (.closure (some loc) [] env1 arity body)
    rw [valueWellFormed.eq_3]
    exact ⟨by simp, envWell, ⟨[(arity, out)], group⟩⟩
  have valRelated : valueRel g1 l1 t0.code (.closure (some loc) [] env1 arity body)
      (.closure (some loc) [] env2 arity out) := by
    apply ((valueRel_sourceEquations g1 l1 t0.code).2.1 _ _ _ _ _ _).mpr
    exact ⟨loc, [], env2, out, group, rfl, rfl, .nil, envRelated⟩
  refine ⟨0, .val [.closure (some loc) [] env2 arity out], t0, g1, l1, invariant, stateWell,
    stateExtends_refl g1 well.2, well, Set.Subset.rfl, disjoint, ?_, ?_, states, ?_⟩
  · simpa [everyResult] using valWell
  · simp [ClosSem.evaluate, targetArity]
  · exact .cons valRelated .nil

private theorem fnBodyEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (name : Flapjack.Basis.Pure.MlString.MlString) (loc arity : Nat) (out : ClosLang.Exp)
    (h : envRel R env1 env2 0 [(0, .fn name (some loc) none arity out)]) :
    envRel R env1 env2 0 [(arity, out)] := by
  unfold envRel at h ⊢
  split <;> simp_all [freeVar, freeVars, freeVarExp, Nat.add_comm]

private theorem fnCase {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vars : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F) :
    ExprMotive [.fn name loc vars arity body] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, wellState,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases loc with
  | none => simp [everyFnLocationSome, fnLocationSomeExp] at annotations
  | some loc =>
    cases vars with
    | some vs => simp [everyFnVarsNone, fnVarsNoneExp] at varsNone
    | none =>
      by_cases validArity : arity ≤ s0.maxApp ∧ arity ≠ 0
      · simp [ClosSem.evaluate, validArity] at sourceRun
        obtain ⟨rfl, rfl⟩ := sourceRun
        cases fastRun : calls [body] (insertEachSource loc 1 g0) with
        | mk fastEs fastState =>
          obtain ⟨fastOut, rfl⟩ := calls_sing body (insertEachSource loc 1 g0) fastEs fastState fastRun
          have fastSing : callsSing body (insertEachSource loc 1 g0) = (fastOut, fastState) := by
            have eq := fastRun
            simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
            exact Prod.ext eq.1 eq.2
          by_cases isClosed : closed (.fn name (some loc) none arity fastOut) = true
          · simp only [calls, callsSingList, callsSing, Option.getD_some, fastSing, isClosed,
              if_true, Prod.mk.injEq] at compileRun
            obtain ⟨rfl, rfl⟩ := compileRun
            have bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.fn name (some loc) none arity body]}
                (sptDomain fastState.1)) l1 := by
              intro key hkey
              apply allowed
              rw [locations]
              exact hkey
            have group := fnOptimizedRelation name loc arity body fastOut g0 fastState g1 l1 t0.code
              annotations varsNone distinct fresh initialWell fastRun isClosed growth bound included
            have related := fnBodyEnvRel (valueRel g1 l1 t0.code) env1 env2 name loc arity
              (.call .none 0 (loc + 1) (variablesSource .none 1 arity)) (by simpa using envRelated)
            exact finishFnCreation name loc arity body _ env1 env2 s0 t0 g1 l1 validArity invariant
              envWell wellState well disjoint states group related
          · cases ordinaryRun : calls [body] g0 with
            | mk ordinaryEs next =>
              obtain ⟨out, rfl⟩ := calls_sing body g0 ordinaryEs next ordinaryRun
              have ordinarySing : callsSing body g0 = (out, next) := by
                have eq := ordinaryRun
                simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
                exact Prod.ext eq.1 eq.2
              simp only [calls, callsSingList, callsSing, Option.getD_some, fastSing, isClosed,
                ordinarySing, Prod.mk.injEq] at compileRun
              obtain ⟨rfl, rfl⟩ := compileRun
              have bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.fn name (some loc) none arity body]}
                  (sptDomain next.1)) l1 := by
                intro key hkey
                apply allowed
                rw [locations]
                exact hkey
              have group := fnOrdinaryRelation name loc arity body fastOut out g0 fastState next g1 l1 t0.code
                annotations varsNone distinct fresh initialWell fastRun isClosed ordinaryRun growth bound included
              have related := fnBodyEnvRel (valueRel g1 l1 t0.code) env1 env2 name loc arity out (by simpa using envRelated)
              exact finishFnCreation name loc arity body out env1 env2 s0 t0 g1 l1 validArity invariant
                envWell wellState well disjoint states group related
      · simp [ClosSem.evaluate, validArity, ClosSem.typeError] at sourceRun
        obtain ⟨rfl, rfl⟩ := sourceRun
        exact (safe rfl).elim
private theorem callArgsEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (trace : BackendCommon.Tra) (ticks dest : Nat) (args : List ClosLang.Exp)
    (related : envRel R env1 env2 0 [(0, .call trace ticks dest args)]) :
    envRel R env1 env2 0 (args.map (fun e => (0, e))) := by
  have existsFree : ∀ n xs, freeVars n xs ↔ ∃ e ∈ xs, freeVarExp n e := by
    intro n xs
    induction xs with
    | nil => simp [freeVars]
    | cons e es ih => simp [freeVars, ih]
  unfold envRel at related ⊢
  by_cases same : env1.length = env2.length
  · simpa only [same, ↓reduceIte] using related
  · simp only [same, ↓reduceIte] at related ⊢
    simp only [freeVar, freeVars, freeVarExp, Nat.zero_add, List.mem_singleton,
      exists_eq_left, List.mem_map, exists_exists_and_eq_and, or_false] at related ⊢
    simpa [existsFree] using related

private theorem callCase {C F : Type} (trace : BackendCommon.Tra) (ticks dest : Nat) (args : List ClosLang.Exp)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (argsIH : ExprMotive args env1 s0) : ExprMotive [.call trace ticks dest args] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, wellState,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases argsCompile : calls args g0 with
  | mk out next =>
    have argsSing : callsSingList args g0 = (out, next) := argsCompile
    simp only [calls, callsSingList, callsSing, argsSing, Prod.mk.injEq] at compileRun
    obtain ⟨rfl, rfl⟩ := compileRun
    have argsAnnotations : everyFnLocationSome args := by
      simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
    have argsVars : everyFnVarsNone args := by simpa [everyFnVarsNone, fnVarsNoneExp] using varsNone
    have argsDistinct : (codeLocations args).Nodup := by simpa [codeLocations, codeLocationsExp] using distinct
    have argsFresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations args})
        {n | n ∈ g0.2.map Prod.fst} := by simpa [codeLocations, codeLocationsExp] using fresh
    have argsBound : Set.Subset (Set.diff {n | n ∈ codeLocations args} (sptDomain next.1)) l1 := by
      intro key hkey
      apply allowed
      rw [locations]
      change (key ∈ codeLocations args ∧ ¬ sptDomain next.1 key) at hkey
      change (key ∈ codeLocations [.call trace ticks dest args] ∧ ¬ sptDomain next.1 key)
      exact ⟨by simpa [codeLocations, codeLocationsExp] using hkey.1, hkey.2⟩
    have argsEnv := callArgsEnvRel (valueRel g1 l1 t0.code) env1 env2 trace ticks dest out (by simpa using envRelated)
    cases argsRun : ClosSem.evaluate args env1 s0 with
    | mk argsResult middle =>
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        simp [ClosSem.evaluate, argsRun] at sourceRun
        obtain ⟨rfl, rfl⟩ := sourceRun
        exact safe rfl
      have argsSim := argsIH (args, env1, s0) g0 next env2 t0 out argsResult middle
        ({n | n ∈ codeLocations args} \ sptDomain next.1) l1 g1
        ⟨rfl, argsRun, argsSafe, argsCompile, invariant, argsAnnotations, argsVars, envWell, wellState,
          initialWell, argsDistinct, argsFresh, rfl, growth, argsBound, disjoint, well,
          argsEnv, states, included⟩
      obtain ⟨ck, targetArgs, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
        argsWell, targetRun, states2, argsRelated⟩ := argsSim
      have fixedSource : ClosSem.fixClock s0 (argsResult, middle) = (argsResult, middle) := by
        rw [← argsRun]
        exact ClosSem.fixClock_evaluate args env1 s0
      have fixedTarget : ClosSem.fixClock {t0 with clock := t0.clock + ck} (targetArgs, t) = (targetArgs, t) := by
        rw [← targetRun]
        exact ClosSem.fixClock_evaluate out env2 {t0 with clock := t0.clock + ck}
      cases argsResult with
      | err error =>
        cases targetArgs with
        | val values => exact False.elim argsRelated
        | err targetError =>
          simp only [ClosSem.evaluate, argsRun, fixedSource, Prod.mk.injEq] at sourceRun
          obtain ⟨rfl, rfl⟩ := sourceRun
          refine ⟨ck, .err targetError, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2,
            disjoint2, argsWell, ?_, states2, argsRelated⟩
          simp only [ClosSem.evaluate, targetRun, fixedTarget]
      | val values =>
        have emptyCode := states2.2.2.2.2.2
        simp [ClosSem.evaluate, argsRun, fixedSource, ClosSem.findCode, emptyCode,
          HolFiniteMapExact.empty, ClosSem.typeError] at sourceRun
        obtain ⟨rfl, rfl⟩ := sourceRun
        exact (safe rfl).elim
private theorem evaluateOrdinaryOp {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk) :
    ClosSem.evaluate [.op trace op args] env state =
      match ClosSem.evaluate args env state with
      | (.err error, next) => (.err error, next)
      | (.val values, next) => match ClosSem.doApp op values.reverse next with
        | .err error => (.err error, next)
        | .val (value, last) => (.val [value], last) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  cases run : ClosSem.evaluate args env state with
  | mk result next =>
    cases result with
    | err error => rfl
    | val values =>
      cases op <;> simp_all
      case thunkOp mode => cases mode <;> simp_all <;> rfl
      all_goals rfl
private theorem opArgsEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (trace : BackendCommon.Tra) (op : ClosLang.Op) (args : List ClosLang.Exp)
    (related : envRel R env1 env2 0 [(0, .op trace op args)]) :
    envRel R env1 env2 0 (args.map (fun e => (0, e))) := by
  apply callArgsEnvRel R env1 env2 trace 0 0 args
  unfold envRel at related ⊢
  split <;> simp_all [freeVar, freeVars, freeVarExp]

private theorem ordinaryOpCase {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (argsIH : ExprMotive args env1 s0) (notInstall : op ≠ .install)
    (notForce : op ≠ .thunkOp .forceThunk) : ExprMotive [.op trace op args] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, wellState,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases argsCompile : calls args g0 with
  | mk out next =>
    have argsSing : callsSingList args g0 = (out, next) := argsCompile
    simp only [calls, callsSingList, callsSing, argsSing, Prod.mk.injEq] at compileRun
    obtain ⟨rfl, rfl⟩ := compileRun
    have argsAnnotations : everyFnLocationSome args := by
      simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
    have argsVars : everyFnVarsNone args := by simpa [everyFnVarsNone, fnVarsNoneExp] using varsNone
    have argsDistinct : (codeLocations args).Nodup := by simpa [codeLocations, codeLocationsExp] using distinct
    have argsFresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations args})
        {n | n ∈ g0.2.map Prod.fst} := by simpa [codeLocations, codeLocationsExp] using fresh
    have argsBound : Set.Subset (Set.diff {n | n ∈ codeLocations args} (sptDomain next.1)) l1 := by
      intro key hkey
      apply allowed
      rw [locations]
      change (key ∈ codeLocations args ∧ ¬ sptDomain next.1 key) at hkey
      change (key ∈ codeLocations [.op trace op args] ∧ ¬ sptDomain next.1 key)
      exact ⟨by simpa [codeLocations, codeLocationsExp] using hkey.1, hkey.2⟩
    have argsEnv := opArgsEnvRel (valueRel g1 l1 t0.code) env1 env2 trace op out (by simpa using envRelated)
    cases argsRun : ClosSem.evaluate args env1 s0 with
    | mk argsResult middle =>
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        simp [evaluateOrdinaryOp trace op args env1 s0 notInstall notForce, argsRun] at sourceRun
        obtain ⟨rfl, rfl⟩ := sourceRun
        exact safe rfl
      have argsSim := argsIH (args, env1, s0) g0 next env2 t0 out argsResult middle
        ({n | n ∈ codeLocations args} \ sptDomain next.1) l1 g1
        ⟨rfl, argsRun, argsSafe, argsCompile, invariant, argsAnnotations, argsVars, envWell, wellState,
          initialWell, argsDistinct, argsFresh, rfl, growth, argsBound, disjoint, well,
          argsEnv, states, included⟩
      obtain ⟨ck, targetArgs, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
        argsWell, targetRun, states2, argsRelated⟩ := argsSim
      cases argsResult with
      | err error =>
        cases targetArgs with
        | val values => exact False.elim argsRelated
        | err targetError =>
          simp only [evaluateOrdinaryOp trace op args env1 s0 notInstall notForce, argsRun, Prod.mk.injEq] at sourceRun
          obtain ⟨rfl, rfl⟩ := sourceRun
          refine ⟨ck, .err targetError, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2,
            disjoint2, argsWell, ?_, states2, argsRelated⟩
          simp only [evaluateOrdinaryOp trace op out env2 _ notInstall notForce, targetRun]
      | val values =>
        cases targetArgs with
        | err error => exact False.elim argsRelated
        | val targetValues =>
          cases opRun : ClosSem.doApp op values.reverse middle with
          | err error =>
            have opThm := doApp_correct op values middle g2 l2 t targetValues
            rw [opRun] at opThm
            cases error with
            | raise value => exact False.elim opThm
            | abort abort =>
              rcases opThm with typeError | ⟨event, eventEq, targetOp⟩
              · subst abort
                simp [evaluateOrdinaryOp trace op args env1 s0 notInstall notForce, argsRun, opRun] at sourceRun
                obtain ⟨rfl, rfl⟩ := sourceRun
                exact (safe rfl).elim
              · subst abort
                have targetOpRun := targetOp ⟨argsRelated, states2⟩
                simp only [evaluateOrdinaryOp trace op args env1 s0 notInstall notForce, argsRun, opRun,
                  Prod.mk.injEq] at sourceRun
                obtain ⟨rfl, rfl⟩ := sourceRun
                refine ⟨ck, .err (.abort (.ffiError event)), t, g2, l2, inv2, stateWell2, growth2, well2,
                  allowed2, disjoint2, by simp [everyResult, everyErrorResult], ?_, states2, by simp [resultRel, excRel]⟩
                simp only [evaluateOrdinaryOp trace op out env2 _ notInstall notForce, targetRun, targetOpRun]
          | val pair =>
            obtain ⟨value, last⟩ := pair
            have opThm := doApp_correct op values middle g2 l2 t targetValues
            rw [opRun] at opThm
            obtain ⟨nextWell, valueWell⟩ := opThm.1 ⟨stateWell2, argsWell⟩
            obtain ⟨targetValue, targetLast, targetOpRun, valueRelated, stateRelated⟩ := opThm.2 ⟨argsRelated, states2⟩
            have fields1 := ClosInterp.doApp_compilerFields op values.reverse middle last value opRun
            have fields2 := ClosInterp.doApp_compilerFields op targetValues.reverse t targetLast targetValue targetOpRun
            simp only [evaluateOrdinaryOp trace op args env1 s0 notInstall notForce, argsRun, opRun,
              Prod.mk.injEq] at sourceRun
            obtain ⟨rfl, rfl⟩ := sourceRun
            refine ⟨ck, .val [targetValue], targetLast, g2, l2, ?_, ?_, growth2, well2, allowed2,
              disjoint2, ?_, ?_, stateRelated, ?_⟩
            · simpa [ClosInterp.CompilerFieldsPreserved, fields1.1, fields1.2.1, fields1.2.2.1,
                fields2.1, fields2.2.1, fields2.2.2.1] using inv2
            · simpa [ClosInterp.CompilerFieldsPreserved, fields2.2.2.1] using nextWell
            · simpa [everyResult, ClosInterp.CompilerFieldsPreserved, fields2.2.2.1] using valueWell
            · simp only [evaluateOrdinaryOp trace op out env2 _ notInstall notForce, targetRun, targetOpRun]
            · change List.Forall₂ (valueRel g2 l2 targetLast.code) [value] [targetValue]
              apply List.Forall₂.cons
              · simpa [ClosInterp.CompilerFieldsPreserved, fields2.2.2.1] using valueRelated
              · exact .nil
private theorem destThunkRelated {C F : Type} (g : State) (allowed : Set Nat)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (values targetValues : List ClosSem.Value) (mode : Flapjack.AstHOL.ThunkMode) (value : ClosSem.Value)
    (states : stateRel g allowed source target)
    (valuesRelated : List.Forall₂ (valueRel g allowed target.code) values targetValues)
    (sourceWell : stateValuesWellFormed g allowed target.code source)
    (found : ClosSem.destThunk values source.refs = .isThunk mode value) :
    ∃ ptr targetValue, values = [.refPtr false ptr] ∧ targetValues = [.refPtr false ptr] ∧
      source.refs.lookup ptr = some (.thunk mode value) ∧
      target.refs.lookup ptr = some (.thunk mode targetValue) ∧
      valueWellFormed g allowed target.code value ∧ valueRel g allowed target.code value targetValue := by
  cases values with
  | nil => simp [ClosSem.destThunk] at found
  | cons head tail =>
    cases tail with
    | cons next tail => simp [ClosSem.destThunk] at found
    | nil =>
      cases head <;> simp [ClosSem.destThunk] at found
      case refPtr flag ptr =>
        cases flag with
        | true =>
          cases h : source.refs.lookup ptr with
          | none => simp [h] at found
          | some cell => cases cell <;> simp [h] at found
        | false =>
          cases entry : source.refs.lookup ptr with
          | none => simp [entry] at found
          | some cell =>
            cases cell <;> simp [entry] at found
            case thunk sourceMode sourceValue =>
              obtain ⟨rfl, rfl⟩ := found
              cases valuesRelated with
              | cons headRelated tailRelated =>
                cases tailRelated
                have view := ClosProps.simpleValRel_view (valueRel g allowed target.code)
                  (valueRel_simple g allowed target.code) (.refPtr false ptr) _ headRelated
                cases view with
                | refPtr =>
                  obtain ⟨targetCell, targetEntry, cellsRelated⟩ :=
                    stateRel_lookupRefs g allowed source target ptr (.thunk sourceMode sourceValue) ⟨states, entry⟩
                  cases targetCell with
                  | valueArray values => simp [ClosProps.refRel] at cellsRelated
                  | byteArray bytes => simp [ClosProps.refRel] at cellsRelated
                  | thunk targetMode targetValue =>
                    simp only [ClosProps.refRel] at cellsRelated
                    obtain ⟨rfl, valueRelated⟩ := cellsRelated
                    have valueWell : valueWellFormed g allowed target.code sourceValue := by
                      have cellWell := sourceWell.2.1 ptr (.thunk sourceMode sourceValue) entry
                      simpa [everyRefValue] using cellWell
                    exact ⟨ptr, targetValue, rfl, rfl, entry, targetEntry, valueWell, valueRelated⟩
private theorem destThunkNotThunkRelated {C F : Type} (g : State) (allowed : Set Nat)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (value targetValue : ClosSem.Value) (states : stateRel g allowed source target)
    (values : valueRel g allowed target.code value targetValue)
    (notThunk : ClosSem.destThunk [value] source.refs = .notThunk) :
    ClosSem.destThunk [targetValue] target.refs = .notThunk := by
  have view := ClosProps.simpleValRel_view (valueRel g allowed target.code)
    (valueRel_simple g allowed target.code) value targetValue values
  cases view <;> simp_all [ClosSem.destThunk]
  case refPtr flag ptr =>
    have refsRelated := states.2.2.2.2.1 ptr
    cases src : source.refs.lookup ptr with
    | none => simp [src] at notThunk
    | some sourceCell =>
      cases tgt : target.refs.lookup ptr with
      | none => simp [src, tgt, optionRel] at refsRelated
      | some targetCell =>
        simp only [src, tgt, optionRel] at refsRelated
        cases sourceCell <;> cases targetCell <;>
          simp_all [ClosProps.refRel]
        all_goals cases flag <;> simp_all
private theorem stateRel_updateThunk {C F : Type} (g : State) (allowed : Set Nat)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F) (ptr : Nat)
    (value targetValue : ClosSem.Value) (states : stateRel g allowed source target)
    (values : valueRel g allowed target.code value targetValue) :
    stateRel g allowed {source with refs := source.refs.updateEq (ptr, .thunk .evaluated value)}
      {target with refs := target.refs.updateEq (ptr, .thunk .evaluated targetValue)} := by
  refine ⟨states.1, states.2.1, states.2.2.1, states.2.2.2.1, ?_, states.2.2.2.2.2⟩
  intro key
  by_cases same : key = ptr
  · subst key
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, optionRel, ClosProps.refRel] using values
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] using states.2.2.2.2.1 key

private theorem stateWell_updateThunk {C F : Type} (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (source : ClosSem.State (NumSet × C) F)
    (ptr : Nat) (value : ClosSem.Value) (stateWell : stateValuesWellFormed g allowed code source)
    (valueWell : valueWellFormed g allowed code value) :
    stateValuesWellFormed g allowed code {source with refs := source.refs.updateEq (ptr, .thunk .evaluated value)} := by
  refine ⟨stateWell.1, ?_, stateWell.2.2⟩
  intro key cell found
  by_cases same : key = ptr
  · subst key
    simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at found
    cases found
    simpa [everyRefValue] using valueWell
  · apply stateWell.2.1 key cell
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, same] using found
private theorem updateThunkRelated {C F : Type} (g : State) (allowed : Set Nat)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F) (ptr : Nat)
    (value targetValue : ClosSem.Value) (refs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (states : stateRel g allowed source target)
    (sourceWell : stateValuesWellFormed g allowed target.code source)
    (values : valueRel g allowed target.code value targetValue)
    (valueWell : valueWellFormed g allowed target.code value)
    (updated : ClosSem.updateThunk [.refPtr false ptr] source.refs [value] = some refs) :
    ∃ targetRefs,
      ClosSem.updateThunk [.refPtr false ptr] target.refs [targetValue] = some targetRefs ∧
      stateRel g allowed {source with refs := refs} {target with refs := targetRefs} ∧
      stateValuesWellFormed g allowed target.code {source with refs := refs} := by
  cases status : ClosSem.destThunk [value] source.refs with
  | badRef => simp [ClosSem.updateThunk, status] at updated
  | isThunk mode inner => simp [ClosSem.updateThunk, status] at updated
  | notThunk =>
    have targetStatus := destThunkNotThunkRelated g allowed source target value targetValue states values status
    cases cell : source.refs.lookup ptr with
    | none => simp [ClosSem.updateThunk, status, ClosSem.storeThunk, cell] at updated
    | some sourceCell =>
      cases sourceCell with
      | valueArray xs => simp [ClosSem.updateThunk, status, ClosSem.storeThunk, cell] at updated
      | byteArray xs => simp [ClosSem.updateThunk, status, ClosSem.storeThunk, cell] at updated
      | thunk mode inner =>
        cases mode with
        | evaluated => simp [ClosSem.updateThunk, status, ClosSem.storeThunk, cell] at updated
        | notEvaluated =>
          simp [ClosSem.updateThunk, status, ClosSem.storeThunk, cell] at updated
          subst refs
          obtain ⟨targetCell, targetCellLookup, cellsRelated⟩ :=
            stateRel_lookupRefs g allowed source target ptr (.thunk .notEvaluated inner) ⟨states, cell⟩
          cases targetCell with
          | valueArray xs => simp [ClosProps.refRel] at cellsRelated
          | byteArray xs => simp [ClosProps.refRel] at cellsRelated
          | thunk targetMode targetInner =>
            simp only [ClosProps.refRel] at cellsRelated
            obtain ⟨rfl, _⟩ := cellsRelated
            refine ⟨target.refs.updateEq (ptr, .thunk .evaluated targetValue), ?_, ?_, ?_⟩
            · simp [ClosSem.updateThunk, targetStatus, ClosSem.storeThunk, targetCellLookup]
            · exact stateRel_updateThunk g allowed source target ptr value targetValue states values
            · exact stateWell_updateThunk g allowed target.code source ptr value sourceWell valueWell
private theorem forceGeneratedCompilation (g : State) :
    calls [ClosSem.appUnit (.var .none 0)] g = ([ClosSem.appUnit (.var .none 0)], g) := by
  simp [calls, callsSingList, callsSing, ClosSem.appUnit]

private theorem forceGeneratedSyntax :
    everyFnLocationSome [ClosSem.appUnit (.var .none 0)] ∧
    everyFnVarsNone [ClosSem.appUnit (.var .none 0)] ∧
    codeLocations [ClosSem.appUnit (.var .none 0)] = [] := by
  simp [ClosSem.appUnit, everyFnLocationSome, fnLocationSomeExp,
    everyFnVarsNone, fnVarsNoneExp, codeLocations, codeLocationsExp]
private theorem forceThunkCase {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (argsIH : ExprMotive args env1 s0)
    (forceIH : ∀ (value : ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock ≤ s0.clock → ExprMotive [ClosSem.appUnit (.var .none 0)] [value] state) :
    ExprMotive [.op trace (.thunkOp .forceThunk) args] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, wellState,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases argsCompile : calls args g0 with
  | mk out next =>
    have argsSing : callsSingList args g0 = (out, next) := argsCompile
    simp only [calls, callsSingList, callsSing, argsSing, Prod.mk.injEq] at compileRun
    obtain ⟨rfl, rfl⟩ := compileRun
    have argsAnnotations : everyFnLocationSome args := by
      simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
    have argsVars : everyFnVarsNone args := by simpa [everyFnVarsNone, fnVarsNoneExp] using varsNone
    have argsDistinct : (codeLocations args).Nodup := by simpa [codeLocations, codeLocationsExp] using distinct
    have argsFresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations args})
        {n | n ∈ g0.2.map Prod.fst} := by simpa [codeLocations, codeLocationsExp] using fresh
    have argsBound : Set.Subset (Set.diff {n | n ∈ codeLocations args} (sptDomain next.1)) l1 := by
      intro key hkey
      apply allowed
      rw [locations]
      change (key ∈ codeLocations args ∧ ¬ sptDomain next.1 key) at hkey
      change (key ∈ codeLocations [.op trace (.thunkOp .forceThunk) args] ∧ ¬ sptDomain next.1 key)
      exact ⟨by simpa [codeLocations, codeLocationsExp] using hkey.1, hkey.2⟩
    have argsEnv := opArgsEnvRel (valueRel g1 l1 t0.code) env1 env2 trace (.thunkOp .forceThunk) out
      (by simpa using envRelated)
    have nextWell := calls_wellFormed args g0 out next
      ⟨argsCompile, argsDistinct, fun key h => Set.disjoint_left.mp argsFresh h.1 h.2,
        argsAnnotations, initialWell⟩
    cases argsRun : ClosSem.evaluate args env1 s0 with
    | mk argsResult middle =>
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        simp [ClosSem.evaluate, argsRun] at sourceRun
        obtain ⟨rfl, rfl⟩ := sourceRun
        exact safe rfl
      have argsSim := argsIH (args, env1, s0) g0 next env2 t0 out argsResult middle
        ({n | n ∈ codeLocations args} \ sptDomain next.1) l1 g1
        ⟨rfl, argsRun, argsSafe, argsCompile, invariant, argsAnnotations, argsVars, envWell, wellState,
          initialWell, argsDistinct, argsFresh, rfl, growth, argsBound, disjoint, well,
          argsEnv, states, included⟩
      obtain ⟨ck, targetArgs, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
        argsWell, targetRun, states2, argsRelated⟩ := argsSim
      have fixedSource : ClosSem.fixClock s0 (argsResult, middle) = (argsResult, middle) := by
        rw [← argsRun]
        exact ClosSem.fixClock_evaluate args env1 s0
      have fixedTarget : ClosSem.fixClock {t0 with clock := t0.clock + ck} (targetArgs, t) = (targetArgs, t) := by
        rw [← targetRun]
        exact ClosSem.fixClock_evaluate out env2 {t0 with clock := t0.clock + ck}
      cases argsResult with
      | err error =>
        cases targetArgs with
        | val values => exact False.elim argsRelated
        | err targetError =>
          simp only [ClosSem.evaluate, argsRun, fixedSource, Prod.mk.injEq] at sourceRun
          obtain ⟨rfl, rfl⟩ := sourceRun
          refine ⟨ck, .err targetError, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2,
            disjoint2, argsWell, ?_, states2, argsRelated⟩
          simp only [ClosSem.evaluate, targetRun, fixedTarget]
      | val values =>
        cases targetArgs with
        | err error => exact False.elim argsRelated
        | val targetValues =>
          change List.Forall₂ (valueRel g2 l2 t.code) values targetValues at argsRelated
          cases dest : ClosSem.destThunk values middle.refs with
          | badRef | notThunk =>
            simp [ClosSem.evaluate, argsRun, fixedSource, dest, ClosSem.typeError] at sourceRun
            obtain ⟨rfl, rfl⟩ := sourceRun
            exact (safe rfl).elim
          | isThunk mode value =>
            obtain ⟨ptr, targetValue, valuesEq, targetValuesEq, sourceEntry, targetEntry, valueWell, valueRelated⟩ :=
              destThunkRelated g2 l2 middle t values targetValues mode value states2 argsRelated stateWell2 dest
            have targetDest : ClosSem.destThunk targetValues t.refs = .isThunk mode targetValue := by
              simp [targetValuesEq, ClosSem.destThunk, targetEntry]
            cases mode with
            | evaluated =>
              simp only [ClosSem.evaluate, argsRun, fixedSource, dest, Prod.mk.injEq] at sourceRun
              obtain ⟨rfl, rfl⟩ := sourceRun
              refine ⟨ck, .val [targetValue], t, g2, l2, inv2, stateWell2, growth2, well2, allowed2,
                disjoint2, ?_, ?_, states2, ?_⟩
              · simpa [everyResult] using valueWell
              · simp [ClosSem.evaluate, targetRun, fixedTarget, targetDest]
              · exact .cons valueRelated .nil
            | notEvaluated =>
              have middleClock : middle.clock ≤ s0.clock :=
                ClosSem.evaluate_clock_source.1 args env1 s0 (.val values) middle argsRun
              have codeGrowth : t0.code.submap t.code := by
                simpa using ClosProps.CodeGrowthPort.evaluate_mono out env2
                  {t0 with clock := t0.clock + ck} (.val targetValues) t targetRun
              have nextGrowth := stateExtends_trans next g1 g2 growth growth2
              have nextIncluded := codeIncludes_submap next.2 t0.code t.code ⟨included, codeGrowth⟩
              have generatedEnv : envRel (valueRel g2 l2 t.code) [value] [targetValue] 0
                  [(0, ClosSem.appUnit (.var .none 0))] := by
                unfold envRel
                simp [valueRelated]
              have generatedFresh : Disjoint
                  (Set.image Nat.succ {n | n ∈ codeLocations [ClosSem.appUnit (.var .none 0)]})
                  {n | n ∈ next.2.map Prod.fst} := by simp [forceGeneratedSyntax.2.2]
              cases bodyRun : ClosSem.evaluate [ClosSem.appUnit (.var .none 0)] [value] middle with
              | mk bodyResult last =>
                have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
                  intro bad
                  subst bodyResult
                  simp [ClosSem.evaluate, argsRun, fixedSource, dest, bodyRun] at sourceRun
                  obtain ⟨rfl, rfl⟩ := sourceRun
                  exact safe rfl
                have bodySim := forceIH value middle middleClock
                  ([ClosSem.appUnit (.var .none 0)], [value], middle) next next [targetValue] t
                  [ClosSem.appUnit (.var .none 0)] bodyResult last
                  ({n | n ∈ codeLocations [ClosSem.appUnit (.var .none 0)]} \ sptDomain next.1) l2 g2
                  ⟨rfl, bodyRun, bodySafe, forceGeneratedCompilation next, inv2,
                    forceGeneratedSyntax.1, forceGeneratedSyntax.2.1, by simpa using valueWell, stateWell2,
                    nextWell, by simp [forceGeneratedSyntax.2.2], generatedFresh,
                    rfl, nextGrowth,
                    by
                      intro key member
                      exact False.elim (by simpa [forceGeneratedSyntax.2.2] using member.1),
                    disjoint2, well2,
                    by simpa using generatedEnv, states2, nextIncluded⟩
                obtain ⟨ck2, bodyRes, t2, g3, l3, inv3, stateWell3, growth3, well3, allowed3, disjoint3,
                  bodyWell, bodyTargetRun, states3, bodyRelated⟩ := bodySim
                have shifted := ClosProps.ClockShiftPort.evaluate_addClock t
                  {t0 with clock := t0.clock + ck} (.val targetValues) out env2 ⟨targetRun, by simp⟩ ck2
                have shiftedRun : ClosSem.evaluate out env2 {t0 with clock := t0.clock + (ck + ck2)} =
                    (.val targetValues, {t with clock := t.clock + ck2}) := by
                  simpa only [Nat.add_assoc] using shifted
                have fixedShift := ClosSem.fixClock_evaluate out env2 {t0 with clock := t0.clock + (ck + ck2)}
                rw [shiftedRun] at fixedShift
                cases bodyResult with
                | err error =>
                  cases bodyRes with
                  | val values => exact False.elim bodyRelated
                  | err targetError =>
                    simp only [ClosSem.evaluate, argsRun, fixedSource, dest, bodyRun, Prod.mk.injEq] at sourceRun
                    obtain ⟨rfl, rfl⟩ := sourceRun
                    refine ⟨ck + ck2, .err targetError, t2, g3, l3, inv3, stateWell3,
                      stateExtends_trans g1 g2 g3 growth2 growth3, well3, Set.Subset.trans allowed2 allowed3,
                      disjoint3, bodyWell, ?_, states3, bodyRelated⟩
                    simp [ClosSem.evaluate, shiftedRun, fixedShift, targetDest, bodyTargetRun]
                | val forced =>
                  cases bodyRes with
                  | err error => exact False.elim bodyRelated
                  | val targetForced =>
                    obtain ⟨forcedValue, rfl⟩ := ClosProps.evaluateSing (ClosSem.appUnit (.var .none 0)) [value]
                      middle last forced bodyRun
                    obtain ⟨targetForcedValue, rfl⟩ := ClosProps.evaluateSing (ClosSem.appUnit (.var .none 0))
                      [targetValue] _ t2 targetForced bodyTargetRun
                    change List.Forall₂ (valueRel g3 l3 t2.code) [forcedValue] [targetForcedValue] at bodyRelated
                    cases bodyRelated with
                    | cons forcedRelated tail =>
                      cases tail
                      have forcedWell : valueWellFormed g3 l3 t2.code forcedValue := bodyWell forcedValue (by simp)
                      cases updated : ClosSem.updateThunk values last.refs [forcedValue] with
                      | none =>
                        simp [ClosSem.evaluate, argsRun, fixedSource, dest, bodyRun, updated, ClosSem.typeError] at sourceRun
                        obtain ⟨rfl, rfl⟩ := sourceRun
                        exact (safe rfl).elim
                      | some refs =>
                        have updateSource : ClosSem.updateThunk [.refPtr false ptr] last.refs [forcedValue] = some refs := by
                          simpa [valuesEq] using updated
                        obtain ⟨targetRefs, targetUpdate, updatedStates, updatedWell⟩ :=
                          updateThunkRelated g3 l3 last t2 ptr forcedValue targetForcedValue refs
                            states3 stateWell3 forcedRelated forcedWell updateSource
                        have wholeSource : ClosSem.evaluate [.op trace (.thunkOp .forceThunk) args] env1 s0 =
                            (.val [forcedValue], {last with refs := refs}) := by
                          simp [ClosSem.evaluate, argsRun, fixedSource, dest, bodyRun, updated]
                        have sourceEq := sourceRun.symm.trans wholeSource
                        simp only [Prod.mk.injEq] at sourceEq
                        obtain ⟨rfl, rfl⟩ := sourceEq
                        refine ⟨ck + ck2, .val [targetForcedValue], {t2 with refs := targetRefs}, g3, l3,
                          by simpa using inv3, by simpa using updatedWell,
                          stateExtends_trans g1 g2 g3 growth2 growth3, well3, Set.Subset.trans allowed2 allowed3,
                          disjoint3, ?_, ?_, updatedStates, ?_⟩
                        · simpa [everyResult] using forcedWell
                        · rw [ClosSem.evaluate, shiftedRun, fixedShift]
                          simp only
                          rw [targetDest]
                          simp only
                          rw [bodyTargetRun]
                          simp only
                          rw [targetValuesEq, targetUpdate]
                        · exact .cons forcedRelated .nil
/-- Flapjack-specific lookup correspondence used when initializing code invariants. -/
theorem alistToFmapLookup {V : Type} (entries : List (Nat × V)) (key : Nat) :
    (HolFiniteMapExact.alistToFmap entries).lookup key = holALookup entries key := by
  induction entries with
  | nil => simp [HolFiniteMapExact.alistToFmap, HolFiniteMapExact.empty, holALookup]
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    by_cases eq : key = k
    · subst key
      rw [HolFiniteMapExact.lookup_alistToFmap_head (k, v) rest]
      simp [holALookup]
    · rw [HolFiniteMapExact.lookup_alistToFmap_tail (k, v) rest key eq]
      simpa [holALookup, eq] using ih

private theorem codeInvFacts {C F : Type} (g : State) (allowed : Set Nat)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (inv : codeInv (some g) allowed source.code source.compile source.compileOracle
      target.code target.compile target.compileOracle) :
    wellFormed g ∧ codeIncludes g.2 target.code := by
  obtain ⟨_, _, _, ⟨known, entries, well, _, _, codeEq, group⟩, _⟩ := inv
  have eq : g = (known, entries) := by simpa using group (by simp)
  subst g
  refine ⟨well, ?_⟩
  intro key value found
  rw [codeEq, alistToFmapLookup]
  exact found

private theorem installRelated {C F : Type} (g1 : State) (l1 : Set Nat)
    (source : ClosSem.State (NumSet × C) F) (target : ClosSem.State C F)
    (values targetValues : List ClosSem.Value) (result : Result (List ClosLang.Exp) ClosSem.Value)
    (last : ClosSem.State (NumSet × C) F)
    (invariant : codeInv (some g1) l1 source.code source.compile source.compileOracle
      target.code target.compile target.compileOracle)
    (states : stateRel g1 l1 source target) (disjoint : Disjoint l1 (sptDomain g1.1))
    (sourceWell : stateValuesWellFormed g1 l1 target.code source)
    (valuesRel : List.Forall₂ (valueRel g1 l1 target.code) values targetValues)
    (run : ClosSem.doInstall values source = (result, last)) (safe : result ≠ .err (.abort .typeError)) :
    ∃ exps converted aux g2 l2 targetLast,
      result = (if source.clock = 0 then .err (.abort .timeoutError) else .val exps) ∧
      ClosSem.doInstall targetValues target =
        (if source.clock = 0 then .err (.abort .timeoutError) else .val converted, targetLast) ∧
      exps ≠ [] ∧ syntaxOk exps ∧ calls exps g1 = (converted, g2) ∧
      wellFormed g2 ∧ codeIncludes g2.2 targetLast.code ∧
      stateValuesWellFormed g2 l2 targetLast.code last ∧
      target.code.submap targetLast.code ∧
      codeInv (some g2) l2 last.code last.compile last.compileOracle
        targetLast.code targetLast.compile targetLast.compileOracle ∧
      stateRel g2 l2 last targetLast ∧ stateExtends g1 g2 ∧ l1 ⊆ l2 ∧
      Disjoint l2 (sptDomain g2.1) ∧
      Disjoint (Set.image Nat.succ {x | x ∈ codeLocations exps}) target.code.domain ∧
      Set.Subset (Set.diff {x | x ∈ codeLocations exps} (sptDomain g2.1)) l2 ∧
      targetLast.code = target.code.updateListEq aux := by
  classical
  obtain ⟨byteValue, wordValue, bytes, words, config, exps, auxiliary, nextConfig,
    valuesEq, bytesEq, wordsEq, sourceOracle, sourceCompile, sourceFresh, sourceDistinct,
    nextConfigEq, nonempty, lastEq, resultEq⟩ := ClosSem.doInstall_nonType_parts values source last result run safe
  subst values
  cases valuesRel with
  | @cons _ targetByte _ _ byteRel tail =>
    cases tail with
    | @cons _ targetWord _ _ wordRel tail =>
      cases tail
      have targetBytes := valueToBytes_thm g1 l1 target.code byteValue _ bytes ⟨bytesEq, byteRel⟩
      have targetWords := valueToWords_thm g1 l1 target.code wordValue _ words ⟨wordsEq, wordRel⟩
      cases targetOracle : target.compileOracle 0 with
      | mk cfg2 progs =>
        have transformed := InstallSimulation.codeRel_stateRel_install g1 l1 source target config exps auxiliary bytes words nextConfig cfg2 progs
          ⟨invariant, states, sourceCompile, sourceOracle, targetOracle, nextConfigEq.symm, disjoint⟩
        obtain ⟨targetDisjoint, targetDistinct, converted, aux, g2, l2, nextCfg2, targetCompile,
          progsEq, targetNextEq, gGrowth, allowedGrowth, targetAllowedDisjoint, freshExps, callsEq,
          installedStates, installedInv, targetGrowth, locDisjoint⟩ := transformed
        subst progs
        have targetFresh : ∀ index ∈ aux.map Prod.fst, target.code.lookup index = none := by
          intro index member
          by_contra nonemptyLookup
          have inDomain : index ∈ target.code.domain := nonemptyLookup
          exact Set.disjoint_left.mp targetDisjoint inDomain member
        have expandedFresh : ∀ index arity exp, (index, arity, exp) ∈ aux → target.code.lookup index = none := by
          intro index arity exp member
          apply targetFresh index
          exact List.mem_map.mpr ⟨(index, arity, exp), member, rfl⟩
        have convertedNonempty : converted ≠ [] := by
          intro bad
          have len := calls_length exps g1 converted g2 callsEq
          cases exps with
          | nil => exact nonempty rfl
          | cons e es => simp [bad] at len
        have targetCompile' : target.compile cfg2 (converted, aux) = some (bytes, words, nextCfg2) := targetCompile
        have equalClock := stateRel_clock g1 l1 source target states
        have syntaxValid : syntaxOk exps := by
          have entry := (invariant.2.2.2.2 0).1
          simpa [sourceOracle] using entry
        have auxEmpty : auxiliary = [] := by
          have entry := (invariant.2.2.2.2 0).2
          simpa [sourceOracle] using entry
        have nextWell := stateValuesWellFormed_subg g1 l1 target.code source
          (target.code.updateListEq aux) g2 l2 ⟨sourceWell, targetGrowth, gGrowth, allowedGrowth⟩
        have targetRun : ClosSem.doInstall [targetByte, targetWord] target =
            (if source.clock = 0 then .err (.abort .timeoutError) else .val converted,
              {target with code := target.code.updateListEq aux, compileOracle := holShiftSeq 1 target.compileOracle, clock := target.clock - 1}) := by
          simp only [ClosSem.doInstall, targetBytes, targetWords, targetOracle, targetDistinct,
            targetCompile', targetNextEq, equalClock]
          by_cases z : target.clock = 0 <;> simp [z, convertedNonempty] <;> exact expandedFresh
        subst last
        refine ⟨exps, converted, aux, g2, l2,
          {target with code := target.code.updateListEq aux, compileOracle := holShiftSeq 1 target.compileOracle, clock := target.clock - 1},
          resultEq, targetRun, nonempty, syntaxValid, callsEq, ?_, ?_, ?_, targetGrowth,
          ?_, ?_, gGrowth, allowedGrowth, targetAllowedDisjoint, locDisjoint, freshExps, rfl⟩
        · exact (codeInvFacts g2 l2
            {source with code := source.code.updateListEq auxiliary, compileOracle := holShiftSeq 1 source.compileOracle}
            {target with code := target.code.updateListEq aux, compileOracle := holShiftSeq 1 target.compileOracle}
            installedInv).1
        · exact (codeInvFacts g2 l2
            {source with code := source.code.updateListEq auxiliary, compileOracle := holShiftSeq 1 source.compileOracle}
            {target with code := target.code.updateListEq aux, compileOracle := holShiftSeq 1 target.compileOracle}
            installedInv).2
        · simpa [auxEmpty, stateValuesWellFormed, HolFiniteMapExact.updateListEq] using nextWell
        · simpa using installedInv
        · have shifted := stateRel_withClock g2 l2
            {source with compileOracle := holShiftSeq 1 source.compileOracle, code := source.code.updateListEq auxiliary}
            {target with compileOracle := holShiftSeq 1 target.compileOracle, code := target.code.updateListEq aux}
            (source.clock - 1) installedStates
          simpa [← equalClock] using shifted
private theorem nonemptyLastRelated {A B : Type} [Nonempty A] [Nonempty B]
    (R : A → B → Prop) (xs : List A) (ys : List B) (related : List.Forall₂ R xs ys)
    (nonempty : xs ≠ []) : R (holLast xs) (holLast ys) := by
  induction related with
  | nil => exact False.elim (nonempty rfl)
  | @cons x y xs ys head tail ih =>
    cases tail with
    | nil => simpa [holLast] using head
    | @cons x2 y2 xs ys next rest =>
      simpa [holLast] using ih (by simp)

private theorem nonemptyLastMember {A : Type} [Nonempty A] (xs : List A) (nonempty : xs ≠ []) :
    holLast xs ∈ xs := by
  induction xs with
  | nil => exact False.elim (nonempty rfl)
  | cons x xs ih =>
    cases xs with
    | nil => simp [holLast]
    | cons y ys =>
      have h := ih (by simp)
      simp only [holLast, List.mem_cons]
      exact Or.inr (List.mem_cons.mp h)
private theorem installCase {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (argsIH : ExprMotive args env1 s0)
    (installIH : ∀ (es : List ClosLang.Exp) (state : ClosSem.State (NumSet × C) F),
      state.clock < s0.clock → ExprMotive es [] state) :
    ExprMotive [.op trace .install args] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, wellState,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases argsCompile : calls args g0 with
  | mk out next =>
    have argsSing : callsSingList args g0 = (out, next) := argsCompile
    simp only [calls, callsSingList, callsSing, argsSing, Prod.mk.injEq] at compileRun
    obtain ⟨rfl, rfl⟩ := compileRun
    have argsAnnotations : everyFnLocationSome args := by
      simpa [everyFnLocationSome, fnLocationSomeExp] using annotations
    have argsVars : everyFnVarsNone args := by simpa [everyFnVarsNone, fnVarsNoneExp] using varsNone
    have argsDistinct : (codeLocations args).Nodup := by simpa [codeLocations, codeLocationsExp] using distinct
    have argsFresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations args})
        {n | n ∈ g0.2.map Prod.fst} := by simpa [codeLocations, codeLocationsExp] using fresh
    have argsBound : Set.Subset (Set.diff {n | n ∈ codeLocations args} (sptDomain next.1)) l1 := by
      intro key hkey
      apply allowed
      rw [locations]
      change (key ∈ codeLocations args ∧ ¬ sptDomain next.1 key) at hkey
      change (key ∈ codeLocations [.op trace .install args] ∧ ¬ sptDomain next.1 key)
      exact ⟨by simpa [codeLocations, codeLocationsExp] using hkey.1, hkey.2⟩
    have argsEnv := opArgsEnvRel (valueRel g1 l1 t0.code) env1 env2 trace .install out
      (by simpa using envRelated)
    have nextWell := calls_wellFormed args g0 out next
      ⟨argsCompile, argsDistinct, fun key h => Set.disjoint_left.mp argsFresh h.1 h.2,
        argsAnnotations, initialWell⟩
    cases argsRun : ClosSem.evaluate args env1 s0 with
    | mk argsResult middle =>
      have argsSafe : argsResult ≠ .err (.abort .typeError) := by
        intro bad
        subst argsResult
        simp [ClosSem.evaluate, argsRun] at sourceRun
        obtain ⟨rfl, rfl⟩ := sourceRun
        exact safe rfl
      have argsSim := argsIH (args, env1, s0) g0 next env2 t0 out argsResult middle
        ({n | n ∈ codeLocations args} \ sptDomain next.1) l1 g1
        ⟨rfl, argsRun, argsSafe, argsCompile, invariant, argsAnnotations, argsVars, envWell, wellState,
          initialWell, argsDistinct, argsFresh, rfl, growth, argsBound, disjoint, well,
          argsEnv, states, included⟩
      obtain ⟨ck, targetArgs, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
        argsWell, targetRun, states2, argsRelated⟩ := argsSim
      have fixedSource : ClosSem.fixClock s0 (argsResult, middle) = (argsResult, middle) := by
        rw [← argsRun]
        exact ClosSem.fixClock_evaluate args env1 s0
      have fixedTarget : ClosSem.fixClock {t0 with clock := t0.clock + ck} (targetArgs, t) = (targetArgs, t) := by
        rw [← targetRun]
        exact ClosSem.fixClock_evaluate out env2 {t0 with clock := t0.clock + ck}
      cases argsResult with
      | err error =>
        cases targetArgs with
        | val values => exact False.elim argsRelated
        | err targetError =>
          simp only [ClosSem.evaluate, argsRun, fixedSource, Prod.mk.injEq] at sourceRun
          obtain ⟨rfl, rfl⟩ := sourceRun
          refine ⟨ck, .err targetError, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2,
            disjoint2, argsWell, ?_, states2, argsRelated⟩
          simp only [ClosSem.evaluate, targetRun, fixedTarget]
      | val values =>
        cases targetArgs with
        | err error => exact False.elim argsRelated
        | val targetValues =>
          change List.Forall₂ (valueRel g2 l2 t.code) values targetValues at argsRelated
          cases installRun : ClosSem.doInstall values.reverse middle with
          | mk installResult installed =>
            have installSafe : installResult ≠ .err (.abort .typeError) := by
              intro bad
              subst installResult
              rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun] at sourceRun
              simp only at sourceRun
              rw [installRun] at sourceRun
              simp only [Prod.mk.injEq] at sourceRun
              obtain ⟨rfl, rfl⟩ := sourceRun
              exact safe rfl
            obtain ⟨exps, converted, aux, g3, l3, targetInstalled, resultEq, targetInstallRun,
              nonempty, syntaxValid, callsEq, installedWell, installedIncluded, installedStateWell,
              codeGrowth, installedInv, installedStates, gGrowth, lGrowth, installedDisjoint,
              locationDisjoint, locationBound, targetCode⟩ :=
              installRelated g2 l2 middle t values.reverse targetValues.reverse installResult installed
                inv2 states2 disjoint2 stateWell2 (List.rel_reverse argsRelated) installRun installSafe
            by_cases zero : middle.clock = 0
            · simp only [zero, if_true] at resultEq targetInstallRun
              subst installResult
              rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun] at sourceRun
              simp only at sourceRun
              rw [installRun] at sourceRun
              simp only [Prod.mk.injEq] at sourceRun
              obtain ⟨rfl, rfl⟩ := sourceRun
              refine ⟨ck, .err (.abort .timeoutError), targetInstalled, g3, l3, installedInv, installedStateWell,
                stateExtends_trans g1 g2 g3 growth2 gGrowth, installedWell, Set.Subset.trans allowed2 lGrowth,
                installedDisjoint, by simp [everyResult, everyErrorResult], ?_, installedStates, by simp [resultRel, excRel]⟩
              rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetRun]
              simp only
              rw [targetInstallRun]
            · simp only [zero, if_false] at resultEq targetInstallRun
              subst installResult
              have clockFacts := ClosSem.doInstall_success_clock values.reverse middle installed exps installRun
              have middleClock := ClosSem.evaluate_clock_source.1 args env1 s0 (.val values) middle argsRun
              have less : installed.clock < s0.clock := by omega
              have freshCode : Disjoint (Set.image Nat.succ {x | x ∈ codeLocations exps})
                  {x | x ∈ g2.2.map Prod.fst} := by
                apply Set.disjoint_left.mpr
                intro key newLoc oldCode
                obtain ⟨entry, member, entryKey⟩ := List.mem_map.mp oldCode
                obtain ⟨label, value⟩ := entry
                simp only at entryKey
                subst label
                have lookup := holALookup_of_distinct_member g2.2 key value ⟨well2.2, member⟩
                have present : key ∈ t.code.domain := by
                  change t.code.lookup key ≠ none
                  rw [(codeInvFacts g2 l2 middle t inv2).2 key value lookup]
                  simp
                exact Set.disjoint_left.mp locationDisjoint newLoc present
              cases bodyRun : ClosSem.evaluate exps [] installed with
              | mk bodyResult last =>
                have bodySafe : bodyResult ≠ .err (.abort .typeError) := by
                  intro bad
                  subst bodyResult
                  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun] at sourceRun
                  simp only at sourceRun
                  rw [installRun] at sourceRun
                  simp only at sourceRun
                  rw [bodyRun] at sourceRun
                  simp only [Prod.mk.injEq] at sourceRun
                  obtain ⟨rfl, rfl⟩ := sourceRun
                  exact safe rfl
                have bodySim := installIH exps installed less (exps, [], installed) g2 g3 [] targetInstalled
                  converted bodyResult last ({x | x ∈ codeLocations exps} \ sptDomain g3.1) l3 g3
                  ⟨rfl, bodyRun, bodySafe, callsEq, installedInv, syntaxValid.1, syntaxValid.2.1,
                    by simp, installedStateWell, well2, syntaxValid.2.2, freshCode, rfl,
                    stateExtends_refl g3 installedWell.2, locationBound, installedDisjoint, installedWell,
                    by simp [envRel], installedStates, installedIncluded⟩
                obtain ⟨ck2, bodyRes, t2, g4, l4, inv4, stateWell4, growth4, well4, allowed4, disjoint4,
                  bodyWell, bodyTargetRun, states4, bodyRelated⟩ := bodySim
                have shiftedArgs := ClosProps.ClockShiftPort.evaluate_addClock t
                  {t0 with clock := t0.clock + ck} (.val targetValues) out env2 ⟨targetRun, by simp⟩ ck2
                have shiftedArgsRun : ClosSem.evaluate out env2 {t0 with clock := t0.clock + (ck + ck2)} =
                    (.val targetValues, {t with clock := t.clock + ck2}) := by
                  simpa only [Nat.add_assoc] using shiftedArgs
                have shiftedInstall := ClosSem.doInstall_success_addClock targetValues.reverse t targetInstalled
                  converted ck2 targetInstallRun
                cases bodyResult with
                | err error =>
                  cases bodyRes with
                  | val values => exact False.elim bodyRelated
                  | err targetError =>
                    have sourceWhole : ClosSem.evaluate [.op trace .install args] env1 s0 = (.err error, last) := by
                      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun]
                      simp only
                      rw [installRun]
                      simp only
                      rw [bodyRun]
                    have sourceEq := sourceRun.symm.trans sourceWhole
                    simp only [Prod.mk.injEq] at sourceEq
                    obtain ⟨rfl, rfl⟩ := sourceEq
                    refine ⟨ck + ck2, .err targetError, t2, g4, l4, inv4, stateWell4,
                      stateExtends_trans g1 g3 g4 (stateExtends_trans g1 g2 g3 growth2 gGrowth) growth4,
                      well4, Set.Subset.trans (Set.Subset.trans allowed2 lGrowth) allowed4,
                      disjoint4, bodyWell, ?_, states4, bodyRelated⟩
                    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, shiftedArgsRun]
                    simp only
                    rw [shiftedInstall]
                    simp only
                    rw [bodyTargetRun]
                | val values =>
                  cases bodyRes with
                  | err error => exact False.elim bodyRelated
                  | val targetValues' =>
                    change List.Forall₂ (valueRel g4 l4 t2.code) values targetValues' at bodyRelated
                    have valueNonempty : values ≠ [] := by
                      intro bad
                      have length := ClosProps.evaluateImpLength exps [] installed last values bodyRun
                      cases exps with
                      | nil => exact nonempty rfl
                      | cons e es => simp [bad] at length
                    let : Nonempty ClosSem.Value := ⟨ClosSem.unitValue⟩
                    have lastWell : valueWellFormed g4 l4 t2.code (ClosSem.lastValue values) := by
                      apply bodyWell
                      exact nonemptyLastMember values valueNonempty
                    have lastRelated : valueRel g4 l4 t2.code (ClosSem.lastValue values)
                        (ClosSem.lastValue targetValues') :=
                      nonemptyLastRelated (valueRel g4 l4 t2.code) values targetValues' bodyRelated valueNonempty
                    have sourceWhole : ClosSem.evaluate [.op trace .install args] env1 s0 =
                        (.val [ClosSem.lastValue values], last) := by
                      rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun]
                      simp only
                      rw [installRun]
                      simp only
                      rw [bodyRun]
                    have sourceEq := sourceRun.symm.trans sourceWhole
                    simp only [Prod.mk.injEq] at sourceEq
                    obtain ⟨rfl, rfl⟩ := sourceEq
                    refine ⟨ck + ck2, .val [ClosSem.lastValue targetValues'], t2, g4, l4, inv4, stateWell4,
                      stateExtends_trans g1 g3 g4 (stateExtends_trans g1 g2 g3 growth2 gGrowth) growth4,
                      well4, Set.Subset.trans (Set.Subset.trans allowed2 lGrowth) allowed4,
                      disjoint4, ?_, ?_, states4, ?_⟩
                    · simpa [everyResult] using lastWell
                    · rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, shiftedArgsRun]
                      simp only
                      rw [shiftedInstall]
                      simp only
                      rw [bodyTargetRun]
                    · exact .cons lastRelated .nil
private theorem letrecCapturedEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (names : List Flapjack.Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp)
    (related : envRel R env1 env2 0 [(0, .letrec names (some loc) none fns body)]) :
    envRel R env1 env2 fns.length fns := by
  unfold envRel at related ⊢
  by_cases same : env1.length = env2.length
  · simpa only [same, ↓reduceIte] using related
  · simp only [same, ↓reduceIte] at related ⊢
    intro x ⟨fn, member, used⟩
    apply related x
    refine ⟨(0, .letrec names (some loc) none fns body), by simp, ?_⟩
    simp only [Nat.zero_add, freeVar, freeVars, freeVarExp, or_false]
    apply Or.inl
    apply (freeVarFuns_exists x fns.length fns).mpr
    refine ⟨fn, member, ?_⟩
    simpa [freeVar, freeVars, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using used

private theorem letrecBodyTailEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (names : List Flapjack.Basis.Pure.MlString.MlString) (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp)
    (related : envRel R env1 env2 0 [(0, .letrec names (some loc) none fns body)]) :
    envRel R env1 env2 fns.length [(0, body)] := by
  unfold envRel at related ⊢
  by_cases same : env1.length = env2.length
  · simpa only [same, ↓reduceIte] using related
  · simp only [same, ↓reduceIte] at related ⊢
    intro x ⟨fn, member, used⟩
    simp only [List.mem_singleton] at member
    subst fn
    apply related x
    refine ⟨(0, .letrec names (some loc) none fns body), by simp, ?_⟩
    simp only [Nat.zero_add, freeVar, freeVars, freeVarExp, or_false] at used ⊢
    exact Or.inr (by simpa [Nat.add_comm] using used)
private theorem recursiveClosuresRelated (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (env1 env2 : List ClosSem.Value)
    (group : recClosureRel g allowed code loc fns1 fns2)
    (captured : envRel (valueRel g allowed code) env1 env2 fns2.length fns2) :
    List.Forall₂ (valueRel g allowed code)
      ((List.range fns1.length).map (fun i => ClosSem.Value.recclosure (some loc) [] env1 fns1 i))
      ((List.range fns2.length).map (fun i => ClosSem.Value.recclosure (some loc) [] env2 fns2 i)) := by
  have arities := recClosureRel_arities g allowed code loc fns1 fns2 group
  have same : fns1.length = fns2.length := by
    have lengths := congrArg List.length arities
    simpa using lengths.symm
  rw [← same]
  generalize List.range fns1.length = indexes
  induction indexes with
  | nil => exact .nil
  | cons i is ih =>
    apply List.Forall₂.cons
    · apply ((valueRel_sourceEquations g allowed code).2.2 _ _ _ _ _ _).mpr
      exact ⟨loc, [], env2, fns2, group, rfl, rfl, .nil, captured⟩
    · exact ih

private theorem recursiveClosuresWellFormed (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (fns1 fns2 : List (Nat × ClosLang.Exp)) (env1 : List ClosSem.Value)
    (group : recClosureRel g allowed code loc fns1 fns2)
    (envWell : ∀ value ∈ env1, valueWellFormed g allowed code value) :
    ∀ value ∈ (List.range fns1.length).map (fun i => ClosSem.Value.recclosure (some loc) [] env1 fns1 i),
      valueWellFormed g allowed code value := by
  intro value member
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp member
  change valueWellFormed g (fun x => x ∈ allowed) code (.recclosure (some loc) [] env1 fns1 i)
  rw [valueWellFormed.eq_4]
  exact ⟨by simp, envWell, ⟨fns2, group⟩⟩

private theorem letrecBodyEnvRel (g : State) (allowed : Set Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (loc : Nat)
    (names : List Flapjack.Basis.Pure.MlString.MlString) (fns1 fns2 : List (Nat × ClosLang.Exp))
    (body : ClosLang.Exp) (env1 env2 : List ClosSem.Value)
    (group : recClosureRel g allowed code loc fns1 fns2)
    (related : envRel (valueRel g allowed code) env1 env2 0 [(0, .letrec names (some loc) none fns2 body)]) :
    envRel (valueRel g allowed code)
      (((List.range fns1.length).map (fun i => ClosSem.Value.recclosure (some loc) [] env1 fns1 i)) ++ env1)
      (((List.range fns2.length).map (fun i => ClosSem.Value.recclosure (some loc) [] env2 fns2 i)) ++ env2)
      0 [(0, body)] := by
  have arities := recClosureRel_arities g allowed code loc fns1 fns2 group
  have same : fns1.length = fns2.length := by
    have lengths := congrArg List.length arities
    simpa using lengths.symm
  have captured := letrecCapturedEnvRel (valueRel g allowed code) env1 env2 names loc fns2 body related
  have bodyTail := letrecBodyTailEnvRel (valueRel g allowed code) env1 env2 names loc fns2 body related
  have recursive := recursiveClosuresRelated g allowed code loc fns1 fns2 env1 env2 group captured
  apply envRel_drop (valueRel g allowed code) fns2.length _ _ [(0, body)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [same] using bodyTail
  · simpa [same] using recursive
  · simp [same]
  · simp
private theorem letrecInitialFacts (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (g0 : State)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (vars : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.letrec names (some loc) none fns body]})
      {n | n ∈ g0.2.map Prod.fst}) (well : wellFormed g0) :
    recClosureWellFormed loc fns ∧
    (∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations (fns.map Prod.snd)} ∧
      label ∈ g0.2.map Prod.fst)) ∧
    (∀ label, ¬ (label ∈ (List.range fns.length).map (fun i => 2 * i + loc + 1) ∧
      label ∈ g0.2.map Prod.fst)) ∧
    (∀ label ∈ (List.range fns.length).map (fun i => 2 * i + loc), ¬ sptDomain g0.1 label) := by
  have allLocations : (codeLocations (fns.map Prod.snd) ++
      (List.range fns.length).map (fun i => 2 * i + loc) ++ codeLocations [body]).Nodup := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, Nat.add_comm] using distinct
  have ⟨groupDistinct, _, _⟩ := List.nodup_append.mp allLocations
  have ⟨bodyDistinct, _, apart⟩ := List.nodup_append.mp groupDistinct
  have ann : everyFnLocationSome (fns.map Prod.snd) := by
    simp only [everyFnLocationSome, fnLocationSomeExp] at locations
    exact (fnLocationSomeFuns_eq_map fns).mp locations.1.2.1
  have noVars : everyFnVarsNone (fns.map Prod.snd) := by
    simp only [everyFnVarsNone, fnVarsNoneExp] at vars
    exact (fnVarsNoneFuns_eq_map fns).mp vars.1.2.1
  have bodyApart : ∀ n, ¬ (n ∈ (List.range fns.length).map (fun i => 2 * i + loc) ∧
      n ∈ codeLocations (fns.map Prod.snd)) := by
    intro n ⟨slot, inBody⟩
    exact apart n inBody n slot rfl
  have allFresh : ∀ n, n ∈ codeLocations (fns.map Prod.snd) ++
      (List.range fns.length).map (fun i => 2 * i + loc) ++ codeLocations [body] →
      n + 1 ∉ g0.2.map Prod.fst := by
    intro n member present
    apply Set.disjoint_left.mp fresh
    · refine ⟨n, ?_, rfl⟩
      simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, Nat.add_comm] using member
    · exact present
  refine ⟨⟨ann, noVars, bodyApart, bodyDistinct⟩, ?_, ?_, ?_⟩
  · intro label ⟨⟨n, member, eq⟩, present⟩
    have := allFresh n (List.mem_append_left _ (List.mem_append_left _ member))
    exact this (by simpa [← eq] using present)
  · intro label ⟨member, present⟩
    obtain ⟨i, range, eq⟩ := List.mem_map.mp member
    have item : 2 * i + loc ∈ (List.range fns.length).map (fun j => 2 * j + loc) :=
      List.mem_map.mpr ⟨i, range, rfl⟩
    have := allFresh (2 * i + loc) (List.mem_append_left _ (List.mem_append_right _ item))
    exact this (by simpa [← eq] using present)
  · intro label member present
    have absent := allFresh label (List.mem_append_left _ (List.mem_append_right _ member))
    apply absent
    have image : label + 1 ∈ Set.image Nat.succ (sptDomain g0.1) := ⟨label, present, rfl⟩
    rw [← well.1] at image
    exact image
private theorem letrecClosedGuard (fns : List (Nat × ClosLang.Exp)) (bodies : List ClosLang.Exp)
    (sameLength : fns.length = bodies.length) :
    (fns.zip bodies).all (fun (fn, body) =>
      closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 body)) = true ↔
    List.Forall₂ (fun fn body => ∀ v, DbVars.hasVar v (free [body]).2 = true → v < fn.1) fns bodies := by
  induction fns generalizing bodies with
  | nil =>
    cases bodies with
    | nil => simp
    | cons head tail => simp at sameLength
  | cons fn rest ih =>
    cases bodies with
    | nil => simp at sameLength
    | cons body bodies =>
      have len : rest.length = bodies.length := by simpa using sameLength
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true]
      rw [closedFn, ih bodies len]
      constructor
      · rintro ⟨head, tail⟩
        exact .cons head tail
      · intro rel
        cases rel with
        | cons head tail => exact ⟨head, tail⟩
private theorem letrecLocationBounds (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body out : ClosLang.Exp) (middle final : State)
    (allowed : Set Nat)
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (run : calls [body] middle = ([out], final))
    (wholeBound : Set.Subset
      (Set.diff {n | n ∈ codeLocations [.letrec names (some loc) none fns body]} (sptDomain final.1)) allowed) :
    Set.Subset (Set.diff {n | n ∈ codeLocations (fns.map Prod.snd)} (sptDomain middle.1)) allowed ∧
    Set.Subset (Set.diff {n | n ∈ (List.range fns.length).map (fun i => 2 * i + loc)}
      (sptDomain middle.1)) allowed := by
  have allLocations : ((codeLocations (fns.map Prod.snd) ++
      (List.range fns.length).map (fun i => 2 * i + loc)) ++ codeLocations [body]).Nodup := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, Nat.add_comm] using distinct
  have apart := (List.nodup_append.mp allLocations).2.2
  have keep : ∀ key, key ∈ codeLocations (fns.map Prod.snd) ++
      (List.range fns.length).map (fun i => 2 * i + loc) → ¬ sptDomain middle.1 key →
      ¬ sptDomain final.1 key := by
    intro key member absent present
    rcases calls_domainLocations [body] middle [out] final run present with old | bodyMember
    · exact absent old
    · exact apart key member key bodyMember rfl
  constructor
  · intro key ⟨member, absent⟩
    apply wholeBound
    refine ⟨?_, keep key (List.mem_append_left _ member) absent⟩
    have part := List.mem_append_left (codeLocations [body])
      (List.mem_append_left ((List.range fns.length).map (fun i => 2 * i + loc)) member)
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, Nat.add_comm] using part
  · intro key ⟨member, absent⟩
    apply wholeBound
    refine ⟨?_, keep key (List.mem_append_right _ member) absent⟩
    have part := List.mem_append_left (codeLocations [body])
      (List.mem_append_right (codeLocations (fns.map Prod.snd)) member)
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, Nat.add_comm] using part
private theorem letrecOrdinaryRelation (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body bodyOut : ClosLang.Exp)
    (fastEs es : List ClosLang.Exp) (g0 fastState groupState final g1 : State)
    (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (vars : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.letrec names (some loc) none fns body]})
      {n | n ∈ g0.2.map Prod.fst}) (well : wellFormed g0)
    (fastRun : calls (fns.map Prod.snd) (insertEachSource loc fns.length g0) = (fastEs, fastState))
    (notClosed : (fns.zip fastEs).all (fun (fn, converted) =>
      closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 converted)) ≠ true)
    (groupRun : calls (fns.map Prod.snd) g0 = (es, groupState))
    (bodyRun : calls [body] groupState = ([bodyOut], final))
    (bodyGrowth : stateExtends groupState final) (growth : stateExtends final g1)
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.letrec names (some loc) none fns body]}
      (sptDomain final.1)) allowed) (included : codeIncludes final.2 code) :
    recClosureRel g1 allowed code loc fns ((fns.map Prod.fst).zip es) := by
  classical
  obtain ⟨groupWell, bodyFresh, slotFresh, initialAbsent⟩ :=
    letrecInitialFacts names loc fns body g0 locations vars distinct fresh well
  obtain ⟨bodyBound, slotBound⟩ := letrecLocationBounds names loc fns body bodyOut groupState final allowed distinct bodyRun bound
  have absent : ∀ label ∈ (List.range fns.length).map (fun i => 2 * i + loc), ¬ sptDomain groupState.1 label := by
    intro label member present
    rcases calls_domainLocations (fns.map Prod.snd) g0 es groupState groupRun present with old | new
    · exact initialAbsent label member old
    · exact groupWell.2.2.1 label ⟨member, new⟩
  have slotsAllowed : Set.Subset {n | n ∈ (List.range fns.length).map (fun i => 2 * i + loc)} allowed := by
    intro label member
    exact slotBound ⟨member, absent label member⟩
  have fastLength : fns.length = fastEs.length := by
    have len := calls_length (fns.map Prod.snd) (insertEachSource loc fns.length g0) fastEs fastState fastRun
    simpa using len.symm
  have guardFalse : ¬ List.Forall₂
      (fun fn converted => ∀ n, DbVars.hasVar n (free [converted]).2 = true → n < fn.1) fns fastEs := by
    intro guard
    exact notClosed ((letrecClosedGuard fns fastEs fastLength).mpr guard)
  have groupGrowth := stateExtends_trans groupState final g1 bodyGrowth growth
  have groupIncluded := codeIncludes_subg groupState final code bodyGrowth included
  unfold recClosureRel
  refine ⟨g0, groupWell, well, bodyFresh, slotFresh, ?_⟩
  change (if List.Forall₂ _ fns (calls (fns.map Prod.snd) (insertEachSource loc fns.length g0)).1 then _ else _)
  simp only [fastRun, guardFalse, ↓reduceIte, groupRun]
  exact ⟨True.intro, groupGrowth, bodyBound, slotsAllowed, groupIncluded⟩
private theorem letrecOptimizedRelation (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body bodyOut : ClosLang.Exp)
    (es : List ClosLang.Exp) (g0 fastState final g1 : State)
    (allowed : Set Nat) (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp))
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (vars : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.letrec names (some loc) none fns body]})
      {n | n ∈ g0.2.map Prod.fst}) (well : wellFormed g0)
    (fastRun : calls (fns.map Prod.snd) (insertEachSource loc fns.length g0) = (es, fastState))
    (isClosed : (fns.zip es).all (fun (fn, converted) =>
      closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 converted)) = true)
    (bodyRun : calls [body] (codeListSource loc ((fns.map Prod.fst).zip es) fastState) = ([bodyOut], final))
    (bodyGrowth : stateExtends (codeListSource loc ((fns.map Prod.fst).zip es) fastState) final)
    (growth : stateExtends final g1)
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.letrec names (some loc) none fns body]}
      (sptDomain final.1)) allowed) (included : codeIncludes final.2 code) :
    recClosureRel g1 allowed code loc fns (callsListSource .none 1 loc fns) := by
  classical
  obtain ⟨groupWell, bodyFresh, slotFresh, _⟩ :=
    letrecInitialFacts names loc fns body g0 locations vars distinct fresh well
  have bounds := letrecLocationBounds names loc fns body bodyOut
    (codeListSource loc ((fns.map Prod.fst).zip es) fastState) final allowed distinct bodyRun bound
  have bodyBound : Set.Subset (Set.diff {n | n ∈ codeLocations (fns.map Prod.snd)} (sptDomain fastState.1)) allowed := by
    simpa [codeListSource_fst] using bounds.1
  have fastLength : fns.length = es.length := by
    have len := calls_length (fns.map Prod.snd) (insertEachSource loc fns.length g0) es fastState fastRun
    simpa using len.symm
  have guard := (letrecClosedGuard fns es fastLength).mp isClosed
  have groupGrowth := stateExtends_trans _ final g1 bodyGrowth growth
  have groupIncluded := codeIncludes_subg _ final code bodyGrowth included
  unfold recClosureRel
  refine ⟨g0, groupWell, well, bodyFresh, slotFresh, ?_⟩
  change (if List.Forall₂ _ fns (calls (fns.map Prod.snd) (insertEachSource loc fns.length g0)).1 then _ else _)
  simp only [fastRun, guard, ↓reduceIte]
  exact ⟨⟨.none, 1, rfl⟩, groupGrowth, bodyBound, groupIncluded⟩
private theorem optimizedGroupWellFormed (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (g0 fastState : State) (es : List ClosLang.Exp)
    (groupWell : recClosureWellFormed loc fns) (initialWell : wellFormed g0)
    (freshCode : ∀ label, ¬ (label ∈ Set.image Nat.succ {k | k ∈ codeLocations (fns.map Prod.snd)} ∧
      label ∈ g0.2.map Prod.fst))
    (freshSlots : ∀ label, ¬ (label ∈ (List.range fns.length).map (fun i => 2 * i + loc + 1) ∧
      label ∈ g0.2.map Prod.fst))
    (run : calls (fns.map Prod.snd) (insertEachSource loc fns.length g0) = (es, fastState)) :
    wellFormed (codeListSource loc ((fns.map Prod.fst).zip es) fastState) := by
  let replacement : List (Nat × Nat × ClosLang.Exp) := []
  obtain ⟨added, suffix, rerun⟩ := rerunOptimizedGroup loc fns.length g0 fastState replacement (fns.map Prod.snd) es run
  have oldCode : fastState.2 = added ++ g0.2 := by simpa [insertEach_snd] using suffix
  have len : es.length = fns.length := by
    simpa using calls_length (fns.map Prod.snd) (insertEachSource loc fns.length g0) es fastState run
  obtain ⟨initialWell', freshCode'⟩ := optimizedInitialFacts loc fns g0 replacement groupWell initialWell freshCode freshSlots
  have rerunWell := calls_wellFormed (fns.map Prod.snd) (insertWithCode replacement loc fns.length g0) es
    (fastState.1, added ++ (insertWithCode replacement loc fns.length g0).2)
    ⟨rerun, groupWell.2.2.2, freshCode', groupWell.1, initialWell'⟩
  have labelsPerm : (((codeListSource loc ((fns.map Prod.fst).zip es) fastState).2).map Prod.fst).Perm
      ((added ++ (insertWithCode replacement loc fns.length g0).2).map Prod.fst) := by
    rw [codeListSource_labels, oldCode, List.map_append, List.map_append, insertWithCode_labels]
    simp only [List.length_zip, List.length_map, len, Nat.min_self]
    let slots := ((List.range fns.length).map (fun i => loc + i * 2 + 1)).reverse
    let newlyAdded := added.map Prod.fst
    let old := g0.2.map Prod.fst
    have commute : (slots ++ newlyAdded).Perm (newlyAdded ++ slots) := List.perm_append_comm
    simpa only [slots, newlyAdded, old, List.append_assoc] using commute.append_right old
  constructor
  · apply Set.ext
    intro key
    constructor
    · intro member
      have target : key ∈ (added ++ (insertWithCode replacement loc fns.length g0).2).map Prod.fst :=
        labelsPerm.mem_iff.mp member
      change key ∈ {label | label ∈ (added ++ (insertWithCode replacement loc fns.length g0).2).map Prod.fst} at target
      rw [rerunWell.1] at target
      simpa [codeListSource_fst] using target
    · intro member
      have target : key ∈ Set.image Nat.succ (sptDomain fastState.1) := by
        simpa [codeListSource_fst] using member
      rw [← rerunWell.1] at target
      exact labelsPerm.mem_iff.mpr target
  · exact labelsPerm.nodup_iff.mpr rerunWell.2
private theorem letrecBodyFresh (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (g0 groupState : State)
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.letrec names (some loc) none fns body]})
      {n | n ∈ g0.2.map Prod.fst})
    (origin : ∀ label ∈ groupState.2.map Prod.fst,
      label ∈ g0.2.map Prod.fst ∨ ∃ n, n ∈ codeLocations (fns.map Prod.snd) ++
        (List.range fns.length).map (fun i => 2 * i + loc) ∧ label = Nat.succ n) :
    ∀ label, ¬ (label ∈ Set.image Nat.succ {n | n ∈ codeLocations [body]} ∧
      label ∈ groupState.2.map Prod.fst) := by
  have allLocations : ((codeLocations (fns.map Prod.snd) ++
      (List.range fns.length).map (fun i => 2 * i + loc)) ++ codeLocations [body]).Nodup := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, Nat.add_comm] using distinct
  have apart := (List.nodup_append.mp allLocations).2.2
  intro label ⟨⟨n, inBody, labelEq⟩, present⟩
  rcases origin label present with old | ⟨groupLoc, inGroup, groupEq⟩
  · apply Set.disjoint_left.mp fresh
    · refine ⟨n, ?_, labelEq⟩
      have part := List.mem_append_right
        (codeLocations (fns.map Prod.snd) ++ (List.range fns.length).map (fun i => 2 * i + loc)) inBody
      simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, Nat.add_comm] using part
    · exact old
  · have eq : groupLoc = n := Nat.succ.inj (groupEq.symm.trans labelEq.symm)
    exact apart groupLoc inGroup n inBody eq

private theorem letrecOrdinaryLabelOrigin (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (g0 groupState : State) (es : List ClosLang.Exp)
    (run : calls (fns.map Prod.snd) g0 = (es, groupState)) :
    ∀ label ∈ groupState.2.map Prod.fst,
      label ∈ g0.2.map Prod.fst ∨ ∃ n, n ∈ codeLocations (fns.map Prod.snd) ++
        (List.range fns.length).map (fun i => 2 * i + loc) ∧ label = Nat.succ n := by
  have origins := calls_addSucc_codeLocations (fns.map Prod.snd) g0 es groupState run
  intro label member
  rcases origins member with old | ⟨n, inBody, eq⟩
  · exact Or.inl old
  · exact Or.inr ⟨n, List.mem_append_left _ inBody, eq.symm⟩

private theorem letrecOptimizedLabelOrigin (loc : Nat) (fns : List (Nat × ClosLang.Exp))
    (g0 fastState : State) (es : List ClosLang.Exp)
    (run : calls (fns.map Prod.snd) (insertEachSource loc fns.length g0) = (es, fastState)) :
    ∀ label ∈ (codeListSource loc ((fns.map Prod.fst).zip es) fastState).2.map Prod.fst,
      label ∈ g0.2.map Prod.fst ∨ ∃ n, n ∈ codeLocations (fns.map Prod.snd) ++
        (List.range fns.length).map (fun i => 2 * i + loc) ∧ label = Nat.succ n := by
  have len : es.length = fns.length := by
    simpa using calls_length (fns.map Prod.snd) (insertEachSource loc fns.length g0) es fastState run
  have origins := calls_addSucc_codeLocations (fns.map Prod.snd) (insertEachSource loc fns.length g0) es fastState run
  intro label member
  rw [codeListSource_labels] at member
  simp only [List.length_zip, List.length_map, len, Nat.min_self, List.mem_append, List.mem_reverse] at member
  rcases member with generated | old
  · obtain ⟨i, bound, eq⟩ := List.mem_map.mp generated
    right
    refine ⟨2 * i + loc, List.mem_append_right _ (List.mem_map.mpr ⟨i, bound, rfl⟩), ?_⟩
    omega
  · rcases origins old with original | ⟨n, inBody, eq⟩
    · left
      simpa [insertEach_snd] using original
    · exact Or.inr ⟨n, List.mem_append_left _ inBody, eq.symm⟩
private theorem letrecBodyCompilationFacts (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (body bodyOut : ClosLang.Exp)
    (g0 groupState final : State) (allowed : Set Nat)
    (locations : everyFnLocationSome [.letrec names (some loc) none fns body])
    (vars : everyFnVarsNone [.letrec names (some loc) none fns body])
    (distinct : (codeLocations [.letrec names (some loc) none fns body]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.letrec names (some loc) none fns body]})
      {n | n ∈ g0.2.map Prod.fst})
    (origin : ∀ label ∈ groupState.2.map Prod.fst,
      label ∈ g0.2.map Prod.fst ∨ ∃ n, n ∈ codeLocations (fns.map Prod.snd) ++
        (List.range fns.length).map (fun i => 2 * i + loc) ∧ label = Nat.succ n)
    (groupWell : wellFormed groupState) (bodyRun : calls [body] groupState = ([bodyOut], final))
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.letrec names (some loc) none fns body]}
      (sptDomain final.1)) allowed) :
    stateExtends groupState final ∧ wellFormed final ∧ everyFnLocationSome [body] ∧
      everyFnVarsNone [body] ∧ (codeLocations [body]).Nodup ∧
      Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [body]}) {n | n ∈ groupState.2.map Prod.fst} ∧
      Set.Subset (Set.diff {n | n ∈ codeLocations [body]} (sptDomain final.1)) allowed := by
  have allLocations : ((codeLocations (fns.map Prod.snd) ++
      (List.range fns.length).map (fun i => 2 * i + loc)) ++ codeLocations [body]).Nodup := by
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, Nat.add_comm] using distinct
  have bodyDistinct := (List.nodup_append.mp allLocations).2.1
  have bodyFresh := letrecBodyFresh names loc fns body g0 groupState distinct fresh origin
  have annotations : everyFnLocationSome [body] := by
    simp only [everyFnLocationSome, fnLocationSomeExp] at locations ⊢
    exact ⟨locations.1.2.2, trivial⟩
  have noVars : everyFnVarsNone [body] := by
    simp only [everyFnVarsNone, fnVarsNoneExp] at vars ⊢
    exact ⟨vars.1.2.2, trivial⟩
  have bodyGrowth := calls_subg [body] groupState [bodyOut] final
    ⟨bodyRun, groupWell.2, bodyDistinct, bodyFresh⟩
  have finalWell := calls_wellFormed [body] groupState [bodyOut] final
    ⟨bodyRun, bodyDistinct, bodyFresh, annotations, groupWell⟩
  refine ⟨bodyGrowth, finalWell, annotations, noVars, bodyDistinct, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro key x y
    exact bodyFresh key ⟨x, y⟩
  · intro key ⟨member, absent⟩
    apply bound
    refine ⟨?_, absent⟩
    have part := List.mem_append_right (codeLocations (fns.map Prod.snd) ++
      (List.range fns.length).map (fun i => 2 * i + loc)) member
    simpa [codeLocations, codeLocationsExp, codeLocationsFuns_map, Nat.add_comm] using part
private theorem finishLetrec {C F : Type} (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Nat) (fns1 fns2 : List (Nat × ClosLang.Exp)) (body bodyOut : ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (s0 s : ClosSem.State (NumSet × C) F) (t0 : ClosSem.State C F)
    (groupState final g1 : State) (l1 : Set Nat) (res : Result (List ClosSem.Value) ClosSem.Value)
    (bodyIH : ∀ env, ExprMotive [body] env s0)
    (validArity : fns1.all (fun (arity, _) => arity ≤ s0.maxApp && arity != 0) = true)
    (bodyRun : ClosSem.evaluate [body]
      (((List.range fns1.length).map (fun i => ClosSem.Value.recclosure (some loc) [] env1 fns1 i)) ++ env1) s0 = (res, s))
    (safe : res ≠ .err (.abort .typeError))
    (bodyCompile : calls [body] groupState = ([bodyOut], final))
    (invariant : codeInv (some g1) l1 s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle)
    (envWell : ∀ v ∈ env1, valueWellFormed g1 l1 t0.code v)
    (stateWell : stateValuesWellFormed g1 l1 t0.code s0)
    (groupWell : wellFormed groupState) (bodyAnnotations : everyFnLocationSome [body])
    (bodyVars : everyFnVarsNone [body]) (bodyDistinct : (codeLocations [body]).Nodup)
    (bodyFresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [body]}) {n | n ∈ groupState.2.map Prod.fst})
    (growth : stateExtends final g1)
    (bodyBound : Set.Subset (Set.diff {n | n ∈ codeLocations [body]} (sptDomain final.1)) l1)
    (disjoint : Disjoint l1 (sptDomain g1.1)) (well : wellFormed g1)
    (group : recClosureRel g1 l1 t0.code loc fns1 fns2)
    (envRelated : envRel (valueRel g1 l1 t0.code) env1 env2 0 [(0, .letrec names (some loc) none fns2 bodyOut)])
    (states : stateRel g1 l1 s0 t0) (included : codeIncludes final.2 t0.code) :
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 s.code s.compile s.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code s ∧ stateExtends g1 g2 ∧ wellFormed g2 ∧
      l1 ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v) (valueWellFormed g2 l2 t.code) res ∧
      ClosSem.evaluate [.letrec names (some loc) none fns2 bodyOut] env2 {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 s t ∧ resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) res res' := by
  let srcRec := (List.range fns1.length).map (fun i => ClosSem.Value.recclosure (some loc) [] env1 fns1 i)
  let dstRec := (List.range fns2.length).map (fun i => ClosSem.Value.recclosure (some loc) [] env2 fns2 i)
  have sourceEnvWell : ∀ v ∈ srcRec ++ env1, valueWellFormed g1 l1 t0.code v := by
    intro v member
    rcases List.mem_append.mp member with rec | captured
    · exact recursiveClosuresWellFormed g1 l1 t0.code loc fns1 fns2 env1 group envWell v rec
    · exact envWell v captured
  have bodyEnv := letrecBodyEnvRel g1 l1 t0.code loc names fns1 fns2 bodyOut env1 env2 group envRelated
  have maxEq := stateRel_maxApp g1 l1 s0 t0 states
  have arities := recClosureRel_arities g1 l1 t0.code loc fns1 fns2 group
  have targetArity : fns2.all (fun (arity, _) => arity ≤ t0.maxApp && arity != 0) = true := by
    have source' : (fns1.map Prod.fst).all (fun arity => arity ≤ s0.maxApp && arity != 0) = true := by
      simpa [List.all_map] using validArity
    have target' : (fns2.map Prod.fst).all (fun arity => arity ≤ t0.maxApp && arity != 0) = true := by
      simpa [arities, ← maxEq] using source'
    simpa [List.all_map] using target'
  obtain ⟨ck, res', t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
    resultWell, targetRun, states2, related2⟩ :=
    bodyIH (srcRec ++ env1) ([body], srcRec ++ env1, s0) groupState final (dstRec ++ env2) t0 [bodyOut] res s
      ({n | n ∈ codeLocations [body]} \ sptDomain final.1) l1 g1
      ⟨rfl, by simpa [srcRec] using bodyRun, safe, bodyCompile, invariant, bodyAnnotations, bodyVars,
        sourceEnvWell, stateWell, groupWell, bodyDistinct, bodyFresh, rfl, growth, bodyBound, disjoint,
        well, by simpa [srcRec, dstRec] using bodyEnv, states, included⟩
  refine ⟨ck, res', t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
    resultWell, ?_, states2, related2⟩
  simpa [ClosSem.evaluate, targetArity, dstRec] using targetRun
private theorem letrecCase {C F : Type} (names : List Flapjack.Basis.Pure.MlString.MlString)
    (loc : Option Nat) (vars : Option (List Nat)) (fns : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (bodyIH : ∀ env, ExprMotive [body] env s0) :
    ExprMotive [.letrec names loc vars fns body] env1 s0 := by
  intro tmp g0 g env2 t0 ys res s l l1 g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, varsNone, envWell, stateWell,
    initialWell, distinct, fresh, locations, growth, allowed, disjoint, well, envRelated, states, included⟩
  cases loc with
  | none => simp [everyFnLocationSome, fnLocationSomeExp] at annotations
  | some loc =>
    cases vars with
    | some vs => simp [everyFnVarsNone, fnVarsNoneExp] at varsNone
    | none =>
      by_cases valid : fns.all (fun (arity, _) => arity ≤ s0.maxApp && arity != 0) = true
      · have bodyRun : ClosSem.evaluate [body]
            (((List.range fns.length).map (fun i => ClosSem.Value.recclosure (some loc) [] env1 fns i)) ++ env1) s0 =
            (res, s) := by simpa [ClosSem.evaluate, valid] using sourceRun
        cases fastRun : calls (fns.map Prod.snd) (insertEachSource loc fns.length g0) with
        | mk fastEs fastState =>
          have fastSing : callsSingList (fns.map Prod.snd) (insertEachSource loc fns.length g0) =
              (fastEs, fastState) := fastRun
          have len : fns.length = fastEs.length := by
            have h := calls_length (fns.map Prod.snd) (insertEachSource loc fns.length g0) fastEs fastState fastRun
            simpa using h.symm
          by_cases guard : (fns.zip fastEs).all (fun (fn, converted) =>
              closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 converted)) = true
          · let groupState := codeListSource loc ((fns.map Prod.fst).zip fastEs) fastState
            cases bodyCompile : calls [body] groupState with
            | mk bodyEs final =>
              obtain ⟨bodyOut, rfl⟩ := calls_sing body groupState bodyEs final bodyCompile
              have bodySing : callsSing body groupState = (bodyOut, final) := by
                have eq := bodyCompile
                simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
                exact Prod.ext eq.1 eq.2
              dsimp only [groupState] at bodySing
              simp only [calls, callsSingList, callsSing, Option.getD_some, fastSing] at compileRun
              simp only [← len, beq_self_eq_true, guard, Bool.and_self, if_true, bodySing, Prod.mk.injEq] at compileRun
              obtain ⟨rfl, rfl⟩ := compileRun
              have initial := letrecInitialFacts names loc fns body g0 annotations varsNone distinct fresh initialWell
              have groupWell : wellFormed groupState := by
                exact optimizedGroupWellFormed loc fns g0 fastState fastEs initial.1 initialWell initial.2.1 initial.2.2.1 fastRun
              have origin := letrecOptimizedLabelOrigin loc fns g0 fastState fastEs fastRun
              have bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.letrec names (some loc) none fns body]}
                  (sptDomain final.1)) l1 := by
                intro key hkey
                apply allowed
                rw [locations]
                exact hkey
              obtain ⟨bodyGrowth, _, bodyAnnotations, bodyVars, bodyDistinct, bodyFresh, bodyBound⟩ :=
                letrecBodyCompilationFacts names loc fns body bodyOut g0 groupState final l1 annotations varsNone
                  distinct fresh origin groupWell bodyCompile bound
              have group := letrecOptimizedRelation names loc fns body bodyOut fastEs g0 fastState final g1 l1 t0.code
                annotations varsNone distinct fresh initialWell fastRun guard bodyCompile bodyGrowth growth bound included
              exact finishLetrec names loc fns (callsListSource .none 1 loc fns) body bodyOut env1 env2 s0 s t0
                groupState final g1 l1 res bodyIH valid bodyRun safe bodyCompile invariant envWell stateWell groupWell
                bodyAnnotations bodyVars bodyDistinct bodyFresh growth bodyBound disjoint well group
                (by simpa using envRelated) states included
          · cases groupRun : calls (fns.map Prod.snd) g0 with
            | mk es groupState =>
              have groupSing : callsSingList (fns.map Prod.snd) g0 = (es, groupState) := groupRun
              cases bodyCompile : calls [body] groupState with
              | mk bodyEs final =>
                obtain ⟨bodyOut, rfl⟩ := calls_sing body groupState bodyEs final bodyCompile
                have bodySing : callsSing body groupState = (bodyOut, final) := by
                  have eq := bodyCompile
                  simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
                  exact Prod.ext eq.1 eq.2
                have guardFalse : (fns.zip fastEs).all (fun (fn, converted) =>
                    closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 converted)) = false := by
                  cases h : (fns.zip fastEs).all (fun (fn, converted) =>
                      closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 converted)) <;> simp_all
                simp only [calls, callsSingList, callsSing, Option.getD_some, fastSing] at compileRun
                simp only [← len, beq_self_eq_true, guardFalse, Bool.and_false, Bool.false_eq_true,
                  ↓reduceIte, groupSing, bodySing, Prod.mk.injEq] at compileRun
                obtain ⟨rfl, rfl⟩ := compileRun
                have initial := letrecInitialFacts names loc fns body g0 annotations varsNone distinct fresh initialWell
                have groupWell := calls_wellFormed (fns.map Prod.snd) g0 es groupState
                  ⟨groupRun, initial.1.2.2.2, initial.2.1, initial.1.1, initialWell⟩
                have origin := letrecOrdinaryLabelOrigin loc fns g0 groupState es groupRun
                have bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.letrec names (some loc) none fns body]}
                    (sptDomain final.1)) l1 := by
                  intro key hkey
                  apply allowed
                  rw [locations]
                  exact hkey
                obtain ⟨bodyGrowth, _, bodyAnnotations, bodyVars, bodyDistinct, bodyFresh, bodyBound⟩ :=
                  letrecBodyCompilationFacts names loc fns body bodyOut g0 groupState final l1 annotations varsNone
                    distinct fresh origin groupWell bodyCompile bound
                have group := letrecOrdinaryRelation names loc fns body bodyOut fastEs es g0 fastState groupState final g1 l1 t0.code
                  annotations varsNone distinct fresh initialWell fastRun guard groupRun bodyCompile bodyGrowth growth bound included
                exact finishLetrec names loc fns ((fns.map Prod.fst).zip es) body bodyOut env1 env2 s0 s t0
                  groupState final g1 l1 res bodyIH valid bodyRun safe bodyCompile invariant envWell stateWell groupWell
                  bodyAnnotations bodyVars bodyDistinct bodyFresh growth bodyBound disjoint well group
                  (by simpa using envRelated) states included
      · simp [ClosSem.evaluate, valid, ClosSem.typeError] at sourceRun
        obtain ⟨rfl, rfl⟩ := sourceRun
        exact (safe rfl).elim
private theorem normalAppEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (trace : BackendCommon.Tra) (loc : Option Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp)
    (related : envRel R env1 env2 0 [(0, .app trace loc function args)]) :
    envRel R env1 env2 0 (args.map (fun e => (0, e))) ∧ envRel R env1 env2 0 [(0, function)] := by
  have existsFree : ∀ n xs, freeVars n xs ↔ ∃ e ∈ xs, freeVarExp n e := by
    intro n xs
    induction xs with
    | nil => simp [freeVars]
    | cons e es ih => simp [freeVars, ih]
  unfold envRel at related ⊢
  by_cases same : env1.length = env2.length
  · simp only [same, ↓reduceIte] at related ⊢
    exact ⟨related, related⟩
  · simp only [same, ↓reduceIte] at related ⊢
    simp only [freeVar, freeVars, freeVarExp, Nat.zero_add, List.mem_singleton, exists_eq_left,
      List.mem_map, exists_exists_and_eq_and, or_false] at related ⊢
    simp only [existsFree] at related
    constructor
    · intro x used
      exact related x (Or.inr used)
    · intro x used
      exact related x (Or.inl used)

private theorem appSequentialFacts (trace : BackendCommon.Tra) (loc : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (g0 middle final : State)
    (outArgs : List ClosLang.Exp) (outFunction : ClosLang.Exp) (allowed : Set Nat)
    (argsRun : calls args g0 = (outArgs, middle))
    (functionRun : calls [function] middle = ([outFunction], final))
    (locations : everyFnLocationSome [.app trace loc function args])
    (vars : everyFnVarsNone [.app trace loc function args])
    (distinct : (codeLocations [.app trace loc function args]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.app trace loc function args]})
      {n | n ∈ g0.2.map Prod.fst}) (well : wellFormed g0)
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.app trace loc function args]}
      (sptDomain final.1)) allowed) :
    wellFormed middle ∧ stateExtends middle final ∧ (codeLocations args).Nodup ∧
      (codeLocations [function]).Nodup ∧ everyFnLocationSome args ∧ everyFnLocationSome [function] ∧
      everyFnVarsNone args ∧ everyFnVarsNone [function] ∧
      Disjoint (Set.image Nat.succ {n | n ∈ codeLocations args}) {n | n ∈ g0.2.map Prod.fst} ∧
      Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [function]}) {n | n ∈ middle.2.map Prod.fst} ∧
      Set.Subset (Set.diff {n | n ∈ codeLocations args} (sptDomain middle.1)) allowed ∧
      Set.Subset (Set.diff {n | n ∈ codeLocations [function]} (sptDomain final.1)) allowed := by
  have distinct' : (codeLocations [function] ++ codeLocations args).Nodup := by
    simpa [codeLocations, codeLocationsExp] using distinct
  have seqDistinct : (codeLocations args ++ codeLocations [function]).Nodup := by
    exact List.perm_append_comm.nodup_iff.mpr distinct'
  have seqFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ
      {n | n ∈ codeLocations args ++ codeLocations [function]} ∧ label ∈ g0.2.map Prod.fst) := by
    intro label ⟨⟨n, member, eq⟩, present⟩
    apply Set.disjoint_left.mp fresh
    · refine ⟨n, ?_, eq⟩
      simpa [codeLocations, codeLocationsExp, List.mem_append, or_comm] using member
    · exact present
  have annParts : fnLocationSomeExp function ∧ everyFnLocationSome args := by
    simpa [everyFnLocationSome, fnLocationSomeExp] using locations
  have varParts : fnVarsNoneExp function ∧ everyFnVarsNone args := by
    simpa [everyFnVarsNone, fnVarsNoneExp] using vars
  have fnAnn : everyFnLocationSome [function] := by simpa [everyFnLocationSome] using annParts.1
  have fnVars : everyFnVarsNone [function] := by simpa [everyFnVarsNone] using varParts.1
  have seqBound : Set.Subset (Set.diff {n | n ∈ codeLocations args ++ codeLocations [function]}
      (sptDomain final.1)) allowed := by
    intro key ⟨member, absent⟩
    apply bound
    refine ⟨?_, absent⟩
    simpa [codeLocations, codeLocationsExp, List.mem_append, or_comm] using member
  obtain ⟨middleWell, growth, argsDistinct, fnDistinct, argsFresh, fnFresh, argsBound, fnBound⟩ :=
    sequentialCompilationFacts args [function] g0 middle final outArgs [outFunction] allowed argsRun functionRun
      seqDistinct seqFresh annParts.2 well seqBound
  refine ⟨middleWell, growth, argsDistinct, fnDistinct, annParts.2, fnAnn, varParts.2, fnVars, ?_, ?_,
    argsBound, fnBound⟩
  · apply Set.disjoint_left.mpr
    intro key a b
    exact argsFresh key ⟨a, b⟩
  · apply Set.disjoint_left.mpr
    intro key a b
    exact fnFresh key ⟨a, b⟩
private theorem letAppEnvRel {A B : Type} (R : A → B → Prop) (env1 : List A) (env2 : List B)
    (trace : BackendCommon.Tra) (args : List ClosLang.Exp) (function continuation : ClosLang.Exp)
    (related : envRel R env1 env2 0 [(0, .let trace (args ++ [function]) continuation)]) :
    envRel R env1 env2 0 (args.map (fun e => (0, e))) ∧ envRel R env1 env2 0 [(0, function)] := by
  have binding := letBindingsEnvRel R env1 env2 trace (args ++ [function]) continuation related
  constructor
  · apply envRel_of_subset R env1 env2 0 _ _ ?_ binding
    intro fn member
    simp only [List.mem_map] at member ⊢
    obtain ⟨e, member, eq⟩ := member
    exact ⟨e, List.mem_append_left _ member, eq⟩
  · apply envRel_of_subset R env1 env2 0 _ _ ?_ binding
    intro fn member
    simp only [List.mem_singleton] at member
    subst fn
    apply List.mem_map.mpr
    exact ⟨function, by simp, rfl⟩

private theorem appArgsSimulation {C F : Type} (trace : BackendCommon.Tra) (loc : Option Nat)
    (function outFunction : ClosLang.Exp) (args outArgs : List ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (s0 middle last : ClosSem.State (NumSet × C) F)
    (t0 : ClosSem.State C F) (g0 gm g g1 : State) (allowed : Set Nat)
    (argsResult result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ExprMotive args env1 s0) (nonempty : args ≠ [])
    (argsRun : ClosSem.evaluate args env1 s0 = (argsResult, middle))
    (sourceRun : ClosSem.evaluate [.app trace loc function args] env1 s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (argsCompile : calls args g0 = (outArgs, gm)) (functionCompile : calls [function] gm = ([outFunction], g))
    (invariant : codeInv (some g1) allowed s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle)
    (annotations : everyFnLocationSome [.app trace loc function args])
    (noVars : everyFnVarsNone [.app trace loc function args])
    (envWell : ∀ v ∈ env1, valueWellFormed g1 allowed t0.code v)
    (stateWell : stateValuesWellFormed g1 allowed t0.code s0) (well0 : wellFormed g0)
    (distinct : (codeLocations [.app trace loc function args]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.app trace loc function args]})
      {n | n ∈ g0.2.map Prod.fst})
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.app trace loc function args]} (sptDomain g.1)) allowed)
    (growth : stateExtends g g1) (disjoint : Disjoint allowed (sptDomain g1.1)) (well1 : wellFormed g1)
    (argsEnv : envRel (valueRel g1 allowed t0.code) env1 env2 0 (outArgs.map (fun e => (0, e))))
    (states : stateRel g1 allowed s0 t0) (included : codeIncludes g.2 t0.code) :
    ∃ ck argsRes t g2 l2,
      codeInv (some g2) l2 middle.code middle.compile middle.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code middle ∧ stateExtends g1 g2 ∧ wellFormed g2 ∧
      allowed ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v) (valueWellFormed g2 l2 t.code) argsResult ∧
      ClosSem.evaluate outArgs env2 {t0 with clock := t0.clock + ck} = (argsRes, t) ∧
      stateRel g2 l2 middle t ∧ resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) argsResult argsRes := by
  have argsSafe : argsResult ≠ .err (.abort .typeError) := by
    intro bad
    subst argsResult
    simp [ClosSem.evaluate, nonempty, argsRun] at sourceRun
    obtain ⟨rfl, rfl⟩ := sourceRun
    exact safe rfl
  obtain ⟨_, middleGrowth, argsDistinct, _, argsAnnotations, _, argsVars, _, argsFresh, _, argsBound, _⟩ :=
    appSequentialFacts trace loc function args g0 gm g outArgs outFunction allowed argsCompile functionCompile
      annotations noVars distinct fresh well0 bound
  have argsGrowth := stateExtends_trans gm g g1 middleGrowth growth
  have argsIncluded := codeIncludes_subg gm g t0.code middleGrowth included
  exact argsIH (args, env1, s0) g0 gm env2 t0 outArgs argsResult middle
    ({n | n ∈ codeLocations args} \ sptDomain gm.1) allowed g1
    ⟨rfl, argsRun, argsSafe, argsCompile, invariant, argsAnnotations, argsVars, envWell, stateWell,
      well0, argsDistinct, argsFresh, rfl, argsGrowth, argsBound, disjoint, well1, argsEnv, states, argsIncluded⟩
private theorem appFunctionSimulation {C F : Type} (trace : BackendCommon.Tra) (loc : Option Nat)
    (function outFunction : ClosLang.Exp) (args outArgs : List ClosLang.Exp)
    (env1 env2 fnTargetEnv : List ClosSem.Value) (s0 middle next last : ClosSem.State (NumSet × C) F)
    (t0 t : ClosSem.State C F) (g0 gm g g1 g2 : State) (allowed allowed2 : Set Nat) (ck : Nat)
    (values : List ClosSem.Value) (targetArgs fnResult result : Result (List ClosSem.Value) ClosSem.Value)
    (fnIH : ∀ (state : ClosSem.State (NumSet × C) F), state.clock ≤ s0.clock → ExprMotive [function] env1 state)
    (nonempty : args ≠ []) (argsRun : ClosSem.evaluate args env1 s0 = (.val values, middle))
    (fnRun : ClosSem.evaluate [function] env1 middle = (fnResult, next))
    (sourceRun : ClosSem.evaluate [.app trace loc function args] env1 s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (argsCompile : calls args g0 = (outArgs, gm)) (fnCompile : calls [function] gm = ([outFunction], g))
    (targetArgsRun : ClosSem.evaluate outArgs env2 {t0 with clock := t0.clock + ck} = (targetArgs, t))
    (invariant : codeInv (some g2) allowed2 middle.code middle.compile middle.compileOracle t.code t.compile t.compileOracle)
    (annotations : everyFnLocationSome [.app trace loc function args])
    (noVars : everyFnVarsNone [.app trace loc function args])
    (envWell : ∀ v ∈ env1, valueWellFormed g1 allowed t0.code v)
    (stateWell : stateValuesWellFormed g2 allowed2 t.code middle) (well0 : wellFormed g0)
    (distinct : (codeLocations [.app trace loc function args]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.app trace loc function args]})
      {n | n ∈ g0.2.map Prod.fst})
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.app trace loc function args]} (sptDomain g.1)) allowed)
    (growth : stateExtends g g1) (growth2 : stateExtends g1 g2) (allowedGrowth : allowed ⊆ allowed2)
    (disjoint : Disjoint allowed2 (sptDomain g2.1)) (well2 : wellFormed g2)
    (fnEnv : envRel (valueRel g1 allowed t0.code) env1 fnTargetEnv 0 [(0, outFunction)])
    (states : stateRel g2 allowed2 middle t) (included : codeIncludes g.2 t0.code) :
    ∃ ck2 fnRes t2 g3 l3,
      codeInv (some g3) l3 next.code next.compile next.compileOracle t2.code t2.compile t2.compileOracle ∧
      stateValuesWellFormed g3 l3 t2.code next ∧ stateExtends g2 g3 ∧ wellFormed g3 ∧
      allowed2 ⊆ l3 ∧ Disjoint l3 (sptDomain g3.1) ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g3 l3 t2.code v) (valueWellFormed g3 l3 t2.code) fnResult ∧
      ClosSem.evaluate [outFunction] fnTargetEnv {t with clock := t.clock + ck2} = (fnRes, t2) ∧
      stateRel g3 l3 next t2 ∧ resultRel (List.Forall₂ (valueRel g3 l3 t2.code)) (valueRel g3 l3 t2.code) fnResult fnRes := by
  have fnSafe : fnResult ≠ .err (.abort .typeError) := by
    intro bad
    subst fnResult
    rw [ClosSem.evaluate] at sourceRun
    simp only [nonempty, List.isEmpty_iff, ↓reduceIte] at sourceRun
    rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
    simp only at sourceRun
    rw [ClosSem.fixClock_evaluate, fnRun] at sourceRun
    simp only [Prod.mk.injEq] at sourceRun
    obtain ⟨rfl, rfl⟩ := sourceRun
    exact safe rfl
  have middleClock := ClosSem.evaluate_clock_source.1 args env1 s0 (.val values) middle argsRun
  have codeGrowth : t0.code.submap t.code := by
    simpa using ClosProps.CodeGrowthPort.evaluate_mono outArgs env2
      {t0 with clock := t0.clock + ck} targetArgs t targetArgsRun
  have envWell' := everyValueWellFormed_subg g1 allowed t0.code env1 t.code g2 allowed2
    ⟨envWell, codeGrowth, growth2, allowedGrowth⟩
  have fnEnv' := envValueRel_subg g1 allowed t0.code env1 fnTargetEnv 0 [(0, outFunction)] g2 allowed2 t.code
    ⟨fnEnv, growth2, allowedGrowth, codeGrowth⟩
  obtain ⟨middleWell, _, _, fnDistinct, _, fnAnnotations, _, fnVars, _, fnFresh, _, fnBound⟩ :=
    appSequentialFacts trace loc function args g0 gm g outArgs outFunction allowed argsCompile fnCompile
      annotations noVars distinct fresh well0 bound
  have fnGrowth := stateExtends_trans g g1 g2 growth growth2
  have fnBound' := Set.Subset.trans fnBound allowedGrowth
  have fnIncluded := codeIncludes_submap g.2 t0.code t.code ⟨included, codeGrowth⟩
  exact fnIH middle middleClock ([function], env1, middle) gm g fnTargetEnv t [outFunction] fnResult next
    ({n | n ∈ codeLocations [function]} \ sptDomain g.1) allowed2 g2
    ⟨rfl, fnRun, fnSafe, fnCompile, invariant, fnAnnotations, fnVars, envWell', stateWell, middleWell,
      fnDistinct, fnFresh, rfl, fnGrowth, fnBound', disjoint, well2, by simpa using fnEnv', states, fnIncluded⟩
private theorem appContinuationSimulation {C F : Type} (trace : BackendCommon.Tra) (loc : Option Nat)
    (function outFunction : ClosLang.Exp) (args : List ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (s0 middle next last : ClosSem.State (NumSet × C) F)
    (t t2 : ClosSem.State C F) (g2 g3 : State) (allowed2 allowed3 : Set Nat) (ck2 : Nat)
    (values targetValues : List ClosSem.Value) (f targetF : ClosSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (appIH : ∀ (f : ClosSem.Value) (values : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock ≤ s0.clock → AppMotive loc f values state)
    (nonempty : args ≠ []) (argsRun : ClosSem.evaluate args env1 s0 = (.val values, middle))
    (fnRun : ClosSem.evaluate [function] env1 middle = (.val [f], next))
    (sourceRun : ClosSem.evaluate [.app trace loc function args] env1 s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (targetFnRun : ClosSem.evaluate [outFunction] env2 {t with clock := t.clock + ck2} = (.val [targetF], t2))
    (invariant : codeInv (some g3) allowed3 next.code next.compile next.compileOracle t2.code t2.compile t2.compileOracle)
    (stateWell : stateValuesWellFormed g3 allowed3 t2.code next)
    (growth : stateExtends g2 g3) (allowedGrowth : allowed2 ⊆ allowed3)
    (well : wellFormed g3) (disjoint : Disjoint allowed3 (sptDomain g3.1))
    (valueWell : valueWellFormed g3 allowed3 t2.code f)
    (valueRelated : valueRel g3 allowed3 t2.code f targetF)
    (argsWell : ∀ a ∈ values, valueWellFormed g2 allowed2 t.code a)
    (argsRelated : List.Forall₂ (valueRel g2 allowed2 t.code) values targetValues)
    (states : stateRel g3 allowed3 next t2) :
    ∃ ck3 res' t3 g4 l4,
      codeInv (some g4) l4 last.code last.compile last.compileOracle t3.code t3.compile t3.compileOracle ∧
      stateValuesWellFormed g4 l4 t3.code last ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g4 l4 t3.code v)
        (valueWellFormed g4 l4 t3.code) result ∧
      ClosSem.evaluateApp loc targetF targetValues {t2 with clock := t2.clock + ck3} = (res', t3) ∧
      stateRel g4 l4 last t3 ∧ stateExtends g3 g4 ∧ wellFormed g4 ∧ allowed3 ⊆ l4 ∧
      Disjoint l4 (sptDomain g4.1) ∧
      resultRel (List.Forall₂ (valueRel g4 l4 t3.code)) (valueRel g4 l4 t3.code) result res' := by
  have appRun : ClosSem.evaluateApp loc f values next = (result, last) := by
    rw [ClosSem.evaluate] at sourceRun
    simp only [nonempty, List.isEmpty_iff, ↓reduceIte] at sourceRun
    rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
    simp only at sourceRun
    rw [ClosSem.fixClock_evaluate, fnRun] at sourceRun
    simpa [ClosSem.headValue, holHd] using sourceRun
  have firstClock := ClosSem.evaluate_clock_source.1 args env1 s0 (.val values) middle argsRun
  have secondClock := ClosSem.evaluate_clock_source.1 [function] env1 middle (.val [f]) next fnRun
  have nextClock : next.clock ≤ s0.clock := Nat.le_trans secondClock firstClock
  have codeGrowth : t.code.submap t2.code := by
    simpa using ClosProps.CodeGrowthPort.evaluate_mono [outFunction] env2
      {t with clock := t.clock + ck2} (.val [targetF]) t2 targetFnRun
  have argsWell' := everyValueWellFormed_subg g2 allowed2 t.code values t2.code g3 allowed3
    ⟨argsWell, codeGrowth, growth, allowedGrowth⟩
  have argsRelated' := listValueRel_subg g2 allowed2 t.code values targetValues g3 allowed3 t2.code
    ⟨argsRelated, growth, allowedGrowth, codeGrowth⟩
  exact appIH f values next nextClock (L := Unit) () g3 allowed3 t2 result last targetF targetValues
    ⟨appRun, safe, invariant, valueWell, argsWell', stateWell, well, disjoint,
      valueRelated, argsRelated', states⟩
private theorem normalAppTargetRun {C F : Type} (trace : BackendCommon.Tra) (loc : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (initial middle next last : ClosSem.State C F) (ck1 ck2 ck3 : Nat)
    (values : List ClosSem.Value) (f : ClosSem.Value)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (nonempty : args ≠ [])
    (argsRun : ClosSem.evaluate args env {initial with clock := initial.clock + ck1} = (.val values, middle))
    (fnRun : ClosSem.evaluate [function] env {middle with clock := middle.clock + ck2} = (.val [f], next))
    (appRun : ClosSem.evaluateApp loc f values {next with clock := next.clock + ck3} = (result, last)) :
    ClosSem.evaluate [.app trace loc function args] env
      {initial with clock := initial.clock + (ck1 + ck2 + ck3)} = (result, last) := by
  have shiftedArgs := ClosSem.evaluate_addClock.1 args env {initial with clock := initial.clock + ck1}
    middle (.val values) (ck2 + ck3) argsRun (by simp)
  have shiftedFn := ClosSem.evaluate_addClock.1 [function] env {middle with clock := middle.clock + ck2}
    next (.val [f]) ck3 fnRun (by simp)
  rw [ClosSem.evaluate]
  simp only [nonempty, List.isEmpty_iff, ↓reduceIte]
  rw [ClosSem.fixClock_evaluate]
  have shiftedArgs' : ClosSem.evaluate args env
      {initial with clock := initial.clock + (ck1 + ck2 + ck3)} =
      (.val values, {middle with clock := middle.clock + (ck2 + ck3)}) := by
    simpa [Nat.add_assoc] using shiftedArgs
  rw [shiftedArgs']
  simp only
  rw [ClosSem.fixClock_evaluate]
  have shiftedFn' : ClosSem.evaluate [function] env {middle with clock := middle.clock + (ck2 + ck3)} =
      (.val [f], {next with clock := next.clock + ck3}) := by
    simpa [Nat.add_assoc] using shiftedFn
  rw [shiftedFn']
  simpa [ClosSem.headValue, holHd] using appRun
private theorem normalAppArgsErrorTargetRun {C F : Type} (trace : BackendCommon.Tra) (loc : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (initial last : ClosSem.State C F) (ck : Nat) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult ClosSem.Value)
    (nonempty : args ≠ [])
    (argsRun : ClosSem.evaluate args env {initial with clock := initial.clock + ck} = (.err error, last)) :
    ClosSem.evaluate [.app trace loc function args] env {initial with clock := initial.clock + ck} =
      (.err error, last) := by
  rw [ClosSem.evaluate]
  simp only [nonempty, List.isEmpty_iff, ↓reduceIte]
  rw [ClosSem.fixClock_evaluate, argsRun]

private theorem normalAppFunctionErrorTargetRun {C F : Type} (trace : BackendCommon.Tra) (loc : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (initial middle last : ClosSem.State C F) (ck1 ck2 : Nat) (values : List ClosSem.Value) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult ClosSem.Value)
    (nonempty : args ≠ [])
    (argsRun : ClosSem.evaluate args env {initial with clock := initial.clock + ck1} = (.val values, middle))
    (fnRun : ClosSem.evaluate [function] env {middle with clock := middle.clock + ck2} = (.err error, last)) :
    ClosSem.evaluate [.app trace loc function args] env {initial with clock := initial.clock + (ck1 + ck2)} =
      (.err error, last) := by
  have shiftedArgs := ClosSem.evaluate_addClock.1 args env {initial with clock := initial.clock + ck1}
    middle (.val values) ck2 argsRun (by simp)
  have shiftedArgs' : ClosSem.evaluate args env {initial with clock := initial.clock + (ck1 + ck2)} =
      (.val values, {middle with clock := middle.clock + ck2}) := by
    simpa [Nat.add_assoc] using shiftedArgs
  rw [ClosSem.evaluate]
  simp only [nonempty, List.isEmpty_iff, ↓reduceIte]
  rw [ClosSem.fixClock_evaluate, shiftedArgs']
  simp only
  rw [ClosSem.fixClock_evaluate, fnRun]
private theorem finishNormalApp {C F : Type} (trace : BackendCommon.Tra) (loc : Option Nat)
    (function outFunction : ClosLang.Exp) (args outArgs : List ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (s0 last : ClosSem.State (NumSet × C) F)
    (t0 : ClosSem.State C F) (g0 gm g g1 : State) (allowed : Set Nat)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ExprMotive args env1 s0)
    (fnIH : ∀ (state : ClosSem.State (NumSet × C) F), state.clock ≤ s0.clock → ExprMotive [function] env1 state)
    (appIH : ∀ (f : ClosSem.Value) (values : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock ≤ s0.clock → AppMotive loc f values state)
    (nonempty : args ≠ []) (sourceRun : ClosSem.evaluate [.app trace loc function args] env1 s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (argsCompile : calls args g0 = (outArgs, gm)) (fnCompile : calls [function] gm = ([outFunction], g))
    (invariant : codeInv (some g1) allowed s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle)
    (annotations : everyFnLocationSome [.app trace loc function args])
    (noVars : everyFnVarsNone [.app trace loc function args])
    (envWell : ∀ v ∈ env1, valueWellFormed g1 allowed t0.code v)
    (stateWell : stateValuesWellFormed g1 allowed t0.code s0) (well0 : wellFormed g0)
    (distinct : (codeLocations [.app trace loc function args]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.app trace loc function args]})
      {n | n ∈ g0.2.map Prod.fst})
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.app trace loc function args]} (sptDomain g.1)) allowed)
    (growth : stateExtends g g1) (disjoint : Disjoint allowed (sptDomain g1.1)) (well1 : wellFormed g1)
    (argsEnv : envRel (valueRel g1 allowed t0.code) env1 env2 0 (outArgs.map (fun e => (0, e))))
    (fnEnv : envRel (valueRel g1 allowed t0.code) env1 env2 0 [(0, outFunction)])
    (states : stateRel g1 allowed s0 t0) (included : codeIncludes g.2 t0.code) :
    ∃ ck result' t g2 l2,
      codeInv (some g2) l2 last.code last.compile last.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code last ∧ stateExtends g1 g2 ∧ wellFormed g2 ∧
      allowed ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v) (valueWellFormed g2 l2 t.code) result ∧
      ClosSem.evaluate [.app trace loc outFunction outArgs] env2 {t0 with clock := t0.clock + ck} = (result', t) ∧
      stateRel g2 l2 last t ∧ resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) result result' := by
  have outNonempty : outArgs ≠ [] := by
    intro empty
    have len := calls_length args g0 outArgs gm argsCompile
    simp [empty] at len
    cases args with
    | nil => exact nonempty rfl
    | cons x xs => simp at len
  cases argsRun : ClosSem.evaluate args env1 s0 with
  | mk argsResult middle =>
    obtain ⟨ck, targetArgs, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
      argsWell, targetArgsRun, states2, argsRelated⟩ :=
      appArgsSimulation trace loc function outFunction args outArgs env1 env2 s0 middle last t0 g0 gm g g1 allowed
        argsResult result argsIH nonempty argsRun sourceRun safe argsCompile fnCompile invariant annotations noVars
        envWell stateWell well0 distinct fresh bound growth disjoint well1 argsEnv states included
    cases argsResult with
    | err error =>
      cases targetArgs with
      | val _ => exact False.elim argsRelated
      | err targetError =>
        have eq : (result, last) = (.err error, middle) := by
          rw [ClosSem.evaluate] at sourceRun
          simp only [nonempty, List.isEmpty_iff, ↓reduceIte] at sourceRun
          rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
          exact sourceRun.symm
        cases eq
        exact ⟨ck, .err targetError, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
          argsWell, normalAppArgsErrorTargetRun trace loc outFunction outArgs env2 t0 t ck targetError outNonempty targetArgsRun,
          states2, argsRelated⟩
    | val values =>
      cases targetArgs with
      | err _ => exact False.elim argsRelated
      | val targetValues =>
        cases fnRun : ClosSem.evaluate [function] env1 middle with
        | mk fnResult next =>
          obtain ⟨ck2, targetFn, t2, g3, l3, inv3, stateWell3, growth3, well3, allowed3, disjoint3,
            fnWell, targetFnRun, states3, fnRelated⟩ :=
            appFunctionSimulation trace loc function outFunction args outArgs env1 env2 env2 s0 middle next last t0 t
              g0 gm g g1 g2 allowed l2 ck values (.val targetValues) fnResult result fnIH nonempty argsRun fnRun
              sourceRun safe argsCompile fnCompile targetArgsRun inv2 annotations noVars envWell stateWell2 well0
              distinct fresh bound growth growth2 allowed2 disjoint2 well2 fnEnv states2 included
          cases fnResult with
          | err error =>
            cases targetFn with
            | val _ => exact False.elim fnRelated
            | err targetError =>
              have eq : (result, last) = (.err error, next) := by
                rw [ClosSem.evaluate] at sourceRun
                simp only [nonempty, List.isEmpty_iff, ↓reduceIte] at sourceRun
                rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
                simp only at sourceRun
                rw [ClosSem.fixClock_evaluate, fnRun] at sourceRun
                exact sourceRun.symm
              cases eq
              exact ⟨ck + ck2, .err targetError, t2, g3, l3, inv3, stateWell3,
                stateExtends_trans g1 g2 g3 growth2 growth3, well3, Set.Subset.trans allowed2 allowed3, disjoint3,
                fnWell, normalAppFunctionErrorTargetRun trace loc outFunction outArgs env2 t0 t t2 ck ck2 targetValues targetError
                  outNonempty targetArgsRun targetFnRun, states3, fnRelated⟩
          | val fnValues =>
            cases targetFn with
            | err _ => exact False.elim fnRelated
            | val targetFnValues =>
              obtain ⟨f, rfl⟩ := ClosProps.evaluateSing function env1 middle next fnValues fnRun
              obtain ⟨targetF, rfl⟩ := ClosProps.evaluateSing outFunction env2
                {t with clock := t.clock + ck2} t2 targetFnValues targetFnRun
              change List.Forall₂ (valueRel g3 l3 t2.code) [f] [targetF] at fnRelated
              cases fnRelated with
              | cons valueRelated rest =>
                cases rest
                change ∀ v ∈ [f], valueWellFormed g3 l3 t2.code v at fnWell
                have fWell := fnWell f (by simp)
                change ∀ v ∈ values, valueWellFormed g2 l2 t.code v at argsWell
                change List.Forall₂ (valueRel g2 l2 t.code) values targetValues at argsRelated
                obtain ⟨ck3, result', t3, g4, l4, inv4, stateWell4, resultWell, appTargetRun, states4,
                  growth4, well4, allowed4, disjoint4, resultRelated⟩ :=
                  appContinuationSimulation trace loc function outFunction args env1 env2 s0 middle next last t t2
                    g2 g3 l2 l3 ck2 values targetValues f targetF result appIH nonempty argsRun fnRun sourceRun safe
                    targetFnRun inv3 stateWell3 growth3 allowed3 well3 disjoint3 fWell valueRelated argsWell argsRelated states3
                exact ⟨ck + ck2 + ck3, result', t3, g4, l4, inv4, stateWell4,
                  stateExtends_trans g1 g3 g4 (stateExtends_trans g1 g2 g3 growth2 growth3) growth4,
                  well4, Set.Subset.trans (Set.Subset.trans allowed2 allowed3) allowed4, disjoint4, resultWell,
                  normalAppTargetRun trace loc outFunction outArgs env2 t0 t t2 t3 ck ck2 ck3 targetValues targetF result'
                    outNonempty targetArgsRun targetFnRun appTargetRun, states4, resultRelated⟩
private theorem directLetArgsErrorTargetRun {C F : Type} (trace : BackendCommon.Tra)
    (function body : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (initial last : ClosSem.State C F) (ck : Nat) (error : Flapjack.SemanticPrimitivesHOL.ErrorResult ClosSem.Value)
    (argsRun : ClosSem.evaluate args env {initial with clock := initial.clock + ck} = (.err error, last)) :
    ClosSem.evaluate [.let trace (args ++ [function]) body] env {initial with clock := initial.clock + ck} =
      (.err error, last) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, ClosProps.evaluateSnoc, argsRun]

private theorem directLetFunctionErrorTargetRun {C F : Type} (trace : BackendCommon.Tra)
    (function body : ClosLang.Exp) (args : List ClosLang.Exp) (env : List ClosSem.Value)
    (initial middle last : ClosSem.State C F) (ck1 ck2 : Nat) (values : List ClosSem.Value)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult ClosSem.Value)
    (argsRun : ClosSem.evaluate args env {initial with clock := initial.clock + ck1} = (.val values, middle))
    (fnRun : ClosSem.evaluate [function] env {middle with clock := middle.clock + ck2} = (.err error, last)) :
    ClosSem.evaluate [.let trace (args ++ [function]) body] env {initial with clock := initial.clock + (ck1 + ck2)} =
      (.err error, last) := by
  have shiftedArgs := ClosSem.evaluate_addClock.1 args env {initial with clock := initial.clock + ck1}
    middle (.val values) ck2 argsRun (by simp)
  have shiftedArgs' : ClosSem.evaluate args env {initial with clock := initial.clock + (ck1 + ck2)} =
      (.val values, {middle with clock := middle.clock + ck2}) := by
    simpa [Nat.add_assoc] using shiftedArgs
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, ClosProps.evaluateSnoc, shiftedArgs']
  simp only
  rw [fnRun]
private theorem pureFunctionSimulationFacts {C F : Type} (function outFunction : ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (middle next : ClosSem.State (NumSet × C) F)
    (t t2 : ClosSem.State C F) (g0 g1 g : State) (allowed : Set Nat) (ck : Nat)
    (fnResult targetResult : Result (List ClosSem.Value) ClosSem.Value)
    (pure : ClosLang.pure function = true) (compile : calls [function] g0 = ([outFunction], g1))
    (sourceRun : ClosSem.evaluate [function] env1 middle = (fnResult, next))
    (safe : fnResult ≠ .err (.abort .typeError))
    (targetRun : ClosSem.evaluate [outFunction] env2 {t with clock := t.clock + ck} = (targetResult, t2))
    (related : resultRel (List.Forall₂ (valueRel g allowed t2.code)) (valueRel g allowed t2.code)
      fnResult targetResult) :
    ∃ f targetF, fnResult = .val [f] ∧ targetResult = .val [targetF] ∧ next = middle ∧
      t2 = {t with clock := t.clock + ck} ∧ valueRel g allowed t2.code f targetF := by
  have srcPure := PureCorrectPort.pureCorrectEq function env1 middle fnResult next ⟨pure, sourceRun⟩
  have targetPure := calls_pure_sing function g0 outFunction g1 ⟨pure, compile⟩
  have dstPure := PureCorrectPort.pureCorrectEq outFunction env2 {t with clock := t.clock + ck}
    targetResult t2 ⟨targetPure, targetRun⟩
  cases fnResult with
  | err error =>
    cases error with
    | raise _ => exact srcPure.elim
    | abort reason =>
      subst reason
      exact (safe rfl).elim
  | val values =>
    obtain ⟨f, rfl⟩ := ClosProps.evaluateSing function env1 middle next values sourceRun
    cases targetResult with
    | err _ => exact False.elim related
    | val targetValues =>
      obtain ⟨targetF, rfl⟩ := ClosProps.evaluateSing outFunction env2
        {t with clock := t.clock + ck} t2 targetValues targetRun
      change List.Forall₂ (valueRel g allowed t2.code) [f] [targetF] at related
      cases related with
      | cons rel tail =>
        cases tail
        exact ⟨f, targetF, rfl, rfl, srcPure.1, dstPure.1, rel⟩
private theorem knownLocationCodeLookup (g g2 : State) (loc : Nat)
    (code : HolFiniteMapExact Nat (Nat × ClosLang.Exp)) (entry : Nat × ClosLang.Exp)
    (well : wellFormed g) (known : sptDomain g.1 loc) (growth : stateExtends g g2)
    (included : codeIncludes g.2 code) (found : holALookup g2.2 (loc + 1) = some entry) :
    code.lookup (loc + 1) = some entry := by
  have keyMem : loc + 1 ∈ g.2.map Prod.fst := by
    have h : loc + 1 ∈ Set.image Nat.succ (sptDomain g.1) := by
      exact ⟨loc, known, by simp⟩
    rw [← well.1] at h
    exact h
  obtain ⟨⟨key, oldEntry⟩, mem, eq⟩ := List.mem_map.mp keyMem
  simp only at eq
  subst key
  have oldFound : holALookup g.2 (loc + 1) = some oldEntry :=
    holALookup_of_distinct_member g.2 (loc + 1) oldEntry ⟨well.2, mem⟩
  have newFound := growth.2.1 (loc + 1) oldEntry oldFound
  rw [found] at newFound
  cases newFound
  exact included (loc + 1) entry oldFound
private theorem directCallAppEquivalence {C F : Type} (trace stubTrace : BackendCommon.Tra)
    (loc : Nat) (function : ClosSem.Value) (args captured : List ClosSem.Value)
    (argExps : List ClosLang.Exp) (env : List ClosSem.Value) (state : ClosSem.State C F)
    (compiled : ClosLang.Exp) (nonempty : args ≠ [])
    (argsRun : ClosSem.evaluate argExps env state = (.val args, state))
    (dest : ClosSem.destClosure state.maxApp (some loc) function args =
      some (.fullApp (.call stubTrace 0 (loc + 1) (variablesSource stubTrace 1 args.length)) (args ++ captured) []))
    (lookup : state.code.lookup (loc + 1) = some (args.length, compiled)) :
    ClosSem.evaluateApp (some loc) function args state =
      ClosSem.evaluate [.call trace args.length (loc + 1) argExps] env state := by
  cases args with
  | nil => exact (nonempty rfl).elim
  | cons arg args =>
    rw [ClosSem.evaluateApp, dest, ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun]
    simp only [List.length_cons, List.length_nil, Nat.sub_zero]
    by_cases early : state.clock < args.length + 1
    · simp [early, show state.clock < args.length + 1 + 1 by omega, ClosSem.findCode, lookup]
    · simp only [early, ↓reduceIte]
      have comp : ClosSem.evaluate
          [.call stubTrace 0 (loc + 1) (variablesSource stubTrace 1 (args.length + 1))]
          (arg :: args ++ captured) (ClosSem.decClock (args.length + 1) state) =
          (match ClosSem.findCode (loc + 1) (arg :: args) state.code with
          | none => ClosSem.typeError state
          | some (values, body) => if state.clock < args.length + 1 + 1 then
              ClosSem.timeoutError {state with clock := 0}
            else ClosSem.evaluate [body] values (ClosSem.decClock (args.length + 1 + 1) state)) := by
        by_cases boundary : state.clock < args.length + 1 + 1
        · have eq : state.clock = args.length + 1 := by omega
          simp [eq, ClosSem.evaluate, evaluate_variables,
            ClosSem.findCode, lookup, ClosSem.decClock, ClosSem.fixClock]
        · have enough : args.length + 1 + 1 ≤ state.clock := by omega
          simp [boundary, ClosSem.evaluate, evaluate_variables,
            ClosSem.findCode, lookup, ClosSem.decClock, ClosSem.fixClock, show state.clock - (args.length + 1) ≠ 0 by omega,
            show state.clock - (args.length + 1) - 1 = state.clock - (args.length + 1 + 1) by omega]
      apply Eq.trans ?_ comp
      rw [ClosSem.fixClock_evaluate]
      cases run : ClosSem.evaluate
          [.call stubTrace 0 (loc + 1) (variablesSource stubTrace 1 (args.length + 1))]
          (arg :: args ++ captured) (ClosSem.decClock (args.length + 1) state) with
      | mk result final =>
        cases result with
        | err error => rfl
        | val values =>
          obtain ⟨value, rfl⟩ := ClosProps.evaluateSing _ _ _ _ values run
          simp [ClosSem.evaluateApp.eq_def]
private theorem directCallAfterArgs {C F : Type} (trace stubTrace : BackendCommon.Tra)
    (loc : Nat) (function : ClosSem.Value) (args captured : List ClosSem.Value)
    (argExps : List ClosLang.Exp) (env : List ClosSem.Value) (initial middle : ClosSem.State C F)
    (compiled : ClosLang.Exp) (nonempty : args ≠ [])
    (argsRun : ClosSem.evaluate argExps env initial = (.val args, middle))
    (dest : ClosSem.destClosure middle.maxApp (some loc) function args =
      some (.fullApp (.call stubTrace 0 (loc + 1) (variablesSource stubTrace 1 args.length)) (args ++ captured) []))
    (lookup : middle.code.lookup (loc + 1) = some (args.length, compiled)) :
    ClosSem.evaluateApp (some loc) function args middle =
      ClosSem.evaluate [.call trace args.length (loc + 1) argExps] env initial := by
  have varsRun : ClosSem.evaluate (variablesSource trace 0 args.length) args middle = (.val args, middle) := by
    simpa using evaluate_variables args middle args.length trace 0
  rw [directCallAppEquivalence trace stubTrace loc function args captured
    (variablesSource trace 0 args.length) args middle compiled nonempty varsRun dest lookup]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, varsRun]
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argsRun]
private theorem pureDirectTargetRun {C F : Type} (trace stubTrace : BackendCommon.Tra)
    (loc : Nat) (function : ClosSem.Value) (args captured : List ClosSem.Value)
    (argExps : List ClosLang.Exp) (env : List ClosSem.Value) (initial middle next last : ClosSem.State C F)
    (ck1 ck2 ck3 : Nat) (compiled : ClosLang.Exp) (result : Result (List ClosSem.Value) ClosSem.Value)
    (nonempty : args ≠ [])
    (argsRun : ClosSem.evaluate argExps env {initial with clock := initial.clock + ck1} = (.val args, middle))
    (pureNext : next = {middle with clock := middle.clock + ck2})
    (dest : ClosSem.destClosure next.maxApp (some loc) function args =
      some (.fullApp (.call stubTrace 0 (loc + 1) (variablesSource stubTrace 1 args.length)) (args ++ captured) []))
    (lookup : next.code.lookup (loc + 1) = some (args.length, compiled))
    (appRun : ClosSem.evaluateApp (some loc) function args {next with clock := next.clock + ck3} = (result, last)) :
    ClosSem.evaluate [.call trace args.length (loc + 1) argExps] env
      {initial with clock := initial.clock + (ck1 + ck2 + ck3)} = (result, last) := by
  have shifted := ClosSem.evaluate_addClock.1 argExps env {initial with clock := initial.clock + ck1}
    middle (.val args) (ck2 + ck3) argsRun (by simp)
  have shifted' : ClosSem.evaluate argExps env {initial with clock := initial.clock + (ck1 + ck2 + ck3)} =
      (.val args, {next with clock := next.clock + ck3}) := by
    subst next
    simpa [Nat.add_assoc] using shifted
  have dest' : ClosSem.destClosure ({next with clock := next.clock + ck3} : ClosSem.State C F).maxApp
      (some loc) function args =
      some (.fullApp (.call stubTrace 0 (loc + 1) (variablesSource stubTrace 1 args.length)) (args ++ captured) []) := by
    simpa using dest
  have lookup' : ({next with clock := next.clock + ck3} : ClosSem.State C F).code.lookup (loc + 1) =
      some (args.length, compiled) := by simpa using lookup
  have run := directCallAfterArgs trace stubTrace loc function args captured argExps env
    {initial with clock := initial.clock + (ck1 + ck2 + ck3)} {next with clock := next.clock + ck3}
    compiled nonempty shifted' dest' lookup'
  rw [appRun] at run
  exact run.symm
private theorem directClosureFacts {C F : Type} (loc : Nat) (function targetFunction : ClosSem.Value)
    (args targetArgs : List ClosSem.Value) (source last : ClosSem.State (NumSet × C) F)
    (target : ClosSem.State C F) (g0 g : State) (allowed : Set Nat)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (nonempty : args ≠ []) (appRun : ClosSem.evaluateApp (some loc) function args source = (result, last))
    (safe : result ≠ .err (.abort .typeError)) (functionRel : valueRel g allowed target.code function targetFunction)
    (argsRel : List.Forall₂ (valueRel g allowed target.code) args targetArgs)
    (well0 : wellFormed g0) (well : wellFormed g) (growth : stateExtends g0 g)
    (known : sptDomain g0.1 loc) (disjoint : Disjoint allowed (sptDomain g.1))
    (included : codeIncludes g0.2 target.code) (states : stateRel g allowed source target) :
    ∃ stubTrace compiled captured,
      ClosSem.destClosure target.maxApp (some loc) targetFunction targetArgs =
        some (.fullApp (.call stubTrace 0 (loc + 1) (variablesSource stubTrace 1 targetArgs.length))
          (targetArgs ++ captured) []) ∧
      target.code.lookup (loc + 1) = some (targetArgs.length, compiled) := by
  have known' : sptDomain g.1 loc := sptSubspt_domainSubset g0.1 g.1 growth.1 known
  have notAllowed : ¬ allowed loc := by
    intro h
    exact Set.disjoint_left.mp disjoint h known'
  cases dest : ClosSem.destClosure source.maxApp (some loc) function args with
  | none =>
    cases args with
    | nil => exact (nonempty rfl).elim
    | cons a rest => exact (appMissingClosureImpossible a rest (some loc) function source last result dest appRun safe).elim
  | some kind =>
    obtain ⟨body, sourceCaptured, xs, i, es, ga, gb, targetCaptured, trace, _, shape, selected,
      compiled, bound, ext, found, targetDest, code⟩ :=
      destClosure_valueRel_lookup (A := Unit) source.maxApp loc function args kind g allowed target.code targetFunction targetArgs
        ⟨dest, functionRel, argsRel, well, known', notAllowed⟩
    have codeFound := knownLocationCodeLookup g0 g loc target.code (args.length, holEl i es)
      well0 known growth included found
    have len : args.length = targetArgs.length := argsRel.length_eq
    have maxEq := stateRel_maxApp g allowed source target states
    refine ⟨trace, holEl i es, targetCaptured, ?_, ?_⟩
    · simpa [← maxEq, ← len] using targetDest
    · simpa [← len] using codeFound
private theorem finishPureDirectApp {C F : Type} (trace : BackendCommon.Tra) (loc : Nat)
    (function outFunction : ClosLang.Exp) (args outArgs : List ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (s0 last : ClosSem.State (NumSet × C) F)
    (t0 : ClosSem.State C F) (g0 gm g g1 : State) (allowed : Set Nat)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ExprMotive args env1 s0)
    (fnIH : ∀ (state : ClosSem.State (NumSet × C) F), state.clock ≤ s0.clock → ExprMotive [function] env1 state)
    (appIH : ∀ (f : ClosSem.Value) (values : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock ≤ s0.clock → AppMotive (some loc) f values state)
    (pure : ClosLang.pure function = true) (known : sptDomain g.1 loc)
    (nonempty : args ≠ []) (sourceRun : ClosSem.evaluate [.app trace (some loc) function args] env1 s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (argsCompile : calls args g0 = (outArgs, gm)) (fnCompile : calls [function] gm = ([outFunction], g))
    (invariant : codeInv (some g1) allowed s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle)
    (annotations : everyFnLocationSome [.app trace (some loc) function args])
    (noVars : everyFnVarsNone [.app trace (some loc) function args])
    (envWell : ∀ v ∈ env1, valueWellFormed g1 allowed t0.code v)
    (stateWell : stateValuesWellFormed g1 allowed t0.code s0) (well0 : wellFormed g0)
    (distinct : (codeLocations [.app trace (some loc) function args]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.app trace (some loc) function args]})
      {n | n ∈ g0.2.map Prod.fst})
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.app trace (some loc) function args]} (sptDomain g.1)) allowed)
    (growth : stateExtends g g1) (disjoint : Disjoint allowed (sptDomain g1.1)) (well1 : wellFormed g1)
    (argsEnv : envRel (valueRel g1 allowed t0.code) env1 env2 0 (outArgs.map (fun e => (0, e))))
    (states : stateRel g1 allowed s0 t0) (included : codeIncludes g.2 t0.code) :
    ∃ ck result' t g2 l2,
      codeInv (some g2) l2 last.code last.compile last.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code last ∧ stateExtends g1 g2 ∧ wellFormed g2 ∧
      allowed ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v) (valueWellFormed g2 l2 t.code) result ∧
      ClosSem.evaluate [.call trace outArgs.length (loc + 1) outArgs] env2 {t0 with clock := t0.clock + ck} = (result', t) ∧
      stateRel g2 l2 last t ∧ resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) result result' := by
  obtain ⟨env5, fnEnv, _⟩ := envRel_exists g1 allowed t0.code env1 [(0, outFunction)] envWell
  obtain ⟨middleWell, _, _, fnDistinct, _, fnAnnotations, _, _, _, fnFresh, _, _⟩ :=
    appSequentialFacts trace (some loc) function args g0 gm g outArgs outFunction allowed argsCompile fnCompile
      annotations noVars distinct fresh well0 bound
  have wellG := calls_wellFormed [function] gm [outFunction] g
    ⟨fnCompile, fnDistinct, (by intro label h; exact Set.disjoint_left.mp fnFresh h.1 h.2), fnAnnotations, middleWell⟩
  cases argsRun : ClosSem.evaluate args env1 s0 with
  | mk argsResult middle =>
    obtain ⟨ck, targetArgs, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
      argsWell, targetArgsRun, states2, argsRelated⟩ :=
      appArgsSimulation trace (some loc) function outFunction args outArgs env1 env2 s0 middle last t0 g0 gm g g1 allowed
        argsResult result argsIH nonempty argsRun sourceRun safe argsCompile fnCompile invariant annotations noVars
        envWell stateWell well0 distinct fresh bound growth disjoint well1 argsEnv states included
    cases argsResult with
    | err error =>
      cases targetArgs with
      | val _ => exact False.elim argsRelated
      | err targetError =>
        have eq : (result, last) = (.err error, middle) := by
          rw [ClosSem.evaluate] at sourceRun
          simp only [nonempty, List.isEmpty_iff, ↓reduceIte] at sourceRun
          rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
          exact sourceRun.symm
        cases eq
        refine ⟨ck, .err targetError, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
          argsWell, ?_, states2, argsRelated⟩
        rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, targetArgsRun]
    | val values =>
      cases targetArgs with
      | err _ => exact False.elim argsRelated
      | val targetValues =>
        have valuesNonempty : values ≠ [] := by
          intro empty
          have len := ClosProps.evaluateImpLength args env1 s0 middle values argsRun
          simp [empty] at len
          cases args with
          | nil => exact nonempty rfl
          | cons a rest => simp at len
        have targetNonempty : targetValues ≠ [] := by
          intro empty
          have len := argsRelated.length_eq
          simp [empty] at len
          exact valuesNonempty (by cases values <;> simp_all)
        cases fnRun : ClosSem.evaluate [function] env1 middle with
        | mk fnResult next =>
          obtain ⟨ck2, targetFn, t2, g3, l3, inv3, stateWell3, growth3, well3, allowed3, disjoint3,
            fnWell, targetFnRun, states3, fnRelated⟩ :=
            appFunctionSimulation trace (some loc) function outFunction args outArgs env1 env2 env5 s0 middle next last t0 t
              g0 gm g g1 g2 allowed l2 ck values (.val targetValues) fnResult result fnIH nonempty argsRun fnRun
              sourceRun safe argsCompile fnCompile targetArgsRun inv2 annotations noVars envWell stateWell2 well0
              distinct fresh bound growth growth2 allowed2 disjoint2 well2 fnEnv states2 included
          have fnSafe : fnResult ≠ .err (.abort .typeError) := by
            intro bad
            subst fnResult
            rw [ClosSem.evaluate] at sourceRun
            simp only [nonempty, List.isEmpty_iff, ↓reduceIte] at sourceRun
            rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
            simp only at sourceRun
            rw [ClosSem.fixClock_evaluate, fnRun] at sourceRun
            obtain ⟨rfl, rfl⟩ := sourceRun
            exact safe rfl
          obtain ⟨f, targetF, rfl, rfl, sourceNext, targetNext, functionRelated⟩ :=
            pureFunctionSimulationFacts function outFunction env1 env5 middle next t t2 gm g g3 l3 ck2
              fnResult targetFn pure fnCompile fnRun fnSafe targetFnRun fnRelated
          change ∀ v ∈ [f], valueWellFormed g3 l3 t2.code v at fnWell
          have fWell := fnWell f (by simp)
          change ∀ v ∈ values, valueWellFormed g2 l2 t.code v at argsWell
          change List.Forall₂ (valueRel g2 l2 t.code) values targetValues at argsRelated
          have appRun : ClosSem.evaluateApp (some loc) f values next = (result, last) := by
            rw [ClosSem.evaluate] at sourceRun
            simp only [nonempty, List.isEmpty_iff, ↓reduceIte] at sourceRun
            rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
            simp only at sourceRun
            rw [ClosSem.fixClock_evaluate, fnRun] at sourceRun
            simpa [ClosSem.headValue, holHd] using sourceRun
          have codeGrowth1 : t0.code.submap t.code := by
            simpa using ClosProps.CodeGrowthPort.evaluate_mono outArgs env2 {t0 with clock := t0.clock + ck}
              (.val targetValues) t targetArgsRun
          have codeGrowth2 : t.code.submap t2.code := by
            simpa using ClosProps.CodeGrowthPort.evaluate_mono [outFunction] env5 {t with clock := t.clock + ck2}
              (.val [targetF]) t2 targetFnRun
          have argsRelated' := listValueRel_subg g2 l2 t.code values targetValues g3 l3 t2.code
            ⟨argsRelated, growth3, allowed3, codeGrowth2⟩
          have included' := codeIncludes_submap g.2 t0.code t2.code
            ⟨included, HolFiniteMapExact.submap_trans codeGrowth1 codeGrowth2⟩
          obtain ⟨stubTrace, compiled, captured, targetDest, lookup⟩ :=
            directClosureFacts loc f targetF values targetValues next last t2 g g3 l3 result valuesNonempty appRun safe
              functionRelated argsRelated' wellG well3
              (stateExtends_trans g g2 g3 (stateExtends_trans g g1 g2 growth growth2) growth3)
              known disjoint3 included' states3
          obtain ⟨ck3, result', t3, g4, l4, inv4, stateWell4, resultWell, appTargetRun, states4,
            growth4, well4, allowed4, disjoint4, resultRelated⟩ :=
            appContinuationSimulation trace (some loc) function outFunction args env1 env5 s0 middle next last t t2
              g2 g3 l2 l3 ck2 values targetValues f targetF result appIH nonempty argsRun fnRun sourceRun safe
              targetFnRun inv3 stateWell3 growth3 allowed3 well3 disjoint3 fWell functionRelated argsWell argsRelated states3
          have len := ClosSem.evaluate_length.1 outArgs env2 {t0 with clock := t0.clock + ck} t targetValues targetArgsRun
          have callRun := pureDirectTargetRun trace stubTrace loc targetF targetValues captured outArgs env2 t0 t t2 t3
            ck ck2 ck3 compiled result' targetNonempty targetArgsRun targetNext targetDest lookup appTargetRun
          refine ⟨ck + ck2 + ck3, result', t3, g4, l4, inv4, stateWell4,
            stateExtends_trans g1 g3 g4 (stateExtends_trans g1 g2 g3 growth2 growth3) growth4,
            well4, Set.Subset.trans (Set.Subset.trans allowed2 allowed3) allowed4, disjoint4, resultWell,
            ?_, states4, resultRelated⟩
          simpa [len] using callRun
private theorem impureDirectTargetRun {C F : Type} (letTrace callTrace stubTrace : BackendCommon.Tra)
    (loc : Nat) (function : ClosSem.Value) (args captured : List ClosSem.Value)
    (argExps : List ClosLang.Exp) (outFunction : ClosLang.Exp) (env : List ClosSem.Value)
    (initial middle next last : ClosSem.State C F) (ck1 ck2 ck3 : Nat)
    (compiled : ClosLang.Exp) (result : Result (List ClosSem.Value) ClosSem.Value)
    (nonempty : args ≠ [])
    (argsRun : ClosSem.evaluate argExps env {initial with clock := initial.clock + ck1} = (.val args, middle))
    (fnRun : ClosSem.evaluate [outFunction] env {middle with clock := middle.clock + ck2} = (.val [function], next))
    (dest : ClosSem.destClosure next.maxApp (some loc) function args =
      some (.fullApp (.call stubTrace 0 (loc + 1) (variablesSource stubTrace 1 args.length)) (args ++ captured) []))
    (lookup : next.code.lookup (loc + 1) = some (args.length, compiled))
    (appRun : ClosSem.evaluateApp (some loc) function args {next with clock := next.clock + ck3} = (result, last)) :
    ClosSem.evaluate [.let letTrace (argExps ++ [outFunction])
      (.call callTrace args.length (loc + 1) (variablesSource .none 2 args.length))] env
      {initial with clock := initial.clock + (ck1 + ck2 + ck3)} = (result, last) := by
  have shiftedArgs := ClosSem.evaluate_addClock.1 argExps env {initial with clock := initial.clock + ck1}
    middle (.val args) (ck2 + ck3) argsRun (by simp)
  have shiftedFn := ClosSem.evaluate_addClock.1 [outFunction] env {middle with clock := middle.clock + ck2}
    next (.val [function]) ck3 fnRun (by simp)
  have shiftedArgs' : ClosSem.evaluate argExps env {initial with clock := initial.clock + (ck1 + ck2 + ck3)} =
      (.val args, {middle with clock := middle.clock + (ck2 + ck3)}) := by
    simpa [Nat.add_assoc] using shiftedArgs
  have shiftedFn' : ClosSem.evaluate [outFunction] env {middle with clock := middle.clock + (ck2 + ck3)} =
      (.val [function], {next with clock := next.clock + ck3}) := by
    simpa [Nat.add_assoc] using shiftedFn
  have varsRun : ClosSem.evaluate (variablesSource .none 2 args.length) (args ++ [function] ++ env)
      {next with clock := next.clock + ck3} = (.val args, {next with clock := next.clock + ck3}) := by
    simpa using evaluate_variables (args ++ [function] ++ env) {next with clock := next.clock + ck3} args.length .none 2
  have targetDest : ClosSem.destClosure ({next with clock := next.clock + ck3} : ClosSem.State C F).maxApp
      (some loc) function args =
      some (.fullApp (.call stubTrace 0 (loc + 1) (variablesSource stubTrace 1 args.length)) (args ++ captured) []) := by
    simpa using dest
  have targetLookup : ({next with clock := next.clock + ck3} : ClosSem.State C F).code.lookup (loc + 1) =
      some (args.length, compiled) := by simpa using lookup
  have callRun := directCallAfterArgs callTrace stubTrace loc function args captured (variablesSource .none 2 args.length)
    (args ++ [function] ++ env) {next with clock := next.clock + ck3} {next with clock := next.clock + ck3}
    compiled nonempty varsRun targetDest targetLookup
  rw [appRun] at callRun
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, ClosProps.evaluateSnoc, shiftedArgs']
  simp only
  rw [shiftedFn']
  simpa [List.append_assoc] using callRun.symm
private theorem finishImpureDirectApp {C F : Type} (trace letTrace callTrace : BackendCommon.Tra) (loc : Nat)
    (function outFunction : ClosLang.Exp) (args outArgs : List ClosLang.Exp)
    (env1 env2 : List ClosSem.Value) (s0 last : ClosSem.State (NumSet × C) F)
    (t0 : ClosSem.State C F) (g0 gm g g1 : State) (allowed : Set Nat)
    (result : Result (List ClosSem.Value) ClosSem.Value)
    (argsIH : ExprMotive args env1 s0)
    (fnIH : ∀ (state : ClosSem.State (NumSet × C) F), state.clock ≤ s0.clock → ExprMotive [function] env1 state)
    (appIH : ∀ (f : ClosSem.Value) (values : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock ≤ s0.clock → AppMotive (some loc) f values state)
    (known : sptDomain g.1 loc)
    (nonempty : args ≠ []) (sourceRun : ClosSem.evaluate [.app trace (some loc) function args] env1 s0 = (result, last))
    (safe : result ≠ .err (.abort .typeError))
    (argsCompile : calls args g0 = (outArgs, gm)) (fnCompile : calls [function] gm = ([outFunction], g))
    (invariant : codeInv (some g1) allowed s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle)
    (annotations : everyFnLocationSome [.app trace (some loc) function args])
    (noVars : everyFnVarsNone [.app trace (some loc) function args])
    (envWell : ∀ v ∈ env1, valueWellFormed g1 allowed t0.code v)
    (stateWell : stateValuesWellFormed g1 allowed t0.code s0) (well0 : wellFormed g0)
    (distinct : (codeLocations [.app trace (some loc) function args]).Nodup)
    (fresh : Disjoint (Set.image Nat.succ {n | n ∈ codeLocations [.app trace (some loc) function args]})
      {n | n ∈ g0.2.map Prod.fst})
    (bound : Set.Subset (Set.diff {n | n ∈ codeLocations [.app trace (some loc) function args]} (sptDomain g.1)) allowed)
    (growth : stateExtends g g1) (disjoint : Disjoint allowed (sptDomain g1.1)) (well1 : wellFormed g1)
    (argsEnv : envRel (valueRel g1 allowed t0.code) env1 env2 0 (outArgs.map (fun e => (0, e))))
    (fnEnv : envRel (valueRel g1 allowed t0.code) env1 env2 0 [(0, outFunction)])
    (states : stateRel g1 allowed s0 t0) (included : codeIncludes g.2 t0.code) :
    ∃ ck result' t g2 l2,
      codeInv (some g2) l2 last.code last.compile last.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code last ∧ stateExtends g1 g2 ∧ wellFormed g2 ∧
      allowed ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v) (valueWellFormed g2 l2 t.code) result ∧
      ClosSem.evaluate [.let letTrace (outArgs ++ [outFunction])
        (.call callTrace outArgs.length (loc + 1) (variablesSource .none 2 outArgs.length))] env2 {t0 with clock := t0.clock + ck} = (result', t) ∧
      stateRel g2 l2 last t ∧ resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) result result' := by
  obtain ⟨middleWell, _, _, fnDistinct, _, fnAnnotations, _, _, _, fnFresh, _, _⟩ :=
    appSequentialFacts trace (some loc) function args g0 gm g outArgs outFunction allowed argsCompile fnCompile
      annotations noVars distinct fresh well0 bound
  have wellG := calls_wellFormed [function] gm [outFunction] g
    ⟨fnCompile, fnDistinct, (by intro label h; exact Set.disjoint_left.mp fnFresh h.1 h.2), fnAnnotations, middleWell⟩
  cases argsRun : ClosSem.evaluate args env1 s0 with
  | mk argsResult middle =>
    obtain ⟨ck, targetArgs, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
      argsWell, targetArgsRun, states2, argsRelated⟩ :=
      appArgsSimulation trace (some loc) function outFunction args outArgs env1 env2 s0 middle last t0 g0 gm g g1 allowed
        argsResult result argsIH nonempty argsRun sourceRun safe argsCompile fnCompile invariant annotations noVars
        envWell stateWell well0 distinct fresh bound growth disjoint well1 argsEnv states included
    cases argsResult with
    | err error =>
      cases targetArgs with
      | val _ => exact False.elim argsRelated
      | err targetError =>
        have eq : (result, last) = (.err error, middle) := by
          rw [ClosSem.evaluate] at sourceRun
          simp only [nonempty, List.isEmpty_iff, ↓reduceIte] at sourceRun
          rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
          exact sourceRun.symm
        cases eq
        refine ⟨ck, .err targetError, t, g2, l2, inv2, stateWell2, growth2, well2, allowed2, disjoint2,
          argsWell, ?_, states2, argsRelated⟩
        exact directLetArgsErrorTargetRun letTrace outFunction
          (.call callTrace outArgs.length (loc + 1) (variablesSource .none 2 outArgs.length))
          outArgs env2 t0 t ck targetError targetArgsRun
    | val values =>
      cases targetArgs with
      | err _ => exact False.elim argsRelated
      | val targetValues =>
        have valuesNonempty : values ≠ [] := by
          intro empty
          have len := ClosProps.evaluateImpLength args env1 s0 middle values argsRun
          simp [empty] at len
          cases args with
          | nil => exact nonempty rfl
          | cons a rest => simp at len
        have targetNonempty : targetValues ≠ [] := by
          intro empty
          have len := argsRelated.length_eq
          simp [empty] at len
          exact valuesNonempty (by cases values <;> simp_all)
        cases fnRun : ClosSem.evaluate [function] env1 middle with
        | mk fnResult next =>
          obtain ⟨ck2, targetFn, t2, g3, l3, inv3, stateWell3, growth3, well3, allowed3, disjoint3,
            fnWell, targetFnRun, states3, fnRelated⟩ :=
            appFunctionSimulation trace (some loc) function outFunction args outArgs env1 env2 env2 s0 middle next last t0 t
              g0 gm g g1 g2 allowed l2 ck values (.val targetValues) fnResult result fnIH nonempty argsRun fnRun
              sourceRun safe argsCompile fnCompile targetArgsRun inv2 annotations noVars envWell stateWell2 well0
              distinct fresh bound growth growth2 allowed2 disjoint2 well2 fnEnv states2 included
          cases fnResult with
          | err error =>
            cases targetFn with
            | val _ => exact False.elim fnRelated
            | err targetError =>
              have eq : (result, last) = (.err error, next) := by
                rw [ClosSem.evaluate] at sourceRun
                simp only [nonempty, List.isEmpty_iff, ↓reduceIte] at sourceRun
                rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
                simp only at sourceRun
                rw [ClosSem.fixClock_evaluate, fnRun] at sourceRun
                exact sourceRun.symm
              cases eq
              exact ⟨ck + ck2, .err targetError, t2, g3, l3, inv3, stateWell3,
                stateExtends_trans g1 g2 g3 growth2 growth3, well3, Set.Subset.trans allowed2 allowed3, disjoint3,
                fnWell, directLetFunctionErrorTargetRun letTrace outFunction
                  (.call callTrace outArgs.length (loc + 1) (variablesSource .none 2 outArgs.length))
                  outArgs env2 t0 t t2 ck ck2 targetValues targetError targetArgsRun targetFnRun, states3, fnRelated⟩
          | val fnValues =>
            cases targetFn with
            | err _ => exact False.elim fnRelated
            | val targetFnValues =>
              obtain ⟨f, rfl⟩ := ClosProps.evaluateSing function env1 middle next fnValues fnRun
              obtain ⟨targetF, rfl⟩ := ClosProps.evaluateSing outFunction env2
                {t with clock := t.clock + ck2} t2 targetFnValues targetFnRun
              change List.Forall₂ (valueRel g3 l3 t2.code) [f] [targetF] at fnRelated
              cases fnRelated with
              | cons functionRelated rest =>
                cases rest
                change ∀ v ∈ [f], valueWellFormed g3 l3 t2.code v at fnWell
                have fWell := fnWell f (by simp)
                change ∀ v ∈ values, valueWellFormed g2 l2 t.code v at argsWell
                change List.Forall₂ (valueRel g2 l2 t.code) values targetValues at argsRelated
                have appRun : ClosSem.evaluateApp (some loc) f values next = (result, last) := by
                  rw [ClosSem.evaluate] at sourceRun
                  simp only [nonempty, List.isEmpty_iff, ↓reduceIte] at sourceRun
                  rw [ClosSem.fixClock_evaluate, argsRun] at sourceRun
                  simp only at sourceRun
                  rw [ClosSem.fixClock_evaluate, fnRun] at sourceRun
                  simpa [ClosSem.headValue, holHd] using sourceRun
                have codeGrowth1 : t0.code.submap t.code := by
                  simpa using ClosProps.CodeGrowthPort.evaluate_mono outArgs env2 {t0 with clock := t0.clock + ck}
                    (.val targetValues) t targetArgsRun
                have codeGrowth2 : t.code.submap t2.code := by
                  simpa using ClosProps.CodeGrowthPort.evaluate_mono [outFunction] env2 {t with clock := t.clock + ck2}
                    (.val [targetF]) t2 targetFnRun
                have argsRelated' := listValueRel_subg g2 l2 t.code values targetValues g3 l3 t2.code
                  ⟨argsRelated, growth3, allowed3, codeGrowth2⟩
                have included' := codeIncludes_submap g.2 t0.code t2.code
                  ⟨included, HolFiniteMapExact.submap_trans codeGrowth1 codeGrowth2⟩
                obtain ⟨stubTrace, compiled, captured, targetDest, lookup⟩ :=
                  directClosureFacts loc f targetF values targetValues next last t2 g g3 l3 result valuesNonempty appRun safe
                    functionRelated argsRelated' wellG well3
                    (stateExtends_trans g g2 g3 (stateExtends_trans g g1 g2 growth growth2) growth3)
                    known disjoint3 included' states3
                obtain ⟨ck3, result', t3, g4, l4, inv4, stateWell4, resultWell, appTargetRun, states4,
                  growth4, well4, allowed4, disjoint4, resultRelated⟩ :=
                  appContinuationSimulation trace (some loc) function outFunction args env1 env2 s0 middle next last t t2
                    g2 g3 l2 l3 ck2 values targetValues f targetF result appIH nonempty argsRun fnRun sourceRun safe
                    targetFnRun inv3 stateWell3 growth3 allowed3 well3 disjoint3 fWell functionRelated argsWell argsRelated states3
                have len := ClosSem.evaluate_length.1 outArgs env2 {t0 with clock := t0.clock + ck} t targetValues targetArgsRun
                have callRun := impureDirectTargetRun letTrace callTrace stubTrace loc targetF targetValues captured outArgs outFunction env2 t0 t t2 t3
                  ck ck2 ck3 compiled result' targetNonempty targetArgsRun targetFnRun targetDest lookup appTargetRun
                refine ⟨ck + ck2 + ck3, result', t3, g4, l4, inv4, stateWell4,
                  stateExtends_trans g1 g3 g4 (stateExtends_trans g1 g2 g3 growth2 growth3) growth4,
                  well4, Set.Subset.trans (Set.Subset.trans allowed2 allowed3) allowed4, disjoint4, resultWell,
                  ?_, states4, resultRelated⟩
                simpa [len] using callRun
private theorem appExpressionCase {C F : Type} (trace : BackendCommon.Tra) (loc : Option Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) (env1 : List ClosSem.Value)
    (s0 : ClosSem.State (NumSet × C) F) (argsIH : ExprMotive args env1 s0)
    (fnIH : ∀ (state : ClosSem.State (NumSet × C) F), state.clock ≤ s0.clock → ExprMotive [function] env1 state)
    (appIH : ∀ (f : ClosSem.Value) (values : List ClosSem.Value) (state : ClosSem.State (NumSet × C) F),
      state.clock ≤ s0.clock → AppMotive loc f values state) : ExprMotive [.app trace loc function args] env1 s0 := by
  intro tmp g0 g env2 t0 ys res last l allowed g1 h
  rcases h with ⟨_, sourceRun, safe, compileRun, invariant, annotations, noVars, envWell, stateWell,
    well0, distinct, fresh, locations, growth, bound, disjoint, well1, envRelated, states, included⟩
  subst l
  by_cases nonempty : args ≠ []
  · cases argsCompile : calls args g0 with
    | mk outArgs gm =>
      have argsSing : callsSingList args g0 = (outArgs, gm) := argsCompile
      cases fnCompile : calls [function] gm with
      | mk outFn gfinal =>
        obtain ⟨outFunction, rfl⟩ := calls_sing function gm outFn gfinal fnCompile
        have fnSing : callsSing function gm = (outFunction, gfinal) := by
          have eq := fnCompile
          simp only [calls, callsSingList, Prod.mk.injEq, List.cons.injEq, and_true] at eq
          exact Prod.ext eq.1 eq.2
        cases loc with
        | none =>
          simp only [calls, callsSingList, callsSing, argsSing, fnSing, Prod.mk.injEq] at compileRun
          obtain ⟨rfl, rfl⟩ := compileRun
          obtain ⟨argsEnv, fnEnv⟩ := normalAppEnvRel (valueRel g1 allowed t0.code) env1 env2
            trace none outFunction outArgs (by simpa using envRelated)
          exact finishNormalApp trace none function outFunction args outArgs env1 env2 s0 last t0 g0 gm gfinal g1 allowed
            res argsIH fnIH appIH nonempty sourceRun safe argsCompile fnCompile invariant annotations noVars envWell
            stateWell well0 distinct fresh bound growth disjoint well1 argsEnv fnEnv states included
        | some loc =>
          by_cases known : (sptLookup loc gfinal.1).isSome = true
          · by_cases pure : ClosLang.pure function = true
            · simp only [calls, callsSingList, callsSing, argsSing, fnSing, known, pure, ↓reduceIte,
                Prod.mk.injEq] at compileRun
              obtain ⟨rfl, rfl⟩ := compileRun
              have argsEnv := callArgsEnvRel (valueRel g1 allowed t0.code) env1 env2 trace outArgs.length (loc + 1) outArgs
                (by simpa using envRelated)
              exact finishPureDirectApp trace loc function outFunction args outArgs env1 env2 s0 last t0 g0 gm gfinal g1 allowed
                res argsIH fnIH appIH pure (by simpa [sptDomain] using known) nonempty sourceRun safe argsCompile fnCompile
                invariant annotations noVars envWell stateWell well0 distinct fresh bound growth disjoint well1 argsEnv states included
            · simp only [calls, callsSingList, callsSing, argsSing, fnSing, known, pure, Bool.false_eq_true, ↓reduceIte,
                Prod.mk.injEq] at compileRun
              obtain ⟨rfl, rfl⟩ := compileRun
              obtain ⟨argsEnv, fnEnv⟩ := letAppEnvRel (valueRel g1 allowed t0.code) env1 env2
                (BackendCommon.mkCons trace 0) outArgs outFunction
                (.call (BackendCommon.mkCons trace 1) outArgs.length (loc + 1) (variablesSource .none 2 outArgs.length))
                (by simpa using envRelated)
              exact finishImpureDirectApp trace (BackendCommon.mkCons trace 0) (BackendCommon.mkCons trace 1) loc
                function outFunction args outArgs env1 env2 s0 last t0 g0 gm gfinal g1 allowed res argsIH fnIH appIH
                (by simpa [sptDomain] using known) nonempty sourceRun safe argsCompile fnCompile invariant annotations noVars
                envWell stateWell well0 distinct fresh bound growth disjoint well1 argsEnv fnEnv states included
          · simp only [calls, callsSingList, callsSing, argsSing, fnSing, known, Bool.false_eq_true, ↓reduceIte,
              Prod.mk.injEq] at compileRun
            obtain ⟨rfl, rfl⟩ := compileRun
            obtain ⟨argsEnv, fnEnv⟩ := normalAppEnvRel (valueRel g1 allowed t0.code) env1 env2
              trace (some loc) outFunction outArgs (by simpa using envRelated)
            exact finishNormalApp trace (some loc) function outFunction args outArgs env1 env2 s0 last t0 g0 gm gfinal g1 allowed
              res argsIH fnIH appIH nonempty sourceRun safe argsCompile fnCompile invariant annotations noVars envWell
              stateWell well0 distinct fresh bound growth disjoint well1 argsEnv fnEnv states included
  · have empty : args = [] := by simpa using nonempty
    subst args
    simp [ClosSem.evaluate, ClosSem.typeError] at sourceRun
    obtain ⟨rfl, rfl⟩ := sourceRun
    exact (safe rfl).elim
private theorem callsCorrectMotive {C F : Type} :
    (∀ xs env (state : ClosSem.State (NumSet × C) F), ExprMotive xs env state) ∧
    (∀ loc f args (state : ClosSem.State (NumSet × C) F), AppMotive loc f args state) := by
  have parts := clockWeightAppInduction (α := List ClosLang.Exp)
    (β := Option Nat × ClosSem.Value × List ClosSem.Value) (σ := ClosSem.State (NumSet × C) F)
    (·.clock) ClosSem.expsWeight
    (motiveE := fun expressions state => ∀ env, ExprMotive expressions env state)
    (motiveA := fun b state => AppMotive b.1 b.2.1 b.2.2 state) ?_ ?_
  · exact ⟨fun xs env state => parts.1 xs state env,
      fun loc f args state => parts.2 (loc, f, args) state⟩
  · intro b state bodyIH appIH
    obtain ⟨loc, f, args⟩ := b
    apply appCase loc f args state
    · intro e env next smaller
      exact bodyIH [e] next smaller env
    · intro f args next smaller
      exact appIH (loc, f, args) next smaller
  · intro expressions state exprIH smaller appIH env
    cases expressions with
    | nil =>
      intro tmp g0 g env2 t0 ys res last l l1 g1 h
      exact nilCase tmp env state g0 g env2 t0 ys res last l l1 g1 h
    | cons first rest =>
      cases rest with
      | cons second tail =>
        apply listCaseFromWeight first second tail env state
        intro es next bound weight
        exact exprIH es next bound weight env
      | nil =>
        cases first with
        | var trace index => exact varCase trace index env state
        | fn name loc vars arity body => exact fnCase name loc vars arity body env state
        | raise trace body =>
          apply raiseCase trace body env state
          apply exprIH [body] state (Nat.le_refl _) ?_ env
          simp only [ClosSem.expsWeight, ClosSem.expWeight]; omega
        | tick trace body =>
          apply tickCase trace body env state
          intro next clock
          exact smaller [body] next clock env
        | call trace ticks loc args =>
          apply callCase trace ticks loc args env state
          apply exprIH args state (Nat.le_refl _) ?_ env
          simp only [ClosSem.expsWeight, ClosSem.expWeight]; omega
        | «let» trace bindings body =>
          apply letCase trace bindings body env state
          · apply exprIH bindings state (Nat.le_refl _) ?_ env
            simp only [ClosSem.expsWeight, ClosSem.expWeight]; omega
          · intro env' next clock
            apply exprIH [body] next clock ?_ env'
            simp only [ClosSem.expsWeight, ClosSem.expWeight]; omega
        | letrec names loc vars fns body =>
          apply letrecCase names loc vars fns body env state
          intro env'
          apply exprIH [body] state (Nat.le_refl _) ?_ env'
          simp only [ClosSem.expsWeight, ClosSem.expWeight]; omega
        | handle trace body handler =>
          apply handleCase trace body handler env state
          · apply exprIH [body] state (Nat.le_refl _) ?_ env
            simp only [ClosSem.expsWeight, ClosSem.expWeight]; omega
          · intro env' next clock
            apply exprIH [handler] next clock ?_ env'
            simp only [ClosSem.expsWeight, ClosSem.expWeight]; omega
        | ifThenElse trace cond yes no =>
          apply ifCase trace cond yes no env state
          · apply exprIH [cond] state (Nat.le_refl _) ?_ env
            simp only [ClosSem.expsWeight, ClosSem.expWeight]; omega
          · intro branch next branchCase clock
            apply exprIH [branch] next clock ?_ env
            rcases branchCase with rfl | rfl <;> simp only [ClosSem.expsWeight, ClosSem.expWeight] <;> omega
        | app trace loc function args =>
          apply appExpressionCase trace loc function args env state
          · apply exprIH args state (Nat.le_refl _) ?_ env
            simp only [ClosSem.expsWeight, ClosSem.expWeight]; omega
          · intro next clock
            apply exprIH [function] next clock ?_ env
            simp only [ClosSem.expsWeight, ClosSem.expWeight]; omega
          · intro f args next clock
            exact appIH (loc, f, args) next clock
        | op trace op args =>
          have argsIH : ExprMotive args env state := by
            apply exprIH args state (Nat.le_refl _) ?_ env
            simpa [ClosSem.expsWeight] using ClosSem.opWeight_gt trace op args
          by_cases install : op = .install
          · subst op
            apply installCase trace args env state argsIH
            intro es next clock
            exact smaller es next clock []
          · by_cases force : op = .thunkOp .forceThunk
            · subst op
              apply forceThunkCase trace args env state argsIH
              intro value next clock
              apply exprIH [ClosSem.appUnit (.var .none 0)] next clock ?_ [value]
              simp [ClosSem.appUnit, ClosSem.expsWeight, ClosSem.expWeight]; omega
            · exact ordinaryOpCase trace op args env state argsIH install force
/-- Full direct-call simulation for expression lists and closure application.
The unused application-location binder retains its independent HOL type. The
evaluator inherits the real-model assumption recorded in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_correct"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code])]
theorem callsCorrect {C F : Type} :
  (∀ (tmp : List ClosLang.Exp × List ClosSem.Value × ClosSem.State (NumSet × C) F)
    (xs : List ClosLang.Exp) (env1 : List ClosSem.Value) (s0 : ClosSem.State (NumSet × C) F)
    (g0 g : State) (env2 : List ClosSem.Value) (t0 : ClosSem.State C F) (ys : List ClosLang.Exp)
    (res : Flapjack.SemanticPrimitivesHOL.Result (List ClosSem.Value) ClosSem.Value)
    (s : ClosSem.State (NumSet × C) F) (l l1 : Set Nat) (g1 : State),
    tmp = (xs, env1, s0) ∧ ClosSem.evaluate xs env1 s0 = (res, s) ∧
      res ≠ .err (.abort .typeError) ∧ calls xs g0 = (ys, g) ∧
      codeInv (some g1) l1 s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle ∧
      everyFnLocationSome xs ∧ everyFnVarsNone xs ∧
      (∀ v ∈ env1, valueWellFormed g1 l1 t0.code v) ∧ stateValuesWellFormed g1 l1 t0.code s0 ∧
      wellFormed g0 ∧ (codeLocations xs).Nodup ∧
      Disjoint (Set.image Nat.succ {x | x ∈ codeLocations xs}) {x | x ∈ g0.2.map Prod.fst} ∧
      l = {x | x ∈ codeLocations xs} \ sptDomain g.1 ∧
      stateExtends g g1 ∧ l ⊆ l1 ∧ Disjoint l1 (sptDomain g1.1) ∧ wellFormed g1 ∧
      envRel (valueRel g1 l1 t0.code) env1 env2 0 (ys.map (fun x => (0, x))) ∧
      stateRel g1 l1 s0 t0 ∧ codeIncludes g.2 t0.code →
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 s.code s.compile s.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code s ∧
      stateExtends g1 g2 ∧ wellFormed g2 ∧ l1 ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      Flapjack.SemanticPrimitivesProps.everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) res ∧
      ClosSem.evaluate ys env2 {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 s t ∧
      Flapjack.SemanticPrimitivesProps.resultRel (List.Forall₂ (valueRel g2 l2 t.code))
        (valueRel g2 l2 t.code) res res') ∧
  (∀ (loco : Option Nat) (f : ClosSem.Value) (args : List ClosSem.Value)
    (s0 : ClosSem.State (NumSet × C) F),
    ∀ {L : Type} (_loc : L) (g : State) (l : Set Nat) (t0 : ClosSem.State C F)
    (res : Result (List ClosSem.Value) ClosSem.Value) (s : ClosSem.State (NumSet × C) F)
    (f' : ClosSem.Value) (args' : List ClosSem.Value),
    ClosSem.evaluateApp loco f args s0 = (res, s) ∧ res ≠ .err (.abort .typeError) ∧
      codeInv (some g) l s0.code s0.compile s0.compileOracle t0.code t0.compile t0.compileOracle ∧
      valueWellFormed g l t0.code f ∧ (∀ a ∈ args, valueWellFormed g l t0.code a) ∧
      stateValuesWellFormed g l t0.code s0 ∧ wellFormed g ∧ Disjoint l (sptDomain g.1) ∧
      valueRel g l t0.code f f' ∧ List.Forall₂ (valueRel g l t0.code) args args' ∧ stateRel g l s0 t0 →
    ∃ ck res' t g2 l2,
      codeInv (some g2) l2 s.code s.compile s.compileOracle t.code t.compile t.compileOracle ∧
      stateValuesWellFormed g2 l2 t.code s ∧
      everyResult (fun vs => ∀ v ∈ vs, valueWellFormed g2 l2 t.code v)
        (valueWellFormed g2 l2 t.code) res ∧
      ClosSem.evaluateApp loco f' args' {t0 with clock := t0.clock + ck} = (res', t) ∧
      stateRel g2 l2 s t ∧ stateExtends g g2 ∧ wellFormed g2 ∧ l ⊆ l2 ∧ Disjoint l2 (sptDomain g2.1) ∧
      resultRel (List.Forall₂ (valueRel g2 l2 t.code)) (valueRel g2 l2 t.code) res res') := by
  constructor
  · intro tmp xs env1 s0 g0 g env2 t0 ys res s l l1 g1 h
    exact callsCorrectMotive.1 xs env1 s0 tmp g0 g env2 t0 ys res s l l1 g1 h
  · exact callsCorrectMotive.2
end Flapjack.Compiler.Backend.ClosCall
