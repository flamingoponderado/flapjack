import Flapjack.Compiler.Backend.FlatElim.Proofs.TotalPattern

/-! State invariants for pure expressions that only initialize unreachable
globals. -/
namespace Flapjack.Compiler.Backend.FlatElim
open Flapjack.SemanticPrimitivesHOL

/-- Initializing an unreachable, empty source slot preserves its relation to
the unchanged target globals. This is a Flapjack helper for the pure-expression
simulation. -/
theorem globalsRel_set_unreachable (reachable : NumSet) (source target : List (Option FlatSem.Value))
    (index : Nat) (value : FlatSem.Value) (related : globalsRel reachable source target)
    (sourceEmpty : source[index]? = some none) (unreachable : ¬ sptMem index reachable) :
    globalsRel reachable (source.set index (some value)) target := by
  have sourceBound : index < source.length := (List.getElem?_eq_some_iff.mp sourceEmpty).choose
  obtain ⟨lengths, same, present, empty, contents⟩ := related
  have targetBound : index < target.length := by omega
  have targetEmpty : target[index]?.getD none = none := by
    apply empty index targetBound
    simp [sourceEmpty]
  refine ⟨by simpa using lengths, ?_, ?_, ?_, contents⟩
  · intro n inReachable bound
    have ne : index ≠ n := by
      intro sameIndex
      subst n
      exact unreachable inReachable
    simpa [List.getElem?_set_ne ne] using same n inReachable bound
  · intro n v bound found
    by_cases eq : n = index
    · subst n
      rw [targetEmpty] at found
      contradiction
    · simpa [List.getElem?_set_ne (Ne.symm eq)] using present n v bound found
  · intro n bound isEmpty
    by_cases eq : n = index
    · subst n
      simp [sourceBound] at isEmpty
    · simp only [List.getElem?_set_ne (Ne.symm eq)] at isEmpty
      exact empty n bound isEmpty

/-- Updating only an unreachable source global preserves the full flat state
relation. This is a Flapjack helper for the pure-expression simulation. -/
theorem flatStateRel_set_unreachable {C F : Type} (reachable : NumSet) (source target : FlatSem.State C F)
    (index : Nat) (value : FlatSem.Value) (related : flatStateRel reachable source target)
    (sourceEmpty : source.globals[index]? = some none) (unreachable : ¬ sptMem index reachable) :
    flatStateRel reachable { source with globals := source.globals.set index (some value) } target := by
  obtain ⟨clock, refs, ffi, globals, refsClosed, refsSafe⟩ := related
  exact ⟨clock, refs, ffi, globalsRel_set_unreachable reachable source.globals target.globals index value
    globals sourceEmpty unreachable, refsClosed, refsSafe⟩

/-- A successful initialization of an unreachable global returns an Eval-free
unit value and leaves the source related to the unchanged target. This is a
Flapjack helper for the pure-expression simulation. -/
theorem applyResult_globalInit_unreachable {C F : Type} (reachable : NumSet)
    (source target next : FlatSem.State C F) (index : Nat) (values : List FlatSem.Value)
    (result : Result (List FlatSem.Value) FlatSem.Value)
    (related : flatStateRel reachable source target) (unreachable : ¬ sptMem index reachable)
    (run : FlatSem.applyResult source (.globalVarInit index) values = (next, result))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ outputs, flatStateRel reachable next target ∧ result = .val outputs ∧ valuesNoEval outputs := by
  cases values with
  | nil =>
    simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat] at run
    rcases run with ⟨_, rfl⟩
    exact (notTypeError rfl).elim
  | cons value rest =>
    cases rest with
    | cons other rest =>
      simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat] at run
      rcases run with ⟨_, rfl⟩
      exact (notTypeError rfl).elim
    | nil =>
      cases lookup : source.globals[index]? with
      | none =>
        simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, lookup] at run
        rcases run with ⟨_, rfl⟩
        exact (notTypeError rfl).elim
      | some entry =>
        cases entry with
        | some old =>
          simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, lookup] at run
          rcases run with ⟨_, rfl⟩
          exact (notTypeError rfl).elim
        | none =>
          simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, lookup] at run
          rcases run with ⟨rfl, rfl⟩
          refine ⟨[FlatSem.unitValue], flatStateRel_set_unreachable reachable source target index value related lookup unreachable, rfl, ?_⟩
          simp [valuesNoEval, FlatSem.unitValue, valueHasEval, valuesHaveEval]

/-- The pure-expression simulation at a fixed source state. This Flapjack
predicate exposes the clock and expression-weight induction hypotheses. -/
def pureEvaluationSimulationAt {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (expressions : List FlatLang.Exp) : Prop :=
  ∀ (next : FlatSem.State C F) (result : Result (List FlatSem.Value) FlatSem.Value)
    (reachable : NumSet) (target : FlatSem.State C F),
    FlatSem.evaluate env source expressions = (next, result) →
    (∀ expression ∈ expressions, isPure expression = true) → bindingsNoEval env.v →
    expressionsNoEval expressions →
    (∀ expression ∈ expressions, sptIsEmpty (sptInter (findLoc expression) reachable) = true) →
    flatStateRel reachable source target → result ≠ .err (.abort .typeError) →
    ∃ values, flatStateRel reachable next target ∧ result = .val values ∧ valuesNoEval values

/-- Empty expression lists satisfy the pure-evaluation induction step. -/
theorem pureEvaluation_empty {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) : pureEvaluationSimulationAt env source [] := by
  intro next result reachable target run _ _ _ _ related _
  simp [FlatSem.evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨[], related, rfl, by simp [valuesNoEval]⟩

/-- Literals satisfy the pure-evaluation induction step. -/
theorem pureEvaluation_lit {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (literal : Flapjack.AstHOL.Lit) :
    pureEvaluationSimulationAt env source [.lit tra literal] := by
  intro next result reachable target run _ _ _ _ related _
  simp [FlatSem.evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨[.litv literal], related, rfl, by simp [valuesNoEval, valueHasEval]⟩

/-- Local-variable lookup satisfies the pure-evaluation induction step. -/
theorem pureEvaluation_var {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (tra : BackendCommon.Tra) (name : Flapjack.AstHOL.VarN) :
    pureEvaluationSimulationAt env source [.varLocal tra name] := by
  intro next result reachable target run _ envSafe _ _ related notTypeError
  cases lookup : env.v.lookup name with
  | none =>
    simp [FlatSem.evaluate, lookup] at run
    rcases run with ⟨_, rfl⟩
    exact (notTypeError rfl).elim
  | some value =>
    simp [FlatSem.evaluate, lookup] at run
    rcases run with ⟨rfl, rfl⟩
    have member : (name, value) ∈ env.v := by
      obtain ⟨before, after, h, _⟩ := List.lookup_eq_some_iff.mp lookup
      rw [h]
      simp
    exact ⟨[value], related, rfl, by simpa [valuesNoEval] using envSafe (name, value) member⟩

/-- Closure creation satisfies the pure-evaluation induction step. -/
theorem pureEvaluation_fn {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (name argument : Flapjack.AstHOL.VarN) (body : FlatLang.Exp) :
    pureEvaluationSimulationAt env source [.fn name argument body] := by
  intro next result reachable target run _ envSafe expressionsSafe _ related _
  simp [FlatSem.evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  have bodySafe : hasEval body = false := by
    have h := expressionsSafe (.fn name argument body) (by simp)
    simpa [hasEval] using h
  have envValuesSafe : valuesNoEval (env.v.map Prod.snd) := by
    intro value member
    obtain ⟨binding, bindingMember, eq⟩ := List.mem_map.mp member
    subst value
    exact envSafe binding bindingMember
  have envBindingsSafe : bindingsHaveEval env.v = false := by
    rw [bindingsHaveEval_eq_map]
    exact (valuesHaveEval_eq_false_iff _).mpr envValuesSafe
  have closureSafe : valueHasEval (.closure env argument body) = false := by
    cases env with
    | mk bindings => simp [valueHasEval, envBindingsSafe, bodySafe]
  exact ⟨[.closure env argument body], related, rfl, by simpa [valuesNoEval] using closureSafe⟩

/-- Clamping the clock after a pure step leaves the resulting state unchanged
when both the initial and resulting states relate to the same target. -/
theorem fixClock_of_same_target {C F : Type} (reachable : NumSet)
    (source next target : FlatSem.State C F) (result : Result (List FlatSem.Value) FlatSem.Value)
    (initial : flatStateRel reachable source target) (after : flatStateRel reachable next target) :
    FlatSem.fixClock source (next, result) = (next, result) := by
  have clocks : source.clock = next.clock := initial.1.trans after.1.symm
  simp [FlatSem.fixClock, clocks]

/-- The non-singleton list induction step for pure evaluation. The tail
hypothesis is stated at the resulting state of the head evaluation. -/
theorem pureEvaluation_list {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (headIH : pureEvaluationSimulationAt env source [first])
    (tailIH : ∀ (next : FlatSem.State C F), next.clock ≤ source.clock →
      pureEvaluationSimulationAt env next (second :: rest)) :
    pureEvaluationSimulationAt env source (first :: second :: rest) := by
  intro next result reachable target run expressionsPure envSafe expressionsSafe locationsEmpty related notTypeError
  have headPure : ∀ expression ∈ [first], isPure expression = true := by
    intro expression member
    simp only [List.mem_singleton] at member
    subst expression
    exact expressionsPure first (by simp)
  have tailPure : ∀ expression ∈ second :: rest, isPure expression = true := by
    intro expression member
    exact expressionsPure expression (by simp [member])
  have headSafe : expressionsNoEval [first] := by
    intro expression member
    simp only [List.mem_singleton] at member
    subst expression
    exact expressionsSafe first (by simp)
  have tailSafe : expressionsNoEval (second :: rest) := by
    intro expression member
    exact expressionsSafe expression (by simp [member])
  have headEmpty : ∀ expression ∈ [first], sptIsEmpty (sptInter (findLoc expression) reachable) = true := by
    intro expression member
    simp only [List.mem_singleton] at member
    subst expression
    exact locationsEmpty first (by simp)
  have tailEmpty : ∀ expression ∈ second :: rest, sptIsEmpty (sptInter (findLoc expression) reachable) = true := by
    intro expression member
    exact locationsEmpty expression (by simp [member])
  cases headEval : FlatSem.evaluate env source [first] with
  | mk headState headResult =>
    simp only [FlatSem.evaluate, headEval, FlatSem.fixClock] at run
    have headNotTypeError : headResult ≠ .err (.abort .typeError) := by
      intro bad
      subst headResult
      simp at run
      rcases run with ⟨_, rfl⟩
      exact notTypeError rfl
    obtain ⟨heads, headRelated, headResultEq, headsSafe⟩ :=
      headIH headState headResult reachable target headEval headPure envSafe headSafe headEmpty related headNotTypeError
    subst headResult
    obtain ⟨head, rfl⟩ := Flapjack.Compiler.Backend.FlatProps.evaluate_sing env source headState first heads headEval
    have clocks : source.clock = headState.clock := related.1.trans headRelated.1.symm
    simp only [clocks, Nat.min_self] at run
    cases tailEval : FlatSem.evaluate env headState (second :: rest) with
    | mk tailState tailResult =>
      simp only [tailEval] at run
      have tailNotTypeError : tailResult ≠ .err (.abort .typeError) := by
        intro bad
        subst tailResult
        simp at run
        rcases run with ⟨_, rfl⟩
        exact notTypeError rfl
      obtain ⟨tailValues, tailRelated, tailResultEq, tailValuesSafe⟩ :=
        tailIH headState (by omega) tailState tailResult reachable target tailEval tailPure envSafe tailSafe tailEmpty headRelated tailNotTypeError
      subst tailResult
      simp at run
      rcases run with ⟨rfl, rfl⟩
      refine ⟨head :: tailValues, tailRelated, rfl, ?_⟩
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact headsSafe value (by simp)
      · exact tailValuesSafe value member

/-- An intersection is empty exactly when the trees share no key. The
intersection is well formed even when either input tree is not. -/
theorem interEmpty_iff_disjoint {α β : Type} (left : Spt α) (right : Spt β) :
    sptIsEmpty (sptInter left right) = true ↔
      ∀ key, sptMem key left → sptMem key right → False := by
  constructor
  · intro empty key leftMem rightMem
    cases leftFound : sptLookup key left with
    | none => simp [sptMem, sptDomain, leftFound] at leftMem
    | some value =>
      cases rightFound : sptLookup key right with
      | none => simp [sptMem, sptDomain, rightFound] at rightMem
      | some other =>
        have found : sptLookup key (sptInter left right) = some value := by
          simp [sptLookup_sptInterCases, leftFound, rightFound]
        cases treeEq : sptInter left right <;> simp [treeEq, sptIsEmpty] at empty
        rw [treeEq] at found
        simp [sptLookup] at found
  · intro disjoint
    have treeEmpty : sptInter left right = .ln := by
      apply sptWf_empty_of_lookup _ (sptWfInter _ _)
      intro key
      cases leftFound : sptLookup key left with
      | none => simp [sptLookup_sptInterCases, leftFound]
      | some value =>
        cases rightFound : sptLookup key right with
        | none => simp [sptLookup_sptInterCases, leftFound, rightFound]
        | some other =>
          have leftMem : sptMem key left := by simp [sptMem, sptDomain, leftFound]
          have rightMem : sptMem key right := by simp [sptMem, sptDomain, rightFound]
          exact (disjoint key leftMem rightMem).elim
    simp [treeEmpty, sptIsEmpty]

/-- A member expression's locations occur in the list analysis. -/
theorem findLocList_member (expressions : List FlatLang.Exp) (expression : FlatLang.Exp)
    (member : expression ∈ expressions) (key : Nat) (found : sptMem key (findLoc expression)) :
    sptMem key (findGlobalsList destGlobalVarInit expressions) := by
  induction expressions with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    simp only [findGlobalsList, sptMem_sptUnion]
    rcases member with same | member
    · subst expression
      exact Or.inl found
    · exact Or.inr (ih member)

/-- If an expression list has no location in the reachable set, each member
expression has the same property. -/
theorem findLocList_disjoint (expressions : List FlatLang.Exp) (reachable : NumSet)
    (empty : sptIsEmpty (sptInter (findGlobalsList destGlobalVarInit expressions) reachable) = true) :
    ∀ expression ∈ expressions, sptIsEmpty (sptInter (findLoc expression) reachable) = true := by
  intro expression member
  apply (interEmpty_iff_disjoint _ _).mpr
  intro key found reachableKey
  exact (interEmpty_iff_disjoint _ _).mp empty key (findLocList_member expressions expression member key found) reachableKey

end Flapjack.Compiler.Backend.FlatElim
