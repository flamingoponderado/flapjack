import Flapjack.Compiler.Backend.BviTmc.Proofs.StructuralCases
import Flapjack.Compiler.Backend.BviTmc.Proofs.LetCallSimulation

/-! Assembly of the structural and clock induction cases for TMC. -/
namespace Flapjack.Compiler.Backend.BviTmc.Induction
open BviTmc BviSem BvlSem ListSimulation ClockHypothesis StructuralHypothesis StructuralCases SemanticPrimitivesProps ResultRelation

/-- Flapjack infrastructure: all singleton expression cases from the common
smaller-weight and smaller-clock induction hypotheses. -/
theorem singleton_from_induction {C F : Type} (loc : Nat) (e : Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [e] env1 source = (result, final)) (notTypeError : result ≠ .err (.abort .typeError))
    (safe : noMutcons e) (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [e]))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost e source target env1 env2 opt f loc result final := by
  cases e with
  | var index => exact evaluate_variable_post loc index source target env1 env2 opt f result final run notTypeError environments states
  | ifThenElse condition yes no =>
    exact evaluate_if_from_weight loc condition yes no source target env1 env2 opt f result final run notTypeError safe environments states weightIH
  | «let» bindings body =>
    exact evaluate_let_from_weight loc bindings body source target env1 env2 opt f result final run notTypeError safe environments states weightIH
  | raise body =>
    exact evaluate_raise_from_weight loc body source target env1 env2 opt f result final run notTypeError safe environments states weightIH
  | tick body =>
    exact evaluate_tick_from_clock loc body source target env1 env2 opt f result final run notTypeError safe environments states clockIH
  | call ticks destination args handler =>
    exact CallSimulation.evaluate_call_from_induction loc ticks destination args handler source final target env1 env2 opt f result
      run notTypeError safe environments states weightIH clockIH
  | force location index =>
    exact ForceSimulation.evaluate_force_from_clock loc location index source target env1 env2 opt f result final run notTypeError environments states clockIH
  | op op args =>
    cases extracted : toBlockSource env1.length loc (.op op args) with
    | none => exact evaluate_op_from_weight loc op args source target env1 env2 opt f result final run notTypeError safe environments states extracted weightIH
    | some pair =>
      obtain ⟨bindings, cb⟩ := pair
      exact evaluate_extracted_from_weight loc cb (.op op args) bindings source target env1 env2 opt f result final
        run extracted notTypeError safe environments states weightIH clockIH
  | letCall rets ticks destination args body =>
    exact LetCallSimulation.evaluate_letcall_from_induction loc rets ticks destination args body source final target env1 env2 opt f result
      run notTypeError safe environments states weightIH clockIH
  | «return» args =>
    exact evaluate_return_from_weight loc args source target env1 env2 opt f result final run notTypeError safe environments states weightIH

/-- Flapjack infrastructure: the list simulation step from the common
smaller-weight and smaller-clock induction hypotheses. -/
theorem general_from_induction {C F : Type} (loc : Nat) (xs : List Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate xs env1 source = (result, final)) (notTypeError : result ≠ .err (.abort .typeError))
    (safe : ∀ e ∈ xs, noMutcons e) (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (optLength : opt = true → xs.length = 1)
    (weightIH : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight xs))
    (clockIH : SmallerClockIH (C := C) (F := F) source.clock) :
    GeneralPost xs source target env1 env2 opt f loc result final := by
  cases xs with
  | nil =>
    simp [BviSem.evaluate] at run
    obtain ⟨rfl, rfl⟩ := run.symm
    constructor
    · refine ⟨target, f, .val [], ?_, ?_, states, ?_, onlyFresh_refl f target.refs,
        holesUnchanged_refl f target.refs ∅, holesStill_refl f target.refs⟩
      · simp [BviSem.evaluate]
      · simp [SemanticPrimitivesProps.resultRel]
      · intro key value found; exact found
    · intro e impossible
      simp at impossible
  | cons first rest =>
    cases rest with
    | nil =>
      have post := singleton_from_induction loc first source target env1 env2 opt f result final run notTypeError
        (safe first (by simp)) environments states weightIH clockIH
      refine ⟨post.1, ?_⟩
      intro e equal
      have eq : first = e := by simpa using equal
      subst e
      exact post
    | cons second rest =>
      exact evaluate_cons_cons_from_weight first second rest source target env1 env2 opt f loc result final run safe
        environments states optLength notTypeError weightIH

/-- Flapjack infrastructure: the expression-list simulation obtained by
strong induction on the source clock and then on expression weight. -/
theorem evaluate_general {C F : Type} (loc : Nat) (xs : List Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate xs env1 source = (result, final)) (notTypeError : result ≠ .err (.abort .typeError))
    (safe : ∀ e ∈ xs, noMutcons e) (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (optLength : opt = true → xs.length = 1) : GeneralPost xs source target env1 env2 opt f loc result final := by
  have all : ∀ clock weight, ∀ (xs : List Bvi.Exp) (source : BviState (Nat × C) F) (target : BviState C F)
      (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat) (loc : Nat)
      (result : BviResult) (final : BviState (Nat × C) F),
      source.clock ≤ clock → expsWeight xs ≤ weight → evaluate xs env1 source = (result, final) →
      (∀ e ∈ xs, noMutcons e) → envRel opt f env1 env2 → stateRel f source target →
      (opt = true → xs.length = 1) → result ≠ .err (.abort .typeError) →
      GeneralPost xs source target env1 env2 opt f loc result final := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock clockIH =>
      intro weight
      induction weight using Nat.strong_induction_on with
      | h weight weightIH =>
        intro xs source target env1 env2 opt f loc result final clockBound weightBound run safe env states optLength noError
        have smallerClock : SmallerClockIH (C := C) (F := F) source.clock := by
          intro e s t a b o g l r last lt eval safeE envE statesE noErrorE
          have smaller : s.clock < clock := by omega
          exact (clockIH s.clock smaller (expsWeight [e]) [e] s t a b o g l r last (Nat.le_refl _) (Nat.le_refl _)
            eval (by simpa using safeE) envE statesE (by simp) noErrorE).2 e rfl
        have smallerWeight : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight xs) := by
          intro ys s t a b o g l r last bound smaller eval safeY envY statesY lengthY noErrorY
          by_cases earlier : s.clock < clock
          · exact clockIH s.clock earlier (expsWeight ys) ys s t a b o g l r last (Nat.le_refl _) (Nat.le_refl _)
              eval safeY envY statesY lengthY noErrorY
          · have lessWeight : expsWeight ys < weight := by omega
            exact weightIH (expsWeight ys) lessWeight ys s t a b o g l r last (by omega) (Nat.le_refl _)
              eval safeY envY statesY lengthY noErrorY
        exact general_from_induction loc xs source target env1 env2 opt f result final run noError safe env states
          optLength smallerWeight smallerClock
  exact all source.clock (expsWeight xs) xs source target env1 env2 opt f loc result final (Nat.le_refl _)
    (Nat.le_refl _) run safe environments states optLength notTypeError

/-- Flapjack infrastructure: the assembled TMC evaluation simulation with
explicit wrapper and worker conclusions. This stronger statement omits the
original theorem's unused measure premise: `expsWeight` is an internal
termination measure, not HOL's generated `list_size exp_size`. The declaration
remains untagged until the full HOL statement and carriers are reviewed. -/
theorem evaluate_rewrite_tmc_assembled {C F : Type} (xs : List Bvi.Exp)
    (source : BviState (Nat × C) F) (env1 : List Value) (result : BviResult)
    (final : BviState (Nat × C) F) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (target : BviState C F) (env2 : List Value) (loc : Nat)
    (run : evaluate xs env1 source = (result, final))
    (environments : envRel opt f env1 env2) (safe : ∀ x ∈ xs, noMutcons x)
    (states : stateRel f source target) (optLength : opt = true → xs.length = 1)
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
      evaluate xs env2 target = (nextResult, next) ∧
      resultRel (List.Forall₂ (valueRel nextMap)) (eorRel nextMap) result nextResult ∧
      stateRel nextMap final next ∧ finiteSubmap f nextMap ∧
      onlyFresh f nextMap target.refs ∧ holesUnchangedExcept f target.refs next.refs ∅ ∧
      holesStillNotFinalised f target.refs next.refs ∧
      (∀ locOpt, optimisedCode loc locOpt source.code target.code →
        (∀ wrap, xs.length = 1 ∧ rewriteWrapperSource loc locOpt env1.length
            (@holHd Bvi.Exp ⟨.var 0⟩ xs) = some wrap →
          ∃ (wrapState : BviState C F) (wrapMap : HolFiniteMapExact Nat Nat) (wrapResult : BviResult),
            evaluate [wrap] env2 target = (wrapResult, wrapState) ∧
            resultRel (List.Forall₂ (valueRel wrapMap)) (eorRel wrapMap) result wrapResult ∧
            stateRel wrapMap final wrapState ∧ finiteSubmap f wrapMap ∧
            onlyFresh f wrapMap target.refs ∧ holesUnchangedExcept f target.refs wrapState.refs ∅ ∧
            holesStillNotFinalised f target.refs wrapState.refs) ∧
        (opt = true → ∀ i j holePtr work,
          i = env1.length ∧ j = env1.length + 1 ∧
          (∃ c, holeHasVal f env1 env2 target.refs c) ∧ holeNotFinalised target.refs holePtr ∧
          rewriteWorkerSource loc locOpt i j env1.length (@holHd Bvi.Exp ⟨.var 0⟩ xs) = work ∧
          holEl i env2 = .refPtr false holePtr →
          ∃ (workResult : BviResult) (workMap : HolFiniteMapExact Nat Nat) (workState : BviState C F),
            evaluate [work] env2 target = (workResult, workState) ∧
            optResRel workMap result workResult ∧ stateRel workMap final workState ∧
            finiteSubmap f workMap ∧ onlyFresh f workMap target.refs ∧
            holesUnchangedExcept f target.refs workState.refs {holePtr} ∧
            holesStillNotFinalised f target.refs workState.refs ∧
            ∀ resValue, result = .val [resValue] →
              ∃ resValue', mutableBlockRel workMap target.refs (workState.refs.eraseEq holePtr) resValue resValue' ∧
                holeHasVal f env1 env2 workState.refs resValue')) := by
  have post := evaluate_general loc xs source target env1 env2 opt f result final run notTypeError safe environments states optLength
  obtain ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still⟩ := post.1
  refine ⟨next, g, targetResult, targetRun, related, nextStates, extension, fresh, unchanged, still, ?_⟩
  intro locOpt code
  constructor
  · intro wrap ⟨length, rewrite⟩
    cases xs with
    | nil => simp at length
    | cons e rest =>
      cases rest with
      | nil =>
        simp only [holHd] at rewrite
        exact ((post.2 e rfl).2 locOpt code).1 wrap rewrite
      | cons first tail => simp at length
  · intro optTrue i j ptr work ⟨eqi, eqj, ⟨c, hole⟩, notFinal, rewrite, pointer⟩
    subst i
    subst j
    have length := optLength optTrue
    cases xs with
    | nil => simp at length
    | cons e rest =>
      cases rest with
      | nil =>
        simp only [holHd] at rewrite
        have worker := ((post.2 e rfl).2 locOpt code).2 optTrue ptr c hole notFinal pointer
        simpa only [rewrite, IfWorker.WorkerCore] using worker
      | cons first tail => simp at length

end Flapjack.Compiler.Backend.BviTmc.Induction
