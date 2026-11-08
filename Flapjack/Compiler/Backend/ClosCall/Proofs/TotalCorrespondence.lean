import Flapjack.Compiler.Backend.ClosCall.Compile
import Flapjack.Compiler.Backend.ClosCall.Proofs.GroupClosed
import Flapjack.Compiler.Backend.ClosCall.Proofs.Total
import Flapjack.Compiler.Backend.ClosKnown.Inline.Free.Correct

/-! Connecting the bounded executable traversal to the total HOL traversal. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang

/-- Pairwise total closedness test used by the direct-call group case. This
Flapjack helper factors the paired predicate appearing inline in HOL. -/
private def totalGroupClosed (pairs : List ((Nat × Exp) × Exp)) : Bool :=
  pairs.all (fun (fn, code) =>
    closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 code))

private theorem groupClosedFold_eq (fuel : Nat) (pairs : List ((Nat × Exp) × Exp)) (initial : Bool) :
    pairs.foldlM (fun all pair => do
      if !all then pure false else
        closedFuel fuel (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none pair.1.1 pair.2))
      initial = some (initial && totalGroupClosed pairs) := by
  induction pairs generalizing initial with
  | nil => cases initial <;> rfl
  | cons pair rest ih =>
    cases initial with
    | false => simpa [totalGroupClosed] using ih false
    | true =>
      simp only [List.foldlM_cons, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        ClosKnown.closedFuel_correct, Option.bind_eq_bind, Option.bind_some, totalGroupClosed,
        List.all_cons, Bool.true_and]
      cases h : closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none pair.1.1 pair.2) with
      | false => simpa [totalGroupClosed, h, ClosKnown.closedFuel_correct] using ih false
      | true => simpa [totalGroupClosed, h, ClosKnown.closedFuel_correct] using ih true

/-- The executed group fold agrees with the total pairwise closedness test.
This Flapjack bridge is needed to compare the bounded and total traversals. -/
theorem groupClosedFuel_eq_total (fuel : Nat) (fns : List (Nat × Exp)) (bodies : List Exp) :
    groupClosedFuel fuel fns bodies = some ((fns.zip bodies).all (fun (fn, code) =>
      closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 code))) := by
  simpa [groupClosedFuel, totalGroupClosed] using groupClosedFold_eq fuel (fns.zip bodies) true

private def Refines {α : Type} (actual : Option α) (expected : α) : Prop :=
  ∀ result, actual = some result → result = expected

private theorem refines_bind {α β : Type} (actual : Option α) (expected : α)
    (next : α → Option β) (target : α → β) (h : Refines actual expected)
    (step : ∀ x, Refines (next x) (target x)) :
    Refines (actual.bind next) (target expected) := by
  intro result run
  cases value : actual with
  | none => simp [value] at run
  | some x =>
    have eq := h x value
    subst x
    exact step expected result (by simpa [value] using run)

private theorem refines_some {α : Type} (x : α) : Refines (some x) x := by
  intro result eq
  exact (Option.some.inj eq).symm

private theorem refines_bind_at {α β : Type} (actual : Option α) (expected : α)
    (next : α → Option β) (target : β) (h : Refines actual expected)
    (step : Refines (next expected) target) :
    Refines (actual.bind next) target := by
  intro result run
  cases value : actual with
  | none => simp [value] at run
  | some x =>
    have eq := h x value
    subst x
    exact step result (by simpa [value] using run)

private theorem callsFuel_refines (fuel : Nat) :
    (∀ e state, Refines (callsFuel fuel e state) (callsSing e state)) ∧
    (∀ es state, Refines (callsListFuel fuel es state) (callsSingList es state)) := by
  induction fuel with
  | zero =>
    constructor
    · intro e state result run
      simp [callsFuel] at run
    · intro es state
      cases es with
      | nil => simpa [callsListFuel, callsSingList] using refines_some ([], state)
      | cons e es => simp [callsListFuel, Refines]
  | succ fuel ih =>
    obtain ⟨ihE, ihL⟩ := ih
    constructor
    · intro e state
      cases e <;> simp only [callsFuel, callsSing]
      case var t n => exact refines_some _
      case ifThenElse t x y z =>
        refine refines_bind _ _ _ (fun p =>
          let q := callsSing y p.2
          let r := callsSing z q.2
          (Exp.ifThenElse t p.1 q.1 r.1, r.2)) (ihE x state) ?_
        intro p
        refine refines_bind _ _ _ (fun q =>
          let r := callsSing z q.2
          (Exp.ifThenElse t p.1 q.1 r.1, r.2)) (ihE y p.2) ?_
        intro q
        refine refines_bind _ _ _ (fun r => (Exp.ifThenElse t p.1 q.1 r.1, r.2)) (ihE z q.2) ?_
        intro r
        exact refines_some _
      case «let» t xs body =>
        refine refines_bind _ _ _ (fun p =>
          let q := callsSing body p.2
          (Exp.let t p.1 q.1, q.2)) (ihL xs state) ?_
        intro p
        refine refines_bind _ _ _ (fun q => (Exp.let t p.1 q.1, q.2)) (ihE body p.2) ?_
        intro q
        exact refines_some _
      case raise t x =>
        refine refines_bind _ _ _ (fun p => (Exp.raise t p.1, p.2)) (ihE x state) ?_
        intro p
        exact refines_some _
      case tick t x =>
        refine refines_bind _ _ _ (fun p => (Exp.tick t p.1, p.2)) (ihE x state) ?_
        intro p
        exact refines_some _
      case handle t x y =>
        refine refines_bind _ _ _ (fun p =>
          let q := callsSing y p.2
          (Exp.handle t p.1 q.1, q.2)) (ihE x state) ?_
        intro p
        refine refines_bind _ _ _ (fun q => (Exp.handle t p.1 q.1, q.2)) (ihE y p.2) ?_
        intro q
        exact refines_some _
      case call t ticks dest xs =>
        refine refines_bind _ _ _ (fun p => (Exp.call t ticks dest p.1, p.2)) (ihL xs state) ?_
        intro p
        exact refines_some _
      case op t op xs =>
        refine refines_bind _ _ _ (fun p => (Exp.op t op p.1, p.2)) (ihL xs state) ?_
        intro p
        exact refines_some _
      case app t loc x xs =>
        simp only [variablesSource_eq_variables]
        cases loc with
        | none =>
          simp only
          refine refines_bind _ _ _ (fun p =>
            let q := callsSing x p.2
            (Exp.app t none q.1 p.1, q.2)) (ihL xs state) ?_
          intro p
          refine refines_bind _ _ _ (fun q => (Exp.app t none q.1 p.1, q.2)) (ihE x p.2) ?_
          intro q
          exact refines_some _
        | some n =>
          simp only
          let finish (p : List Exp × State) (q : Exp × State) : Exp × State :=
            if (sptLookup n q.2.1).isSome then
              if ClosLang.pure x then (.call t p.1.length (n + 1) p.1, q.2)
              else (.let (BackendCommon.mkCons t 0) (p.1 ++ [q.1])
                (.call (BackendCommon.mkCons t 1) p.1.length (n + 1) (ClosCall.variables .none p.1.length)), q.2)
            else (.app t (some n) q.1 p.1, q.2)
          change Refines _ (finish (callsSingList xs state) (callsSing x (callsSingList xs state).2))
          refine refines_bind _ _ _ (fun p => finish p (callsSing x p.2)) (ihL xs state) ?_
          intro p
          refine refines_bind _ _ _ (fun q => finish p q) (ihE x p.2) ?_
          intro q
          unfold finish
          split
          · split <;> exact refines_some _
          · exact refines_some _
      case fn name loc ws arity body =>
        simp only [← insertEach_eq_source, variablesSource_eq_variables, ClosKnown.closedFuel_correct]
        let finish (p : Exp × State) : Exp × State :=
          if closed (.fn name loc ws arity p.1) then
            (.fn name loc ws arity (.call .none 0 (loc.getD 0 + 1) (ClosCall.variables .none arity)),
              (p.2.1, (loc.getD 0 + 1, arity, p.1) :: p.2.2))
          else
            let q := callsSing body state
            (.fn name loc ws arity q.1, q.2)
        change Refines _ (finish (callsSing body (insertEach (loc.getD 0) 1 state)))
        refine refines_bind _ _ _ finish (ihE body (insertEach (loc.getD 0) 1 state)) ?_
        intro p
        unfold finish
        cases h : closed (.fn name loc ws arity p.1) <;>
          simp only [h, Bool.false_eq_true, ↓reduceIte]
        · refine refines_bind _ _ _ (fun q => (Exp.fn name loc ws arity q.1, q.2)) (ihE body state) ?_
          intro q
          exact refines_some _
        · exact refines_some _
      case letrec names loc ws fns body =>
        simp only [← insertEach_eq_source, ← codeList_eq_source, ← callsList_eq_source]
        let p := callsSingList (fns.map Prod.snd) (insertEach (loc.getD 0) fns.length state)
        have lengths : fns.length = p.1.length := by
          dsimp [p]
          simpa using (callsSingList_length (fns.map Prod.snd)
            (insertEach (loc.getD 0) fns.length state)).symm
        change Refines _ (if fns.length == p.1.length && (fns.zip p.1).all (fun (fn, code) =>
            closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 code)) then
          let q := callsSing body (codeList (loc.getD 0) ((fns.map Prod.fst).zip p.1) p.2)
          (Exp.letrec names loc ws (callsList (loc.getD 0) fns) q.1, q.2)
        else
          let q := callsSingList (fns.map Prod.snd) state
          let r := callsSing body q.2
          (Exp.letrec names loc ws ((fns.map Prod.fst).zip q.1) r.1, r.2))
        have sameLength : (fns.length == p.1.length) = true := by simp [lengths]
        simp only [sameLength, Bool.true_and]
        refine refines_bind_at _ p _ _ (ihL (fns.map Prod.snd)
          (insertEach (loc.getD 0) fns.length state)) ?_
        change Refines ((groupClosedFuel fuel fns p.1).bind _) _
        rw [groupClosedFuel_eq_total]
        simp only [Option.bind_some]
        split
        · refine refines_bind _ _ _ (fun q =>
            (Exp.letrec names loc ws (callsList (loc.getD 0) fns) q.1, q.2))
            (ihE body (codeList (loc.getD 0) ((fns.map Prod.fst).zip p.1) p.2)) ?_
          intro q
          exact refines_some _
        · refine refines_bind _ _ _ (fun q =>
            let r := callsSing body q.2
            (Exp.letrec names loc ws ((fns.map Prod.fst).zip q.1) r.1, r.2))
            (ihL (fns.map Prod.snd) state) ?_
          intro q
          refine refines_bind _ _ _ (fun r =>
            (Exp.letrec names loc ws ((fns.map Prod.fst).zip q.1) r.1, r.2)) (ihE body q.2) ?_
          intro r
          exact refines_some _
    · intro es state
      cases es with
      | nil => simpa [callsListFuel, callsSingList] using refines_some ([], state)
      | cons x xs =>
        simp only [callsListFuel, callsSingList]
        refine refines_bind _ _ _ (fun p =>
          let q := callsSingList xs p.2
          (p.1 :: q.1, q.2)) (ihE x state) ?_
        intro p
        refine refines_bind _ _ _ (fun q => (p.1 :: q.1, q.2)) (ihL xs p.2) ?_
        intro q
        exact refines_some _

/-- Every successful bounded expression traversal equals the total traversal.
This Flapjack bridge relates the executable fuel adapter to HOL's traversal. -/
theorem callsFuel_correct (fuel : Nat) (e : Exp) (state : State) (result : Exp × State)
    (run : callsFuel fuel e state = some result) : result = callsSing e state :=
  (callsFuel_refines fuel).1 e state result run

/-- Every successful bounded list traversal equals the total traversal.
This Flapjack bridge relates the executable fuel adapter to HOL's traversal. -/
theorem callsListFuel_correct (fuel : Nat) (es : List Exp) (state : State) (result : List Exp × State)
    (run : callsListFuel fuel es state = some result) : result = callsSingList es state :=
  (callsFuel_refines fuel).2 es state result run

/-- The executable retry wrapper always returns the total HOL-shaped result.
This Flapjack bridge discharges both fuel exhaustion and output agreement. -/
theorem callsListBounded_correct (fuel : Nat) (es : List Exp) (state : State) :
    callsListBounded fuel es state = some (callsSingList es state) := by
  obtain ⟨result, run⟩ := callsListBounded_succeeds fuel es state
  have eq : result = callsSingList es state := by
    unfold callsListBounded at run
    cases first : callsListFuel fuel es state with
    | none =>
      have retry : callsListFuel (max fuel (listBudget es + 1)) es state = some result := by
        simpa [first] using run
      exact callsListFuel_correct _ es state result retry
    | some value =>
      have same : value = result := by simpa [first] using run
      subst value
      exact callsListFuel_correct fuel es state result first
  simpa [eq] using run

/-- The executable conditional pass agrees with the total traversal when
enabled and returns the unchanged input when disabled. This is a bridge from
the fuel adapter to HOL's `compile_eq`. -/
theorem compileFuel_correct (fuel : Nat) (enabled : Bool) (es : List Exp) :
    compileFuel fuel enabled es = some (if enabled then callsSingList es (.ln, []) else (es, (.ln, []))) := by
  cases enabled <;> simp [compileFuel, callsListBounded_correct]

/-- The executed incremental pass returns the total traversal's known set,
expressions and generated code. This bridges the fuel adapter to HOL's
`compile_inc_eq`; the incoming auxiliary code is discarded. -/
theorem compileIncFuel_correct (fuel : Nat) (known : NumSet)
    (program : List Exp × List (Nat × Nat × Exp)) :
    compileIncFuel? fuel known program =
      some (let result := callsSingList program.1 (known, [])
        (result.2.1, (result.1, result.2.2))) := by
  simp [compileIncFuel?, callsListBounded_correct]

/-- The bounded executable compiler agrees with the total HOL compiler. -/
theorem compileFuel_eq_compile (fuel : Nat) (enabled : Bool) (es : List Exp) :
    compileFuel fuel enabled es = some (compile enabled es) := by
  simpa [compile, calls] using compileFuel_correct fuel enabled es

/-- The bounded executable incremental pass agrees with HOL's total pass. -/
theorem compileIncFuel_eq_compileInc (fuel : Nat) (known : NumSet)
    (program : List Exp × List (Nat × Nat × Exp)) :
    compileIncFuel? fuel known program = some (compileInc known program) := by
  simpa [compileInc, calls] using compileIncFuel_correct fuel known program

end Flapjack.Compiler.Backend.ClosCall
