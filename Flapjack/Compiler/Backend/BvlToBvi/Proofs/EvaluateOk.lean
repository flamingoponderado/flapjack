import Flapjack.Compiler.Backend.BvlToBvi.Proofs.ApplyAllOk
import Flapjack.Compiler.Backend.Semantics.BvlProps.ApplyError
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL

/-! Cases of BVL evaluation well-formedness. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value Ref State evaluate)
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

namespace EvaluateOkCarrier
/-- Canonical BVL reference-map state roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end EvaluateOkCarrier

/-- Flapjack's factorization of the source result-value case analysis. -/
def evalResultOk (refs : HolFiniteMapExact Nat (Ref Value)) : Result (List Value) Value → Prop
  | .val values => bvOkList refs values
  | .err (.raise value) => bvOk refs value
  | .err (.abort _) => True

/-- Flapjack's induction-hypothesis form of the source evaluator invariant.
This quantifies over every input clock; the local case lemmas using it remain
untagged until they are assembled with the source's clock-and-size induction. -/
def evalOk {C F : Type} (expressions : List Bvl.Exp) : Prop :=
  ∀ (env : List Value) (s t : State C F) (result : Result (List Value) Value),
    evaluate expressions env s = (result, t) → stateOk s → bvOkList s.refs env →
    stateOk t ∧ evalResultOk t.refs result ∧ bvOkList t.refs env

/-- Flapjack's clock-bounded induction hypothesis for dynamically selected
function bodies. -/
def evalOkBelow {C F : Type} (clock : Nat) : Prop :=
  ∀ (expressions : List Bvl.Exp) (env : List Value) (s t : State C F)
    (result : Result (List Value) Value), s.clock < clock →
    evaluate expressions env s = (result, t) → stateOk s → bvOkList s.refs env →
    stateOk t ∧ evalResultOk t.refs result ∧ bvOkList t.refs env

/-- Empty-expression-list case of the BVL evaluator invariant. -/
theorem evaluateOk_nil {C F : Type} : @evalOk C F [] := by
  intro env s t result run ok envOk
  simp [evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨ok, by simp [evalResultOk, bvOkList], envOk⟩

/-- Variable case of the BVL evaluator invariant. -/
theorem evaluateOk_var {C F : Type} (index : Nat) : @evalOk C F [.var index] := by
  intro env s t result run ok envOk
  cases lookup : env[index]? with
  | none =>
    simp [evaluate, lookup] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨ok, trivial, envOk⟩
  | some value =>
    simp [evaluate, lookup] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨ok, by
      simp only [evalResultOk, bvOkList, and_true]
      exact (bvOkList_iff _ _).1 envOk value (List.mem_of_getElem? lookup), envOk⟩

/-- Tick case of the BVL evaluator invariant, using the body induction
hypothesis with the source's decremented clock. -/
theorem evaluateOk_tick {C F : Type} (body : Bvl.Exp) (ih : @evalOk C F [body]) :
    @evalOk C F [.tick body] := by
  intro env s t result run ok envOk
  by_cases zero : s.clock = 0
  · simp [evaluate, zero] at run
    rcases run with ⟨rfl, rfl⟩
    exact ⟨ok, trivial, envOk⟩
  · simp only [evaluate, zero, if_false] at run
    exact ih env (BvlSem.decClock 1 s) t result run
      ((stateOk_decClock 1 s).2 ok) envOk

/-- Primitive-operation case of the BVL evaluator invariant. -/
theorem evaluateOk_op {C F : Type} (op : ClosLang.Op) (args : List Bvl.Exp)
    (ih : @evalOk C F args) : @evalOk C F [.op op args] := by
  intro env s t result run ok envOk
  rw [evaluate, BvlSem.fixClock_evaluate] at run
  cases argsRun : evaluate args env s with
  | mk argsResult mid =>
    have prior := ih env s mid argsResult argsRun ok envOk
    rw [argsRun] at run
    cases argsResult with
    | err error =>
      simp only at run
      cases run
      exact prior
    | val values =>
      have valuesOk : bvOkList mid.refs values := prior.2.1
      cases appRun : BvlSem.doApp op values.reverse mid with
      | err error =>
        simp only [appRun, Prod.mk.injEq] at run
        rcases run with ⟨rfl, rfl⟩
        have shape := BvlProps.doAppError op values.reverse mid error appRun
        rcases shape with typeError | ⟨_, _, _, ffiError⟩
        · subst error
          exact ⟨prior.1, trivial, prior.2.2⟩
        · subst error
          exact ⟨prior.1, trivial, prior.2.2⟩
      | val pair =>
        obtain ⟨value, last⟩ := pair
        simp only [appRun, Prod.mk.injEq] at run
        rcases run with ⟨rfl, rfl⟩
        have reverseOk : bvOkList mid.refs values.reverse := by
          apply (bvOkList_iff _ _).2
          intro value member
          exact (bvOkList_iff _ _).1 valuesOk value (List.mem_reverse.mp member)
        have appOk := doApp_ok op values.reverse env mid last value prior.1 reverseOk appRun
        exact ⟨appOk.1, by simpa [evalResultOk, bvOkList] using appOk.2.1,
          appOk.2.2 prior.2.2⟩

/-- Let case of the BVL evaluator invariant. -/
theorem evaluateOk_let {C F : Type} (bindings : List Bvl.Exp) (body : Bvl.Exp)
    (bindingsIH : @evalOk C F bindings) (bodyIH : @evalOk C F [body]) :
    @evalOk C F [.let bindings body] := by
  intro env s t result run ok envOk
  rw [evaluate, BvlSem.fixClock_evaluate] at run
  cases bindingRun : evaluate bindings env s with
  | mk bindingResult mid =>
    have prior := bindingsIH env s mid bindingResult bindingRun ok envOk
    rw [bindingRun] at run
    cases bindingResult with
    | err error =>
      simp only at run
      cases run
      exact prior
    | val values =>
      have extended : bvOkList mid.refs (values ++ env) := by
        apply (bvOkList_iff _ _).2
        intro value member
        rcases List.mem_append.mp member with left | right
        · exact (bvOkList_iff _ _).1 prior.2.1 value left
        · exact (bvOkList_iff _ _).1 prior.2.2 value right
      have bodyOk := bodyIH (values ++ env) mid t result run prior.1 extended
      refine ⟨bodyOk.1, bodyOk.2.1, (bvOkList_iff _ _).2 ?_⟩
      intro value member
      exact (bvOkList_iff _ _).1 bodyOk.2.2 value (List.mem_append_right values member)

/-- Conditional case of the BVL evaluator invariant. -/
theorem evaluateOk_if {C F : Type} (condition yes no : Bvl.Exp)
    (conditionIH : @evalOk C F [condition]) (yesIH : @evalOk C F [yes])
    (noIH : @evalOk C F [no]) : @evalOk C F [.ifThenElse condition yes no] := by
  intro env s t result run ok envOk
  rw [evaluate, BvlSem.fixClock_evaluate] at run
  cases conditionRun : evaluate [condition] env s with
  | mk conditionResult mid =>
    have prior := conditionIH env s mid conditionResult conditionRun ok envOk
    rw [conditionRun] at run
    cases conditionResult with
    | err error =>
      simp only at run
      cases run
      exact prior
    | val values =>
      dsimp only at run
      split at run
      · simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨prior.1, trivial, prior.2.2⟩
      · exact yesIH env mid t result run prior.1 prior.2.2
      · exact noIH env mid t result run prior.1 prior.2.2

/-- Raise case of the BVL evaluator invariant. -/
theorem evaluateOk_raise {C F : Type} (body : Bvl.Exp) (ih : @evalOk C F [body]) :
    @evalOk C F [.raise body] := by
  intro env s t result run ok envOk
  rw [evaluate] at run
  cases bodyRun : evaluate [body] env s with
  | mk bodyResult mid =>
    have prior := ih env s mid bodyResult bodyRun ok envOk
    rw [bodyRun] at run
    cases bodyResult with
    | err error =>
      simp only at run
      cases run
      exact prior
    | val values =>
      obtain ⟨value, rfl⟩ := BvlSem.evaluate_singleton body env s mid values bodyRun
      simp at run
      rcases run with ⟨rfl, rfl⟩
      simp only [evalResultOk, bvOkList, and_true] at prior ⊢
      exact prior

/-- Exception-handler case of the BVL evaluator invariant. -/
theorem evaluateOk_handle {C F : Type} (body handler : Bvl.Exp)
    (bodyIH : @evalOk C F [body]) (handlerIH : @evalOk C F [handler]) :
    @evalOk C F [.handle body handler] := by
  intro env s t result run ok envOk
  rw [evaluate, BvlSem.fixClock_evaluate] at run
  cases bodyRun : evaluate [body] env s with
  | mk bodyResult mid =>
    have prior := bodyIH env s mid bodyResult bodyRun ok envOk
    rw [bodyRun] at run
    cases bodyResult with
    | val values =>
      simp only at run
      cases run
      exact prior
    | err error =>
      cases error with
      | abort reason =>
        simp only at run
        cases run
        exact prior
      | raise value =>
        have extended : bvOkList mid.refs (value :: env) := by
          simp only [bvOkList]
          exact ⟨prior.2.1, prior.2.2⟩
        have handled := handlerIH (value :: env) mid t result run prior.1 extended
        have finalEnv : bvOkList t.refs env := by
          have all := handled.2.2
          simp only [bvOkList] at all
          exact all.2
        exact ⟨handled.1, handled.2.1, finalEnv⟩

/-- Non-singleton expression-list case of the BVL evaluator invariant. -/
theorem evaluateOk_cons {C F : Type} (first second : Bvl.Exp) (rest : List Bvl.Exp)
    (headIH : @evalOk C F [first]) (tailIH : @evalOk C F (second :: rest)) :
    @evalOk C F (first :: second :: rest) := by
  intro env s t result run ok envOk
  rw [evaluate, BvlSem.fixClock_evaluate] at run
  cases headRun : evaluate [first] env s with
  | mk headResult mid =>
    have prior := headIH env s mid headResult headRun ok envOk
    rw [headRun] at run
    cases headResult with
    | err error =>
      simp only at run
      cases run
      exact prior
    | val values =>
      obtain ⟨value, rfl⟩ := BvlSem.evaluate_singleton first env s mid values headRun
      have valueOk : bvOk mid.refs value := by simpa [evalResultOk, bvOkList] using prior.2.1
      cases tailRun : evaluate (second :: rest) env mid with
      | mk tailResult last =>
        have tail := tailIH env mid last tailResult tailRun prior.1 prior.2.2
        have subset := BvlProps.evaluate_refs_mono (second :: rest) env mid
        rw [tailRun] at subset
        have valueLast := bvOk_domain_mono mid.refs value last.refs valueOk subset
        rw [tailRun] at run
        cases tailResult with
        | err error =>
          simp only at run
          cases run
          exact tail
        | val values =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨tail.1, by simpa [evalResultOk, bvOkList] using ⟨valueLast, tail.2.1⟩,
            tail.2.2⟩

/-- Call case of the BVL evaluator invariant, with the source clock-bounded
induction hypothesis for the body selected from code. -/
theorem evaluateOk_call {C F : Type} (ticks : Nat) (dest : Option Nat)
    (args : List Bvl.Exp) (env : List Value) (s : State C F)
    (argsIH : @evalOk C F args) (bodyIH : @evalOkBelow C F s.clock)
    (t : State C F) (result : Result (List Value) Value)
    (run : evaluate [.call ticks dest args] env s = (result, t))
    (ok : stateOk s) (envOk : bvOkList s.refs env) :
    stateOk t ∧ evalResultOk t.refs result ∧ bvOkList t.refs env := by
  have clockBound := BvlSem.evaluate_clock_le args env s
  rw [evaluate, BvlSem.fixClock_evaluate] at run
  cases argsRun : evaluate args env s with
  | mk argsResult mid =>
    have prior := argsIH env s mid argsResult argsRun ok envOk
    simp only [argsRun] at run clockBound
    cases argsResult with
    | err error =>
      simp only at run
      cases run
      exact prior
    | val values =>
      dsimp only at run
      split at run
      · simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨prior.1, trivial, prior.2.2⟩
      · rename_i selected body found
        split at run
        · simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨prior.1, trivial, prior.2.2⟩
        · have selectedOk := findCode_bvOk dest values selected mid.code body mid.refs found prior.2.1
          have called := bodyIH [body] selected (BvlSem.decClock (ticks + 1) mid) t result
            (by simp only [BvlSem.decClock]; omega) run
            ((stateOk_decClock (ticks + 1) mid).2 prior.1) selectedOk
          have subset := BvlProps.evaluate_refs_mono [body] selected (BvlSem.decClock (ticks + 1) mid)
          rw [run] at subset
          have finalEnv := bvOkList_domain_mono mid.refs env t.refs prior.2.2 subset
          exact ⟨called.1, called.2.1, finalEnv⟩

/-- Flapjack helper: successful thunk inspection in a valid source state
returns a value valid in that state's reference domain. -/
theorem destThunk_ok {C F : Type} (s : State C F) (thunk value : Value)
    (mode : AstHOL.ThunkMode) (ok : stateOk s)
    (found : BvlSem.destThunk thunk s.refs = .isThunk mode value) :
    bvOk s.refs value := by
  cases thunk with
  | refPtr flag ptr =>
    simp only [BvlSem.destThunk] at found
    split at found <;> try contradiction
    all_goals split at found <;> try contradiction
    all_goals simp_all [stateOk]
    all_goals grind
  | _ => simp [BvlSem.destThunk] at found

/-- Force case of the BVL evaluator invariant, with the source clock-bounded
induction hypothesis for the body selected from code. -/
theorem evaluateOk_force {C F : Type} (location index : Nat)
    (env : List Value) (s : State C F) (bodyIH : @evalOkBelow C F s.clock)
    (t : State C F) (result : Result (List Value) Value)
    (run : evaluate [.force location index] env s = (result, t))
    (ok : stateOk s) (envOk : bvOkList s.refs env) :
    stateOk t ∧ evalResultOk t.refs result ∧ bvOkList t.refs env := by
  rw [evaluate] at run
  repeat' first | split at run | contradiction
  all_goals simp_all [evalResultOk]
  all_goals try (rcases run with ⟨rfl, rfl⟩; simp_all [bvOkList])
  case h_3 =>
    apply destThunk_ok s _ _ _ ok
    assumption
  case h_2.isTrue => exact ok
  case h_2.isFalse =>
    rename_i _ thunk lookup _ function found _ selected body code nonzero
    have thunkOk := (bvOkList_iff _ _).1 envOk thunk (List.mem_of_getElem? lookup)
    have functionOk := destThunk_ok s thunk function _ ok found
    have argsOk : bvOkList s.refs [thunk, function] := by
      simp [bvOkList, thunkOk, functionOk]
    have selectedOk := findCode_bvOk (some location) [thunk, function] selected s.code body s.refs code argsOk
    have called := bodyIH [body] selected (BvlSem.decClock 1 s) t result
      (by simp only [BvlSem.decClock]; omega) run ((stateOk_decClock 1 s).2 ok) selectedOk
    have subset := BvlProps.evaluate_refs_mono [body] selected (BvlSem.decClock 1 s)
    rw [run] at subset
    have finalEnv := bvOkList_domain_mono s.refs env t.refs envOk subset
    exact ⟨called.1, called.2.1, finalEnv⟩

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
