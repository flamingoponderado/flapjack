import Flapjack.Compiler.Backend.ClosCall.Free
import Flapjack.Compiler.Backend.ClosCall.InsertEach
import Flapjack.Compiler.Backend.ClosCall.Stubs

/-! Total direct-call traversal. -/
namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang

private theorem sizeOf_map_snd_le (xs : List (Nat × Exp)) :
    sizeOf (xs.map Prod.snd) ≤ sizeOf xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases x
    simp_wf
    omega

mutual
  /-- Total single-expression direct-call traversal. -/
  @[hol "cakeml/compiler/backend/clos_callScript.sml" "calls_sing_def"]
  def callsSing : Exp → State → Exp × State
    | .var t n, state => (.var t n, state)
    | .ifThenElse t x y z, state =>
        let (x, state) := callsSing x state
        let (y, state) := callsSing y state
        let (z, state) := callsSing z state
        (.ifThenElse t x y z, state)
    | .let t xs body, state =>
        let (xs, state) := callsSingList xs state
        let (body, state) := callsSing body state
        (.let t xs body, state)
    | .raise t x, state => let (x, state) := callsSing x state; (.raise t x, state)
    | .tick t x, state => let (x, state) := callsSing x state; (.tick t x, state)
    | .handle t x y, state =>
        let (x, state) := callsSing x state
        let (y, state) := callsSing y state
        (.handle t x y, state)
    | .call t ticks dest xs, state =>
        let (xs, state) := callsSingList xs state
        (.call t ticks dest xs, state)
    | .op t op xs, state =>
        let (xs, state) := callsSingList xs state
        (.op t op xs, state)
    | .app t loc x xs, state =>
        let (xs, state) := callsSingList xs state
        let (x', state) := callsSing x state
        match loc with
        | some loc =>
            if (sptLookup loc state.1).isSome then
              if ClosLang.pure x then (.call t xs.length (loc + 1) xs, state)
              else (.let (BackendCommon.mkCons t 0) (xs ++ [x'])
                (.call (BackendCommon.mkCons t 1) xs.length (loc + 1)
                  (variablesSource .none 2 xs.length)), state)
            else (.app t (some loc) x' xs, state)
        | none => (.app t none x' xs, state)
    | .fn name loc ws arity body, state =>
        let n := loc.getD 0
        let newState := insertEachSource n 1 state
        let (body', newState) := callsSing body newState
        let newState := (newState.1, (n + 1, arity, body') :: newState.2)
        if closed (.fn name loc ws arity body') then
          (.fn name loc ws arity (.call .none 0 (n + 1) (variablesSource .none 1 arity)), newState)
        else
          let (body', state) := callsSing body state
          (.fn name loc ws arity body', state)
    | .letrec names loc ws fns body, state =>
        let n := loc.getD 0
        let newState := insertEachSource n fns.length state
        let (bodies, newState) := callsSingList (fns.map Prod.snd) newState
        if fns.length == bodies.length && (fns.zip bodies).all (fun (fn, code) =>
            closed (.fn (Flapjack.Basis.Pure.MlString.ofString "") none none fn.1 code)) then
          let newState := codeListSource n ((fns.map Prod.fst).zip bodies) newState
          let (body, state) := callsSing body newState
          (.letrec names loc ws (callsListSource .none 1 n fns) body, state)
        else
          let (bodies, state) := callsSingList (fns.map Prod.snd) state
          let (body, state) := callsSing body state
          (.letrec names loc ws ((fns.map Prod.fst).zip bodies) body, state)
  termination_by e _ => sizeOf e
  decreasing_by
    all_goals simp_wf
    all_goals try omega
    all_goals have bound := sizeOf_map_snd_le fns
    all_goals omega

  /-- Traverse a list while threading the direct-call state. -/
  @[hol "cakeml/compiler/backend/clos_callScript.sml" "calls_sing_def"]
  def callsSingList : List Exp → State → List Exp × State
    | [], state => ([], state)
    | x :: xs, state =>
        let (x, state) := callsSing x state
        let (xs, state) := callsSingList xs state
        (x :: xs, state)
  termination_by es _ => sizeOf es
  decreasing_by all_goals simp_wf <;> omega
end

/-- Traversal preserves the number of expressions, including recursive groups.
This supports the comparison between HOL's EVERY2 check and the executed zip. -/
theorem callsSingList_length (es : List Exp) (state : State) :
    (callsSingList es state).1.length = es.length := by
  induction es generalizing state with
  | nil => simp [callsSingList]
  | cons e es ih =>
    simp only [callsSingList]
    cases callsSing e state with
    | mk out next =>
      cases run : callsSingList es next with
      | mk outs final =>
        have length := ih next
        rw [run] at length
        simp only [List.length_cons] at length ⊢
        omega

end Flapjack.Compiler.Backend.ClosCall
