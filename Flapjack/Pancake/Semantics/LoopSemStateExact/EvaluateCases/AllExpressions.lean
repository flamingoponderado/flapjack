import Flapjack.Pancake.Semantics.LoopSemStateExact.EvaluateCases.OpShift

/-!
# Whole exact Loop expression hook refinement

This assembles the constructor cases for the Flapjack-specific relation between
the finite-support HOL-shaped evaluator and the candidate production
`loopMachineEvalHook`. It is an untagged cross-carrier theorem. It does not
establish that an executed compiler caller supplies this hook.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- For every faithful `HolLoopExp`, the candidate production hook on the
    executable view agrees with exact `eval` when the two input states satisfy
    `prodRel`. The recursive hypotheses are structural: `Load` receives its
    address IH, `Op` receives an IH for every operand in its argument list, and
    `Shift` receives both child IHs. No desired whole-expression hook equation
    is assumed. -/
theorem loopMachineEvalHook_holLoopExp_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) (expression : HolLoopExp width) :
    loopMachineEvalHook machine (holLoopExpToExecutable expression) =
      (LoopSemStateFiniteExact.eval state expression).map loopValueOfWordLocW := by
  let P1 := fun expression : HolLoopExp width =>
    loopMachineEvalHook machine (holLoopExpToExecutable expression) =
      (LoopSemStateFiniteExact.eval state expression).map loopValueOfWordLocW
  let P2 := fun expressions : List (HolLoopExp width) =>
    ∀ expression, expression ∈ expressions → P1 expression
  change P1 expression
  refine HolLoopExp.brecOn (motive_1 := P1) (motive_2 := P2) expression ?_ ?_
  · intro expression hbelow
    cases expression with
    | const value => exact loopMachineEvalHook_const_prodRel hrel value
    | var name => exact loopMachineEvalHook_var_prodRel hrel name
    | lookup address => exact loopMachineEvalHook_lookup_prodRel hrel address
    | load address =>
        exact loopMachineEvalHook_load_prodRel_of_ih hrel address hbelow.1
    | op operator args =>
        exact loopMachineEvalHook_op_prodRel hrel operator args hbelow.1
    | shift operator left right =>
        exact loopMachineEvalHook_shift_prodRel hrel operator left right
          hbelow.1.1 hbelow.2.1
    | baseAddr => exact loopMachineEvalHook_baseAddr_prodRel hrel
    | topAddr => exact loopMachineEvalHook_topAddr_prodRel hrel
  · intro expressions hbelow
    cases expressions with
    | nil =>
        intro expression hmem
        cases hmem
    | cons head tail =>
        intro expression hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · subst expression
          exact hbelow.1.1
        · exact hbelow.2.1 expression hmem

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack
