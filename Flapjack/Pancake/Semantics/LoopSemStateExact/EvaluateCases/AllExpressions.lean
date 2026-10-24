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

set_option tactic.fun_induction.unfolding false in
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
  fun_induction holLoopExpToExecutable expression with
  | case1 value => exact loopMachineEvalHook_const_prodRel hrel value
  | case2 name => exact loopMachineEvalHook_var_prodRel hrel name
  | case3 address => exact loopMachineEvalHook_lookup_prodRel hrel address
  | case4 address ih => exact loopMachineEvalHook_load_prodRel_of_ih hrel address ih
  | case5 operator args ih => exact loopMachineEvalHook_op_prodRel hrel operator args ih
  | case6 operator left right ihLeft ihRight =>
      exact loopMachineEvalHook_shift_prodRel hrel operator left right ihLeft ihRight
  | case7 => exact loopMachineEvalHook_baseAddr_prodRel hrel
  | case8 => exact loopMachineEvalHook_topAddr_prodRel hrel

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack
