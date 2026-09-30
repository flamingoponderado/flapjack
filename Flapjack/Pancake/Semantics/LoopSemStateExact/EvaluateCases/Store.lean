import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-! Production/exact Loop Store infrastructure. HOL Store uses whole-state
`mem_store`; the production evaluator delegates to a store hook. These
cross-carrier refinements have no HOL theorem original and carry no HOL tag.
They do not establish a whole evaluator or label-rebasing simulation. -/
namespace Flapjack

/-- Whole-state production memory update for a word address. Its domain check
and single-cell update match exact `memStore`; no other state field changes. -/
def loopMachineMemStore {width : Nat} [NeZero width] {F : Type}
    (machine : LoopMachineState (BitVec width) F) (address : BitVec width)
    (value : WordLocW width) : Option (LoopMachineState (BitVec width) F) :=
  if machine.mdomain address then
    some { machine with memory := fun current =>
      if current = address then some (loopValueOfWordLocW value) else machine.memory current }
  else none

/-- Single-cell memory update preserves the full state relation. The memory
postcondition follows from the input relation at every unchanged address. -/
theorem LoopSemStateFiniteExact.memoryUpdate_prodRel {width : Nat} [NeZero width]
    {F : Type} {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F} (hrel : state.prodRel machine)
    (address : BitVec width) (value : WordLocW width) :
    ({ state with memory := fun current =>
      if current = address then value else state.memory current }).prodRel
    { machine with memory := fun current =>
      if current = address then some (loopValueOfWordLocW value) else machine.memory current } := by
  rcases hrel with ⟨hl, hg, hm, hmd, hsh, hc, hb, hf, hbase, htop, hcode, hcover⟩
  refine ⟨hl, hg, ?_, hmd, hsh, hc, hb, hf, hbase, htop, hcode, hcover⟩
  intro current
  by_cases heq : current = address
  · simp [heq]
  · simpa [heq] using hm current

namespace LoopSemStateFiniteExact.EvaluateCases

/-- Store has only normal completion and Error results. -/
def storeResultRel {width : Nat} [NeZero width]
    (exact : Option (LoopResultExact width))
    (production : Option (LoopMachineResult (BitVec width))) : Prop :=
  match exact, production with
  | none, none => True
  | some .error, some .error => True
  | _, _ => False

/-- Relate Store's success and all failure branches. Hook refinements are
explicit; no desired target evaluation or post-state relation is assumed.
The canonical store adapter's postrelation is derived by memoryUpdate_prodRel. -/
theorem evaluateStore_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F) (hrel : state.prodRel machine)
    (sourceExpression : HolLoopExp width) (runtimeExpression : LoopExp (BitVec width))
    (name : Nat)
    (hEval : hooks.eval machine runtimeExpression =
      (LoopSemStateFiniteExact.eval state sourceExpression).map loopValueOfWordLocW)
    (hStore : ∀ address value, hooks.store machine (.word address)
      (loopValueOfWordLocW value) = loopMachineMemStore machine address value) :
    let exactStep := evaluate (.store sourceExpression name) state
    let productionStep := evaluateLoop (machine.clock + 1) hooks
      (.store runtimeExpression name) machine
    storeResultRel exactStep.1 productionStep.1 ∧ exactStep.2.prodRel productionStep.2 := by
  have hlocals := hrel.1 name
  have hdomain := hrel.2.2.2.1
  cases heval : eval state sourceExpression with
  | none =>
      simpa [evaluate, evaluateLoop, storeResultRel, hEval, heval] using hrel
  | some address =>
      cases hlocal : sptLookup name state.locals with
      | none =>
          simpa [evaluate, evaluateLoop, storeResultRel, hEval, heval, hlocals, hlocal]
            using hrel
      | some value =>
          cases address with
          | loc label offset =>
              simpa [evaluate, evaluateLoop, storeResultRel, hEval, heval,
                hlocals, hlocal, loopValueOfWordLocW] using hrel
          | word address =>
              have hs := hStore address value
              simp only [loopValueOfWordLocW] at hs
              by_cases hd : state.mdomain address
              · have hpost := memoryUpdate_prodRel hrel address value
                simpa [evaluate, evaluateLoop, storeResultRel, hEval, heval,
                  hlocals, hlocal, loopValueOfWordLocW, hs, memStore,
                  loopMachineMemStore, hdomain, hd] using hpost
              · simpa [evaluate, evaluateLoop, storeResultRel, hEval, heval,
                  hlocals, hlocal, loopValueOfWordLocW, hs, memStore,
                  loopMachineMemStore, hdomain, hd] using hrel

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack
