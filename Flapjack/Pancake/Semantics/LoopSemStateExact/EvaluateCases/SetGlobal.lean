import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop SetGlobal case

This case compares the exact HOL-shaped `LoopSemStateFiniteExact.evaluate`
SetGlobal equation (`cakeml/pancake/semantics/loopSemScript.sml:306-310`) with
the production `evaluateLoop` SetGlobal branch
(`Flapjack/Pancake/Semantics/LoopSem.lean`, `evaluateLoop`). HOL evaluates with
its exact `eval` and updates through `set_globals`, whereas production calls an
arbitrary `hooks.eval` and an arbitrary `hooks.setGlobal`. Without a hook
refinement premise an unconditional claim is false, so the cross-carrier bridge
takes the expression-hook and setGlobal-hook agreements as explicit, separately
named premises.

The canonical candidate production `setGlobal` adapter `loopMachineSetGlobal`
and its `setGlobals_prodRel` transition lemma are supplied here, so the case
theorem can be instantiated with the concrete executed adapter (the
`hSetGlobal` premise is then a definitional rewrite) as well as with any other
adapter whose agreement is separately proved. These are Flapjack-specific
cross-carrier bridges between the exact finite-support carrier and the
production carrier; none ports a HOL declaration, so they intentionally carry
no `@[hol]` tag. Wiring to an actual non-test `evaluateLoop` caller remains
open work.
-/

namespace Flapjack

/-- Canonical candidate production adapter for the `LoopEvaluateHooks.setGlobal`
    field: overlay the addressed global cell with the location/word payload.
    This is the proposed executable counterpart of the exact
    `LoopSemStateFiniteExact.setGlobals`, matching HOL's `s.globals |+ (gv,w)`
    (`loopSemScript.sml:52-55`). Flapjack-only carrier infrastructure. -/
def loopMachineSetGlobal {width : Nat} [NeZero width] {F : Type}
    (machine : LoopMachineState (BitVec width) F) (address : BitVec 5)
    (value : WordLocW width) : LoopMachineState (BitVec width) F :=
  { machine with globals := FUPDATE machine.globals (address, loopValueOfWordLocW value) }

/-- Exact and production Loop states preserve `prodRel` when the exact
    `set_globals` update is paired with the canonical `loopMachineSetGlobal`
    update. Only the `globals` conjunct changes; the arguments of `prodRel` are
    handled by the `HolFiniteMapExact.update` `FUPDATE` lookup equation for the
    addressed key and by the pre-state relation elsewhere. This is a
    Flapjack-only cross-carrier transition lemma, not a separate HOL
    declaration or a whole-evaluator simulation theorem. -/
theorem LoopSemStateFiniteExact.setGlobals_prodRel {width : Nat} [NeZero width]
    {F : Type} {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hrel : state.prodRel machine) (address : BitVec 5) (value : WordLocW width) :
    (setGlobals address value state).prodRel
      (loopMachineSetGlobal machine address value) := by
  rcases hrel with
    ⟨hlocals, hglobals, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
      hbaseAddr, htopAddr, hcode, hcoverage⟩
  refine ⟨hlocals, ?_, hmemory, hmdomain, hshMdomain, hclock, hbe, hffi,
    hbaseAddr, htopAddr, hcode, hcoverage⟩
  intro key
  simp only [setGlobals, loopMachineSetGlobal, HolFiniteMapExact.lookup_update]
  by_cases hkey : address == key
  · simp [FUPDATE, hkey]
  · simp [FUPDATE, hkey, hglobals key]

namespace LoopSemStateFiniteExact.EvaluateCases

/-- SetGlobal has only its successful/None and Error result shapes. -/
def setGlobalResultRel {width : Nat} [NeZero width]
    (exact : Option (LoopResultExact width))
    (production : Option (LoopMachineResult (BitVec width))) : Prop :=
  match exact, production with
  | none, none => True
  | some .error, some .error => True
  | _, _ => False

/-- Relate one SetGlobal step when the production expression hook agrees with
    exact `eval` for the corresponding expression pair and the production
    setGlobal hook agrees with the canonical `loopMachineSetGlobal` adapter for
    the evaluated payload. The exact and production expression carriers are
    explicitly distinct. Eval failure preserves both states; success uses the
    `setGlobals_prodRel` bridge. This does not establish expression translation
    or hook agreement for the executed compiler on its own, nor does it claim
    arbitrary hooks satisfy the refinements. Flapjack-only bridge
    infrastructure (no `@[hol]` tag). -/
theorem evaluateSetGlobal_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (hrel : state.prodRel machine) (address : BitVec 5)
    (sourceExpression : HolLoopExp width)
    (runtimeExpression : LoopExp (BitVec width))
    (hEval : hooks.eval machine runtimeExpression =
      (LoopSemStateFiniteExact.eval state sourceExpression).map loopValueOfWordLocW)
    (hSetGlobal : ∀ value : WordLocW width,
      hooks.setGlobal machine address (loopValueOfWordLocW value) =
        loopMachineSetGlobal machine address value) :
    let exactStep :=
      LoopSemStateFiniteExact.evaluate (.setGlobal address sourceExpression) state
    let productionStep := Flapjack.evaluateLoop (machine.clock + 1) hooks
      (.setGlobal address runtimeExpression) machine
    setGlobalResultRel exactStep.1 productionStep.1 ∧
      exactStep.2.prodRel productionStep.2 := by
  cases heval : LoopSemStateFiniteExact.eval state sourceExpression with
  | none =>
      have hprod : hooks.eval machine runtimeExpression = none := by
        rw [hEval, heval]
        rfl
      constructor
      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          setGlobalResultRel, heval, hprod]
      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          heval, hprod] using hrel
  | some value =>
      have hprod : hooks.eval machine runtimeExpression =
          some (loopValueOfWordLocW value) := by
        rw [hEval, heval]
        rfl
      have hpost :=
        LoopSemStateFiniteExact.setGlobals_prodRel hrel address value
      constructor
      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          setGlobalResultRel, heval, hprod]
      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          heval, hprod, hSetGlobal value] using hpost

end LoopSemStateFiniteExact.EvaluateCases

end Flapjack
