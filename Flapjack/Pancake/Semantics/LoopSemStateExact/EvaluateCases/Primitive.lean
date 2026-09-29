import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Production/exact Loop Primitive case

This case compares the exact HOL-shaped `LoopSemStateFiniteExact.evaluate`
Primitive equation (`cakeml/pancake/semantics/loopSemScript.sml:285-294`) with
the production `evaluateLoop` Primitive branch (`Flapjack/Pancake/Semantics/LoopSem.lean`,
`evaluateLoop`). Both read arguments, apply a primitive, check arity, then
update or return Error. Production uses arbitrary `hooks.primitive`, so this
cross-carrier bridge requires the hook to refine exact `loopPrimop`. Without
that condition the unconditional claim is false. This is Flapjack-specific
infrastructure rather than a standalone HOL theorem; the executed-path hook
refinement remains open work, and these declarations are intentionally
untagged.
-/

namespace Flapjack
namespace LoopSemStateFiniteExact.EvaluateCases

/-- Primitive has only successful fall-through and Error result shapes. -/
def primitiveResultRel {width : Nat} [NeZero width]
    (exact : Option (LoopResultExact width))
    (production : Option (LoopMachineResult (BitVec width))) : Prop :=
  match exact, production with
  | none, none => True
  | some .error, some .error => True
  | _, _ => False

private theorem getVars_eq_loopMachineGetVars {W F : Type}
    (names : List Nat) (machine : LoopMachineState W F) :
    Flapjack.getVars names machine =
      loopMachineGetVars machine.locals names := by
  induction names generalizing machine with
  | nil => rfl
  | cons name names ih =>
      cases hlocal : machine.locals name with
      | none => simp [Flapjack.getVars, loopMachineGetVars, hlocal]
      | some value =>
          cases htail : loopMachineGetVars machine.locals names <;>
            simp [Flapjack.getVars, loopMachineGetVars, hlocal, ih, htail]

/-- The executable `loopPrimopHOL` adapter satisfies exact `loop_primop_def`
over every HOL-shaped `WordLocW` input. Both Lean definitions implement the
HOL AddCarry equation: exactly three word cells, `wordAddCarryHOL`, then low
word and carry word; malformed arities, non-word cells, and other operators
return `none`. This closes the adapter premise for a hook whose `primitive`
field is `loopPrimopHOL`; it does not establish that a caller installs it. -/
theorem loopPrimopHOL_refines_exact {width : Nat} [NeZero width]
    (operator : PrimOp) (values : List (WordLocW width)) :
    Flapjack.loopPrimopHOL operator (values.map loopValueOfWordLocW) =
      (LoopSemStateFiniteExact.loopPrimop operator values).map
        (List.map loopValueOfWordLocW) := by
  cases operator with
  | addCarry =>
      cases values with
      | nil => simp [Flapjack.loopPrimopHOL, LoopSemStateFiniteExact.loopPrimop]
      | cons first rest =>
          cases rest with
          | nil => simp [Flapjack.loopPrimopHOL, LoopSemStateFiniteExact.loopPrimop,
              Flapjack.loopValueOfWordLocW]
          | cons second rest =>
              cases rest with
              | nil => simp [Flapjack.loopPrimopHOL, LoopSemStateFiniteExact.loopPrimop,
                  Flapjack.loopValueOfWordLocW]
              | cons third rest =>
                  cases rest with
                  | nil =>
                      cases first <;> cases second <;> cases third <;>
                        simp [Flapjack.loopPrimopHOL,
                          LoopSemStateFiniteExact.loopPrimop,
                          Flapjack.loopValueOfWordLocW]
                  | cons _ _ =>
                      simp [Flapjack.loopPrimopHOL,
                        LoopSemStateFiniteExact.loopPrimop,
                        Flapjack.loopValueOfWordLocW]

/-- Relate one Primitive step when the production hook refines exact
`loopPrimop` on every exact input list. Argument values are first related using
the pre-state `prodRel`; successful outputs use `setVars_prodRel`. This does
not prove that the executed compiler's hook satisfies the refinement premise. -/
theorem evaluatePrimitive_prodRel {width : Nat} [NeZero width] {F : Type}
    {state : LoopSemStateFiniteExact width F}
    {machine : LoopMachineState (BitVec width) F}
    (hooks : LoopEvaluateHooks (BitVec width) F)
    (hrel : state.prodRel machine) (destinations : List Nat)
    (operator : PrimOp) (arguments : List Nat)
    (hPrimitive : ∀ values : List (WordLocW width),
      hooks.primitive operator (values.map loopValueOfWordLocW) =
        (LoopSemStateFiniteExact.loopPrimop operator values).map
          (List.map loopValueOfWordLocW)) :
    let exactStep :=
      LoopSemStateFiniteExact.evaluate (.primitive destinations operator arguments) state
    let productionStep := Flapjack.evaluateLoop (machine.clock + 1) hooks
      (.primitive destinations operator arguments) machine
    primitiveResultRel exactStep.1 productionStep.1 ∧
      exactStep.2.prodRel productionStep.2 := by
  have hvars := LoopSemStateFiniteExact.getVars_map_eq_of_prodRel hrel arguments
  cases hget : LoopSemStateFiniteExact.getVars arguments state with
  | none =>
      have hprod : Flapjack.getVars arguments machine = none := by
        rw [← hvars]
        simp [hget]
      have hprod' : loopMachineGetVars machine.locals arguments = none := by
        rw [← getVars_eq_loopMachineGetVars]
        exact hprod
      constructor
      · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          primitiveResultRel, hget, hprod']
      · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
          hget, hprod'] using hrel
  | some values =>
      have hprod : Flapjack.getVars arguments machine =
          some (values.map loopValueOfWordLocW) := by
        rw [← hvars]
        simp [hget]
      have hprod' : loopMachineGetVars machine.locals arguments =
          some (values.map loopValueOfWordLocW) := by
        rw [← getVars_eq_loopMachineGetVars]
        exact hprod
      cases hprim : LoopSemStateFiniteExact.loopPrimop operator values with
      | none =>
          have hprodPrim : hooks.primitive operator
              (values.map loopValueOfWordLocW) = none := by
            rw [hPrimitive values, hprim]
            rfl
          constructor
          · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
              primitiveResultRel, hget, hprod', hprim, hprodPrim]
          · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
              hget, hprod', hprim, hprodPrim] using hrel
      | some results =>
          have hprodPrim : hooks.primitive operator
              (values.map loopValueOfWordLocW) =
                some (results.map loopValueOfWordLocW) := by
            rw [hPrimitive values, hprim]
            rfl
          by_cases hlength : destinations.length = results.length
          · have hprodLength : destinations.length =
                (results.map loopValueOfWordLocW).length := by
              simpa using hlength
            have hpost :=
              LoopSemStateFiniteExact.setVars_prodRel hrel destinations results
            constructor
            · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                primitiveResultRel, hget, hprod', hprim, hprodPrim,
                hlength]
            · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                hget, hprod', hprim, hprodPrim, hlength, hprodLength,
                Flapjack.loopMachineSetVarsWordLoc,
                Flapjack.loopMachineSetVars] using hpost
          · have hprodLength : destinations.length ≠
                (results.map loopValueOfWordLocW).length := by
              simpa using hlength
            constructor
            · simp [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                primitiveResultRel, hget, hprod', hprim, hprodPrim,
                hlength]
            · simpa [LoopSemStateFiniteExact.evaluate, Flapjack.evaluateLoop,
                hget, hprod', hprim, hprodPrim, hlength, hprodLength] using hrel

end LoopSemStateFiniteExact.EvaluateCases
end Flapjack
