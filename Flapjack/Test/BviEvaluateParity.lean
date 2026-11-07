import Flapjack.Compiler.Backend.Semantics.BviSem.Evaluate

/-! Original evaluator observations from bvi_sem_state_probe.out. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem (Value Ref)

example {C F : Type} (s : BviState C F) :
    evaluate [.var 0] [.number 3] s = (.val [.number 3], s) := by
  rw [evaluate]
  rfl

example {C F : Type} (s : BviState C F) :
    evaluate [.return []] [] s = (.err (.raise (.ret [])), s) := by
  rw [evaluate, evaluate]

example {C F : Type} (s : BviState C F) :
    evaluate [.tick (.var 0)] [] { s with clock := 0 } =
      (.err (.abort .timeoutError), { s with clock := 0 }) := by
  rw [evaluate]
  rfl

example {C F : Type} (s : BviState C F) :
    evaluate [.call 0 none [] (some (.var 0))] [] s = (.err (.abort .typeError), s) := by
  rw [evaluate]
  rfl

private def exampleRefs : HolFiniteMapExact Nat (Ref Value) :=
  HolFiniteMapExact.empty.updateEq (1, .thunk .evaluated (.number 7))

example {C F : Type} (s : BviState C F) :
    evaluate [.force 5 0] [.refPtr false 1] { s with refs := exampleRefs } =
      (.val [.number 7], { s with refs := exampleRefs }) := by
  rw [evaluate]
  simp [destThunk, exampleRefs, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]

/-- A return from a callee resumes the let-call continuation with its clock. -/
example {C F : Type} (s : BviState C F) :
    evaluate [.letCall 0 0 0 [] (.var 0)] [.number 7]
      { s with clock := 2, code := .ls (0, .return []) } =
      (.val [.number 7], { s with clock := 1, code := .ls (0, .return []) }) := by
  simp [evaluate, fixClock, decClock, BvlSem.findCode, sptLookup]

end Flapjack.Compiler.Backend.BviSem
