import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts
import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConstsGuard

/-! Untagged, source-shaped fragment of the HOL `evaluate_def` `StoreConsts`
clause (`cakeml/compiler/backend/semantics/stackSemScript.sml:784-788`):

```
(evaluate (StoreConsts t1 t2 stub_opt,s) =
   if ~s.use_store then (SOME Error,s) else
   if ~s.use_alloc /\ IS_SOME stub_opt then (SOME Error,s) else
   if ~check_store_consts_opt t1 t2 stub_opt s.code then (SOME Error,s) else
     store_const_sem t1 t2 s)
```

This is a leaf case (no recursive `evaluate` call). It reuses the accepted
tagged helpers `checkStoreConstsOpt`
(`Flapjack/Compiler/Backend/Semantics/StackSem/StoreConstsGuard.lean`) and
`storeConstSem` (`Flapjack/Compiler/Backend/Semantics/StackSem/StoreConsts.lean`)
over the exact `StackSemStateFiniteExact` carrier.

No `@[hol]` tag is carried because this is a partial case fragment, not the
whole HOL `evaluate_def`; the total 34-constructor evaluator assembly is tracked
by bead `flapjack-y19g.18` (parent `flapjack-y19g`). -/

namespace Flapjack.StackSemStoreConsts

open Flapjack.StackSemStoreConstsGuard

/-- The HOL `evaluate (StoreConsts t1 t2 stubOpt, s)` branch: reject when
`useStore` is off; reject a `some` stub when `useAlloc` is off; reject when the
exact `checkStoreConstsOpt` stub guard fails; otherwise run the exact
`storeConstSem`. Every rejected guard returns `Error` with the original state. -/
def evaluateStoreConsts {width : Nat} [NeZero width] {C F : Type}
    (t1 t2 : Nat) (stubOpt : Option Nat) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if ¬ s.useStore then (some .error, s)
  else if ¬ s.useAlloc ∧ stubOpt.isSome then (some .error, s)
  else if ¬ checkStoreConstsOpt t1 t2 stubOpt s.code then (some .error, s)
  else storeConstSem t1 t2 s

/-- Unfolding equation for the `StoreConsts` fragment. -/
theorem evaluateStoreConsts_def {width : Nat} [NeZero width] {C F : Type}
    (t1 t2 : Nat) (stubOpt : Option Nat) (s : StackSemStateFiniteExact width C F) :
    evaluateStoreConsts t1 t2 stubOpt s =
      (if ¬ s.useStore then (some .error, s)
       else if ¬ s.useAlloc ∧ stubOpt.isSome then (some .error, s)
       else if ¬ checkStoreConstsOpt t1 t2 stubOpt s.code then (some .error, s)
       else storeConstSem t1 t2 s) := rfl

end Flapjack.StackSemStoreConsts
