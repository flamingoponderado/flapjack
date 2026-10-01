import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Carriers
import Flapjack.Compiler.Backend.RegAlloc.Exceptions
import Flapjack.Translator.Monadic.MonadBase

/-!
# reg_alloc generated exception functions

The functions that `ml_monadBaseLib`'s `define_monad_exception_functions
``:state_exn`` ``:ra_state``` generates at `reg_allocScript.sml:106`
(`ml_monadBaseLib.sml:186-307`): `raise_C` and `handle_C` for each `state_exn`
constructor `C`. The result type is polymorphic as in HOL. The names are
recognized by `scripts/hol_sml_declarations.py` `monad_exception_declarations`.
These are proof-side ports: the executed allocator is not routed through them.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Generated `raise_Fail` (`reg_allocScript.sml:106`):
`raise_Fail e1 = λstate. (M_failure (Fail e1), state)`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "raise_Fail_def"]
def raiseFail {α : Type} (e1 : List Basis.Pure.MlString.HolChar) : M State α StateException :=
  fun state => (.failure (.Fail e1), state)

/-- Generated `raise_Subscript` (`reg_allocScript.sml:106`):
`raise_Subscript = λstate. (M_failure Subscript, state)`. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "raise_Subscript_def"]
def raiseSubscript {α : Type} : M State α StateException :=
  fun state => (.failure .Subscript, state)

/-- Generated `handle_Fail` (`reg_allocScript.sml:106`): a `Fail e1` failure of `x`
continues with `f e1` from the failing state; success and `Subscript` pass through. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "handle_Fail_def"]
def handleFail {α : Type} (x : M State α StateException)
    (f : List Basis.Pure.MlString.HolChar → M State α StateException) :
    M State α StateException :=
  fun state =>
    match x state with
    | (.success y, state) => (.success y, state)
    | (.failure (.Fail e1), state) => f e1 state
    | (.failure .Subscript, state) => (.failure .Subscript, state)

/-- Generated `handle_Subscript` (`reg_allocScript.sml:106`): a `Subscript` failure
of `x` continues with `f` from the failing state; success and `Fail` pass through. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "handle_Subscript_def"]
def handleSubscript {α : Type} (x : M State α StateException) (f : M State α StateException) :
    M State α StateException :=
  fun state =>
    match x state with
    | (.success y, state) => (.success y, state)
    | (.failure (.Fail e1), state) => (.failure (.Fail e1), state)
    | (.failure .Subscript, state) => f state

end Flapjack.RegAlloc
