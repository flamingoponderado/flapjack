module

public import Flapjack.Compiler.Backend.Semantics.ClosSem.Call
public import Flapjack.Misc.ListEl
public import Flapjack.HolArb

@[expose] public section

/-!
# Cake `closProps` closure accessors

Lean counterparts of the closure accessor definitions in
`cakeml/compiler/backend/semantics/closPropsScript.sml:1027-1126`.

HOL defines these by pattern matching on `closure` only, so the remaining `v`
constructors are unspecified (`ARB`). As with the ported `cloAddPartialArgs`,
those clauses share the opaque `holArb` value at the result carrier. HOL marks
most of them `[simp]`; the Lean definitions omit that attribute because the
`holArb` fallback clauses would make the generated equation lemmas unsuitable
as rewrite rules, and no existing proof depends on it. `clo_to_env` is not
ported here: its `GENLIST` prefix has no decided Lean rendering.
-/

namespace Flapjack.Compiler.Backend.ClosProps
open ClosSem

/-- The expression carrier is inhabited, so HOL's total `EL` has a Lean
    instance to draw on in `cloToNumParams`. -/
local instance closPropsExpInhabited : Nonempty ClosLang.Exp := ⟨.var .none 0⟩

/-- Original `clo_to_loc_def`: a closure's location, shifted by the entry index
    for a recursive closure. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "clo_to_loc_def"]
noncomputable def cloToLoc : Value → Option Nat
  | .closure loc _ _ _ _ => loc
  | .recclosure loc _ _ _ index => loc.map (fun l => 2 * index + l)
  | _ => holArb (Option Nat)

/-- Original `clo_to_partial_args_def`: the arguments supplied so far. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "clo_to_partial_args_def"]
noncomputable def cloToPartialArgs : Value → List Value
  | .closure _ supplied _ _ _ => supplied
  | .recclosure _ supplied _ _ _ => supplied
  | _ => holArb (List Value)

/-- Original `clo_to_num_params_def`: the closure's parameter count. For a
    recursive closure HOL's total `EL i fns` is the tagged `holEl`. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "clo_to_num_params_def"]
noncomputable def cloToNumParams : Value → Nat
  | .closure _ _ _ arity _ => arity
  | .recclosure _ _ _ functions index => (holEl index functions).1
  | _ => holArb Nat

/-- Original `rec_clo_ok_def`: a recursive closure's entry index is in range. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "rec_clo_ok_def"]
noncomputable def recCloOk : Value → Prop
  | .recclosure _ _ _ functions index => index < functions.length
  | .closure _ _ _ _ _ => True
  | _ => holArb Prop

/-- Original `clo_can_apply_def`: the closure can take `numArgs` more arguments
    at the given location. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "clo_can_apply_def"]
def cloCanApply (loc : Option Nat) (cl : Value) (numArgs : Nat) : Prop :=
  (cloToPartialArgs cl).length < cloToNumParams cl ∧
    recCloOk cl ∧
    (loc ≠ none →
      loc = cloToLoc cl ∧ numArgs = cloToNumParams cl ∧ cloToPartialArgs cl = [])

/-- Original `check_closures_def`: every applicable use of `cl` also applies to
    `cl'`. -/
@[hol "cakeml/compiler/backend/semantics/closPropsScript.sml" "check_closures_def"]
def checkClosures (cl cl' : Value) : Prop :=
  ∀ loc numArgs, cloCanApply loc cl numArgs → cloCanApply loc cl' numArgs

end Flapjack.Compiler.Backend.ClosProps
