module

public import Flapjack.Pancake.Semantics.PanSem.DecExact

@[expose] public section

/-!
# Exact HOL panSem `Assign` and `Primitive` clause steps

Direct source-shaped counterparts of the `Assign` and `Primitive` cases of
`panSem$evaluate_def` (`cakeml/pancake/semantics/panSemScript.sml`):

```
evaluate (Assign vk v src,s) =
  case eval s src of
   | SOME value =>
      if is_valid_value s vk v value then (NONE, set_kvar vk v value s)
      else (SOME Error, s)
   | NONE => (SOME Error, s)

evaluate (Primitive v pop es,s) =
  case OPT_MMAP (eval s) es of
   | SOME vs =>
     (case pan_primop pop vs of
       | SOME value =>
          if is_valid_value s Local v value then (NONE, set_var v value s)
          else (SOME Error, s)
       | NONE => (SOME Error, s))
   | _ => (SOME Error, s)
```

The clauses are stated over the exact MlString-keyed `PanSemStateExact` carrier
and reuse the exact ports `isValidValueHOLExact` (`is_valid_value_def`),
`setKvarHOLExact` (`set_kvar_def`), `setVarHOLExact` (`set_var_def`) and
`panPrimopHOLExact` (`pan_primop_def`).  The recursive expression evaluation is
left as a callback because the exact `eval` is not ported yet, so these
definitions are partial-evaluator infrastructure and carry **no** `@[hol]`
`evaluate` tag.

The direct original-HOL rows are in
`scripts/hol-probes/pan_sem_e2e_probe.out`
(`assign_local_ok`, `assign_global_ok`, `assign_shape_mismatch`,
`assign_expr_error`, `primitive_success`, `primitive_shape_mismatch`,
`primitive_wrong_args`, `primitive_arg_error`); the Lean parity fixtures live in
`Flapjack/Test/PanSemAssignPrimitiveExactParity.lean`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ExpHOL)

/-- HOL `panSem$evaluate` `Assign` case, over the exact MlString-keyed state. -/
def assignStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpression state source with
  | some value =>
      if isValidValueHOLExact state kind name value then
        (none, setKvarHOLExact kind name value state)
      else (some .error, state)
  | none => (some .error, state)

/-- HOL `panSem$evaluate` `Primitive` case, over the exact MlString-keyed state. -/
def primitiveStepHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) (operator : PrimOp)
    (arguments : List (ExpHOL width))
    (evalExpressions : PanSemStateExact width σ → List (ExpHOL width) →
      Option (List (ValueHOL width))) :
    Option (PanSemResultExact width) × PanSemStateExact width σ :=
  match evalExpressions state arguments with
  | some values =>
      match panPrimopHOLExact (width := width) operator values with
      | some value =>
          if isValidValueHOLExact state .local name value then
            (none, setVarHOLExact name value state)
          else (some .error, state)
      | none => (some .error, state)
  | none => (some .error, state)

end Flapjack
