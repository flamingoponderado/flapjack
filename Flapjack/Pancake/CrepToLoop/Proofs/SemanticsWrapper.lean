import Flapjack.Pancake.CrepToLoop.StateRel

/-!
# crep_to_loop `semantics_run_res` over the exact carrier

`cakeml/pancake/proofs/crep_to_loopProofScript.sml:4127-4130` declares a fresh,
polymorphic `semantics_run_res` datatype

```
semantics_run_res = RunError | CompleteResult 'a | Incomplete
```

used by the pass-result wrapper `semantics_wrapper_def` (line 4132) and the
`state_rel_imp_semantics` wrapper.  Its text is identical to
`panPropsScript.sml:1818`'s same-named datatype, but every HOL `Datatype`
command introduces its own type constant, so the two are *distinct* types.  The
`panProps` declaration is ported separately as `SemanticsRunResHOL`
(`Flapjack/Pancake/Semantics/PanProps.lean`); this module ports the
`crep_to_loop` one as the distinct carrier `CrepToLoopSemanticsRunRes`.

Constructor order, arity, and the arbitrary result payload type match HOL
exactly, so no carrier qualifier is required.  Direct Lean constructor
observations are included below.
-/

namespace Flapjack

/-- Exact port of the `crep_to_loopProofScript.sml:4127` datatype
    `semantics_run_res = RunError | CompleteResult 'a | Incomplete`.

    This is a *separate* type constant from the structurally identical
    `panPropsScript.sml:1818` `semantics_run_res` (ported as
    `SemanticsRunResHOL`): matching constructor text does not make them the same
    HOL type.  Constructor names are Lean-qualified by this type only; the
    payload arity and order match HOL. -/
@[hol "cakeml/pancake/proofs/crep_to_loopProofScript.sml" "semantics_run_res"]
inductive CrepToLoopSemanticsRunRes (α : Type u) where
  | RunError
  | CompleteResult (result : α)
  | Incomplete
  deriving DecidableEq, Repr

/-! Direct Lean constructor observations: the three constructors have HOL's
    nullary / one-payload / nullary arities, and the payload type is arbitrary. -/
example : CrepToLoopSemanticsRunRes Nat := .RunError
example (result : Nat) : CrepToLoopSemanticsRunRes Nat := .CompleteResult result
example : CrepToLoopSemanticsRunRes Nat := .Incomplete

end Flapjack
