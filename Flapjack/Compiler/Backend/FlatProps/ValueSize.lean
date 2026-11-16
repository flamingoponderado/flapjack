module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.GeneratedSize

@[expose] public section

/-!
# The generated flat-value size equations

Counterpart of `cakeml/compiler/backend/semantics/flatPropsScript.sml:1463-1471`
(`v_size_aux`). The HOL statement is the triple of generated size equations for
the environment, the environment list and the value list, in terms of the
generated `v1_size`-`v4_size` family. Those are the reviewed renderings
`environmentSizeHOL`, `environmentListSizeHOL`, `valuePairSizeHOL`,
`valueListSizeHOL` and `valueSizeHOL`.
-/

namespace Flapjack.Compiler.Backend.FlatSem

open Flapjack

/-- HOL `v_size_aux`: the generated size equations for an environment, a list of
environment entries, and a list of values, each written with `LENGTH`/`SUM` of
the `MAP` of the next size function. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "v_size_aux"]
theorem valueSizeAux :
    (∀ (env : Environment Value),
      environmentSizeHOL env = 1 + environmentListSizeHOL env.v) ∧
    (∀ (entries : List (AstHOL.VarN × Value)),
      environmentListSizeHOL entries = entries.length + (entries.map valuePairSizeHOL).sum) ∧
    (∀ (values : List Value),
      valueListSizeHOL values = values.length + (values.map valueSizeHOL).sum) := by
  refine ⟨?_, ?_, ?_⟩
  · intro env
    cases env
    rfl
  · intro entries
    induction entries with
    | nil => simp [environmentListSizeHOL]
    | cons entry rest ih =>
      obtain ⟨name, value⟩ := entry
      simp [environmentListSizeHOL, ih]
      omega
  · intro values
    induction values with
    | nil => simp [valueListSizeHOL]
    | cons value rest ih =>
      simp [valueListSizeHOL, ih]
      omega

end Flapjack.Compiler.Backend.FlatSem
