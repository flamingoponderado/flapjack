module

public import Flapjack.TypeSystemHOL.Declarations

@[expose] public section

/-! Transport of constructor validity between type-name environments. -/
namespace Flapjack.TypeSysProps
open Flapjack.TypeSystemHOL Flapjack.AstHOL

/-- Constructor validity transfers when checked names remain valid. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "check_ctor_tenv_change_tenvT"]
theorem checkCtorTenvChangeTenvT (env1 : TenvAbbrev) (defs : TypeDef) (env2 : TenvAbbrev) :
    (∀ ctor ∈ (defs.map (fun entry => entry.2.2)).flatten,
      (∀ ty ∈ ctor.2, checkTypeNames env1 ty = true) →
        ∀ ty ∈ ctor.2, checkTypeNames env2 ty = true) ∧
    checkCtorTenv env1 defs → checkCtorTenv env2 defs := by
  intro ⟨change, valid⟩
  induction defs with
  | nil => trivial
  | cons entry rest ih =>
    rcases entry with ⟨tvs, name, ctors⟩
    simp only [checkCtorTenv] at valid ⊢
    refine ⟨valid.1, valid.2.1, ?_, valid.2.2.2.1, ?_⟩
    · intro ctor mem ty tymem
      have old := valid.2.2.1 ctor mem ty tymem
      refine ⟨old.1, ?_⟩
      apply change ctor ?_ ?_ ty tymem
      · simp [List.mem_flatten, mem]
      · intro x hx
        exact (valid.2.2.1 ctor mem x hx).2
    · apply ih ?_ valid.2.2.2.2
      intro ctor mem
      apply change ctor
      simp [mem]

end Flapjack.TypeSysProps
