module

public import Flapjack.TypeSystemHOL.Declarations
public import Flapjack.TypeSysProps.Abbrev
public import Flapjack.NamespaceProps.All

@[expose] public section

/-! Transport of constructor validity between type-name environments. -/
namespace Flapjack.TypeSysProps
open Flapjack Flapjack.TypeSystemHOL Flapjack.AstHOL Flapjack.NamespaceHOL
  Flapjack.TypeSoundInvariants

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

noncomputable local instance ctorOkClassicalDecidableEq (α : Type) : DecidableEq α :=
  Classical.typeDecidableEq α

/-- Valid constructor declarations built over a well-formed abbreviation
environment produce a well-formed constructor environment. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "check_ctor_tenv_ok"]
theorem checkCtorTenvOk {M Tag : Type} (env : TenvAbbrev) (defs : TypeDef) (ids : List Tag) :
    defs.length = ids.length ∧ checkCtorTenv env defs ∧ tenvAbbrevOk env →
      tenvCtorOk (buildCtorTenv (α := M) env defs ids) := by
  induction defs generalizing ids with
  | nil =>
    intro ⟨lengths, _, _⟩
    cases ids with
    | nil =>
      simp only [buildCtorTenv, tenvCtorOk, nsAll]
      intro name entry found
      cases name <;> simp [alistToNs, nsLookup] at found
    | cons id ids => simp at lengths
  | cons d ds ih =>
    rcases d with ⟨tvs, name, ctors⟩
    cases ids with
    | nil => simp
    | cons id ids =>
      rintro ⟨lengths, valid, envOk⟩
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      simp only [checkCtorTenv] at valid
      simp only [buildCtorTenv, tenvCtorOk]
      apply nsAll_nsAppend
      constructor
      · exact ih ids ⟨lengths, valid.2.2.2.2, envOk⟩
      · apply nsAllAlistToNs
        intro entry member
        simp only [List.mem_reverse, List.mem_map] at member
        obtain ⟨⟨ctorName, args⟩, ctorMem, rfl⟩ := member
        intro t tMem
        obtain ⟨source, sourceMem, rfl⟩ := List.mem_map.mp tMem
        have checks := valid.2.2.1 (ctorName, args) ctorMem source sourceMem
        exact checkFreevarsTypeNameSubst tvs source 0 env ⟨envOk, checks.2, checks.1⟩

end Flapjack.TypeSysProps
