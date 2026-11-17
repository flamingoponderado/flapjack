module

public import Flapjack.TypeSoundInvariants

@[expose] public section

/-! Well-formed declarative type abbreviations. -/
namespace Flapjack.TypeSysProps
open Flapjack.Basis.Pure.MlString Flapjack.NamespaceHOL Flapjack.TypeSystemHOL
  Flapjack.TypeSoundInvariants

noncomputable local instance abbrevClassicalDecidableEq (α : Type) : DecidableEq α :=
  Classical.typeDecidableEq α

/-- Looking up a well-formed abbreviation yields a type whose free variables
are among its declared parameters. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_abbrev_ok_lookup"]
theorem tenvAbbrevOkLookup {M N : Type}
    (env : Namespace M N (List MlString × SemanticT)) (name : Ident M N)
    (tvs : List MlString) (t : SemanticT) :
    tenvAbbrevOk env ∧ nsLookup env name = some (tvs, t) →
      checkFreevars 0 tvs t = true := by
  rintro ⟨wellFormed, found⟩
  exact wellFormed name (tvs, t) found

end Flapjack.TypeSysProps
