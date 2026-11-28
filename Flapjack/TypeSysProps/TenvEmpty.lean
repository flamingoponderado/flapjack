module

public import Flapjack.TypeSoundInvariants
public import Flapjack.NamespaceProps.Empty

@[expose] public section

/-!
# Empty type environments

Lean counterparts of the `typeSysProps` statements about the empty namespace
and the empty type environment.  `nsAll` takes `DecidableEq` arguments in Lean,
rendered here by the same local classical instance convention as the other
namespace modules; HOL imposes no equality constraints.
-/

namespace Flapjack.TypeSysProps

noncomputable local instance instDecidableEq_tenvEmpty (α : Type) : DecidableEq α :=
  Classical.typeDecidableEq α

open Flapjack.Basis.Pure.MlString Flapjack.TypeSoundInvariants Flapjack.NamespaceHOL
open Flapjack.TypeSystemHOL

/-- Original `tenv_val_ok_nsEmpty`: the empty value namespace is well formed. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_val_ok_nsEmpty"]
theorem tenvValOk_nsEmpty {M N : Type} :
    tenvValOk (nsEmpty : Namespace M N (Nat × SemanticT)) :=
  nsAll_nsEmpty _

/-- Original `tenv_ctor_ok_nsEmpty`: the empty constructor namespace is well formed. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_ctor_ok_nsEmpty"]
theorem tenvCtorOk_nsEmpty {M N Tag : Type} :
    tenvCtorOk (nsEmpty : Namespace M N (List MlString × List SemanticT × Tag)) :=
  nsAll_nsEmpty _

/-- Original `tenv_abbrev_ok_nsEmpty`: the empty abbreviation namespace is well
formed. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_abbrev_ok_nsEmpty"]
theorem tenvAbbrevOk_nsEmpty {M N : Type} :
    tenvAbbrevOk (nsEmpty : Namespace M N (List MlString × SemanticT)) :=
  nsAll_nsEmpty _

/-- Original `tenv_ok_empty`: the empty type environment is well formed. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "tenv_ok_empty"]
theorem tenvOk_empty :
    tenvOk ⟨(nsEmpty : TenvVal), (nsEmpty : TenvCtor), (nsEmpty : TenvAbbrev)⟩ := by
  exact ⟨tenvValOk_nsEmpty, tenvCtorOk_nsEmpty, tenvAbbrevOk_nsEmpty⟩

/-- Original `unchanged_tenv`: rebuilding an environment from its fields is the
environment itself. -/
@[hol "cakeml/semantics/proofs/typeSysPropsScript.sml" "unchanged_tenv"]
theorem unchanged_tenv (tenv : TypeEnv) : ⟨tenv.v, tenv.c, tenv.t⟩ = tenv := by
  cases tenv
  rfl

end Flapjack.TypeSysProps
