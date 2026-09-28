import Flapjack.Pancake.PanLang
import Flapjack.Pancake.PanLang.Exp

/-!
# Pancake local/global expression-variable parity

The expected values are direct HOL-EVAL observations from
`scripts/hol-probes/pan_lang_var_exp_probeScript.sml`, covering
`cakeml/pancake/panLangScript.sml:253-293`.
-/

namespace Flapjack.Test.PanLangVarExpParity

open Flapjack

def originalProbeSource : String :=
  "cakeml/pancake/panLangScript.sml:253-293 (var_exp/global_var_exp)"

def nested : Exp Nat :=
  .rStruct [.var .local "x",
    .var .global "g",
    .nStruct "S" [("field", .var .local "y")],
    .load .one (.var .global "addr")]

def parityGuard : Bool :=
  expLocalVars (.var .local "x" : Exp Nat) == ["x"] &&
  expGlobalVars (.var .global "g" : Exp Nat) == ["g"] &&
  expLocalVars nested == ["x", "y"] &&
  expGlobalVars nested == ["g", "addr"]

#guard originalProbeSource ==
  "cakeml/pancake/panLangScript.sml:253-293 (var_exp/global_var_exp)"
#eval parityGuard
#guard parityGuard

/-! ## Exact-carrier parity (`var_exp` over the exact `ExpHOL`) -/

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

/-- Exact `MlS` name (HOL `mlstring`) for the probe's `«x»`. -/
def xName : MlS := ofString "x"

def yName : MlS := ofString "y"

/-- The exact `ExpHOL` image of `nested`, with `MlS` names. -/
def nestedHOL : ExpHOL 8 :=
  .rstruct [.var .local xName, .var .global (ofString "g"),
    .nstruct (ofString "S") [(ofString "field", .var .local yName)],
    .load .one (.var .global (ofString "addr"))]

#guard (varExpHOL (.var .local xName : ExpHOL 8)) == [xName]
#guard varExpHOL nestedHOL == [xName, yName]

example : varExpHOL (.var .local xName : ExpHOL 8) = [xName] := by
  simp [varExpHOL]

example : varExpHOL nestedHOL = [xName, yName] := by
  simp [varExpHOL, nestedHOL]

/-! ## `global_var_exp` specified-fragment parity over the exact `ExpHOL`

HOL's `global_var_exp_def` is partial: `Load32`, `BaseAddr`, `TopAddr` and
`BytesInWord` are `ARB`, so the total `globalVarExpHOL` is untagged and extends
the specification there.  The exact thirteen specified clauses HOL states are
ported by the tagged theorem `globalVarExpHOL_spec`
(`Flapjack/Pancake/PanLang/Exp.lean`), whose HOL statement (and the ARB
primitive) is pinned by `scripts/hol-probes/pan_lang_var_exp_probe.out`.  The
oracle rows below cover the specified fragment. -/

#guard (globalVarExpHOL (.var .global (ofString "g") : ExpHOL 8)) == [ofString "g"]
#guard globalVarExpHOL nestedHOL == [ofString "g", ofString "addr"]

example : globalVarExpHOL (.var .global (ofString "g") : ExpHOL 8) = [ofString "g"] := by
  simp [globalVarExpHOL]

example : globalVarExpHOL nestedHOL = [ofString "g", ofString "addr"] := by
  simp [globalVarExpHOL, nestedHOL]

/-- The `global_var` oracle row follows from the tagged HOL specified clause
`∀v. global_var_exp (Var Global v) = [v]` (`globalVarExpHOL_spec`), so the
kernel checks it against the ported statement, not only by evaluation. -/
example : globalVarExpHOL (.var .global (ofString "g") : ExpHOL 8) = [ofString "g"] :=
  (globalVarExpHOL_spec (width := 8)).2.2.1 (ofString "g")

/-! ## Production-to-exact bridge for `var_exp`

`varExpHOL_expToHOL` proves the executable `expLocalVars` is the reviewed HOL
`var_exp` under the checked `expToHOL` name codec.  Because the probe names are
byte-ranged, decoding with `toStringOfBytes` reproduces the production result. -/

def nestedProd : Exp (BitVec 8) :=
  .rStruct [.var .local "x",
    .var .global "g",
    .nStruct "S" [("field", .var .local "y")],
    .load .one (.var .global "addr")]

#guard ((varExpHOL (expToHOL nestedProd)).map toStringOfBytes) == expLocalVars nestedProd

example : varExpHOL (expToHOL nestedProd) = (expLocalVars nestedProd).map ofString :=
  varExpHOL_expToHOL nestedProd

/-- Parser-representable names decode back to the production compiler's exact
local-variable list through the domain-qualified tagged-HOL bridge. -/
example : (varExpHOL (expToHOL nestedProd)).map toStringOfBytes =
    expLocalVars nestedProd := by
  apply varExpHOL_expToHOL_decode
  intro name hname
  have hvars : expLocalVars nestedProd = ["x", "y"] := by
    simp [nestedProd, expLocalVars, expLocalVars.expLocalVarsList,
      expLocalVars.expLocalVarsFieldList]
  rw [hvars] at hname
  simp at hname
  rcases hname with rfl | rfl <;> decide

end Flapjack.Test.PanLangVarExpParity
