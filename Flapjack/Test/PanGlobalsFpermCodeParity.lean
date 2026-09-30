import Flapjack.Pancake.Proofs.PanGlobals.FpermCode

/-! Direct original pan_globalsProof$fperm_code replay from
scripts/hol-probes/pan_globals_fperm_code_probe.out. -/
namespace Flapjack.Test.PanGlobalsFpermCodeParity
open Pancake.PanLang

private def f : MlS := ⟨[102]⟩
private def g : MlS := ⟨[103]⟩
private def x : MlS := ⟨[120]⟩
private def z : MlS := ⟨[122]⟩
private def code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  ((HolFiniteMapExact.empty.updateEq (f, [], .call none f [], .one)).updateEq
    (g, [], .skip, .one)).updateEq (x, [], .call none g [], .one)

-- swap_f=SOME ([],Skip,One)
example : (fpermCodeHOL f g code).lookup f = some ([], .skip, .one) := by cbv
-- swap_g=SOME ([],TailCall «g» [],One)
example : (fpermCodeHOL f g code).lookup g = some ([], .call none g [], .one) := by cbv
-- other=SOME ([],TailCall «f» [],One)
example : (fpermCodeHOL f g code).lookup x = some ([], .call none f [], .one) := by cbv
-- missing=NONE
example : (fpermCodeHOL f g code).lookup z = none := by cbv
-- equal_names=SOME ([],TailCall «f» [],One)
example : (fpermCodeHOL f f code).lookup f = some ([], .call none f [], .one) := by cbv

private def isCall (expected : MlS) :
    Option (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) → Bool
  | some ([], .call none target [], .one) => target == expected
  | _ => false

private def checks : Bool :=
  (match (fpermCodeHOL f g code).lookup f with
   | some ([], .skip, .one) => true | _ => false) &&
  isCall g ((fpermCodeHOL f g code).lookup g) &&
  isCall f ((fpermCodeHOL f g code).lookup x) &&
  ((fpermCodeHOL f g code).lookup z).isNone &&
  isCall f ((fpermCodeHOL f f code).lookup f)

#guard checks
def runChecks : IO Bool := do
  if checks then
    IO.println "PASS exact PanGlobals finite-map permutation matches five original HOL rows"
    pure true
  else
    IO.println "FAIL exact PanGlobals finite-map permutation differs from original HOL"
    pure false
end Flapjack.Test.PanGlobalsFpermCodeParity
