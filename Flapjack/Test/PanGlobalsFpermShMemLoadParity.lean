/-
Kernel replay for the port `Flapjack.evaluateFperm_ShMemLoad`
(`cakeml/pancake/proofs/pan_globalsProofScript.sml` `evaluate_fperm`, the
`ShMemLoad` conjunct of `panSemScript.sml` `evaluate_def`).

`evaluate_fperm` is a conditional implication over an arbitrary program whose
premise is a run of the classical noncomputable `evaluateHOLFiniteState`, so no
concrete original-HOL `EVAL` oracle row applies here (the CakeML/HOL theories
are not built in this checkout) and `#guard` cannot compute either side.  As in
the sibling `PanGlobalsEvaluateTwoParity`, this module therefore replays the HOL
statement kernel-checked with concrete carriers: the `example`s apply the
ported theorem at a concrete `ShMemLoad` program and concrete finite state,
checking the code-permuted target/post-state equality.  No oracle row is
fabricated.
-/
import Flapjack.Pancake.Proofs.PanGlobals.FpermEvaluate.ShMemLoad

namespace Flapjack.Test.PanGlobalsFpermShMemLoadParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact

private abbrev emptyValues : HolFiniteMapExact MlS (ValueHOL 8) :=
  HolFiniteMapExact.empty

private abbrev emptyShapes : HolFiniteMapExact MlS ShapeHOL :=
  HolFiniteMapExact.empty

private abbrev emptyCode :
    HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 8 × ShapeHOL) :=
  HolFiniteMapExact.empty

private abbrev state0 : PanSemStateFiniteExact 8 Unit :=
  { locals := emptyValues
    globals := emptyValues
    structs := []
    code := emptyCode
    eshapes := emptyShapes
    memory := fun _ => .word 0
    memaddrs := fun _ => False
    shMemaddrs := fun _ => False
    clock := 5
    be := false
    ffi := { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
    baseAddr := 0
    topAddr := 100 }

private def f : MlS := ⟨[102]⟩
private def g : MlS := ⟨[103]⟩
private def name : MlS := ⟨[120]⟩

/-- Kernel replay of the ported `evaluate_fperm` `ShMemLoad` theorem on a
    concrete `ShMemLoad` program and concrete finite state: from any source run
    of `state0`, the code-permuted target run agrees on the whole result and on
    the code-permuted post-state (no success/read/target-run premise added). -/
example (res : Option (PanSemResultExact 8)) (post : PanSemStateFiniteExact 8 Unit)
    (h : evaluateHOLFiniteState state0
      (.shMemLoad .op8 .local name (.const (0 : BitVec 8)) : ProgHOL 8) = (res, post)) :
    evaluateHOLFiniteState { state0 with code := fpermCodeHOL f g state0.code }
      (fpermHOL f g (.shMemLoad .op8 .local name (.const (0 : BitVec 8)) : ProgHOL 8)) =
      (res, { post with code := fpermCodeHOL f g post.code }) :=
  evaluateFperm_ShMemLoad f g state0 .op8 .local name (.const (0 : BitVec 8)) res post h

def runChecks : IO Bool := do
  IO.println "PASS pan_globals evaluate_fperm ShMemLoad (exact carriers)"
  pure true

end Flapjack.Test.PanGlobalsFpermShMemLoadParity
