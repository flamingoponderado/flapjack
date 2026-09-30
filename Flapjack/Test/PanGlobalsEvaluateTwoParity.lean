/-
Parity for the exact HOL `pan_globalsProof$evaluate_two` / `num_cases_lemma`
pure-clock slice (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2631-2657`):
the ports `evaluateTwo` and `numCasesLemma` over the reviewed finite-support
carrier.

`evaluate_two` is a conditional statement about two arbitrary clock-bounded runs
of an arbitrary `ProgHOL`, so no concrete original-HOL `EVAL` oracle row
applies, and `evaluateHOLFiniteState` is a classical noncomputable evaluator, so
`#guard` cannot compute its result.  As for the sibling
`PanGlobalsResortDeclsEvaluateParity`, this module therefore replays each HOL
statement kernel-checked with concrete clock values plus `example`s that apply
the ported theorems.  No oracle row is fabricated.
-/
import Flapjack.Pancake.Proofs.PanGlobals

namespace Flapjack.Test.PanGlobalsEvaluateTwoParity

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

abbrev state0 : PanSemStateFiniteExact 8 Unit :=
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

/-- `num_cases_lemma[local]` (`pan_globalsProofScript.sml:2654-2657`): from a
    predicate holding at every `num`, it holds at `0` and at every `SUC x`. -/
example : (∀ n : Nat, n ≤ n + 1) → (0 ≤ 0 + 1) ∧ ∀ x, Nat.succ x ≤ Nat.succ x + 1 :=
  numCasesLemma (fun n => n ≤ n + 1)

/-- `evaluate_two[local]` (`pan_globalsProofScript.sml:2631-2652`) with the same
    clock on both sides: the result and FFI history are trivially equal. -/
example (p : ProgHOL 8) (t : PanSemStateFiniteExact 8 Unit)
    (res : Option (PanSemResultExact 8)) (st : PanSemStateFiniteExact 8 Unit)
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState { t with clock := 5 } p = (res, st))
    (hnt : res ≠ some .timeOut) :
    res = res ∧ st.ffi = st.ffi :=
  evaluateTwo p t res st res st 5 5 ⟨h, h, hnt, hnt⟩

/-- `evaluate_two[local]` with two distinct clocks `5` and `7`: two
    non-`TimeOut` runs of the same program agree on result and FFI history. -/
example (p : ProgHOL 8) (t : PanSemStateFiniteExact 8 Unit)
    (res : Option (PanSemResultExact 8)) (st : PanSemStateFiniteExact 8 Unit)
    (res' : Option (PanSemResultExact 8)) (st' : PanSemStateFiniteExact 8 Unit)
    (h : PanSemStateFiniteExact.evaluateHOLFiniteState { t with clock := 5 } p = (res, st))
    (h' : PanSemStateFiniteExact.evaluateHOLFiniteState { t with clock := 7 } p = (res', st'))
    (hnt : res ≠ some .timeOut) (hnt' : res' ≠ some .timeOut) :
    res = res' ∧ st.ffi = st'.ffi :=
  evaluateTwo p t res st res' st' 5 7 ⟨h, h', hnt, hnt'⟩

def runChecks : IO Bool := do
  IO.println "PASS pan_globals evaluate_two / num_cases_lemma (exact carriers)"
  pure true

end Flapjack.Test.PanGlobalsEvaluateTwoParity