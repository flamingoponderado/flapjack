module

public import Flapjack.Pancake.Proofs.PanGlobals
public import Flapjack.Test.Fixtures.PanGlobals

-- Checks below run compiled code from these modules.
public meta import Flapjack.Test.Fixtures.PanGlobals
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Flapjack.Test.PanGlobalsEvaluateTwoParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Test.Fixtures.PanGlobals

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
