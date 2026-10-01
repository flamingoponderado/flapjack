import Flapjack.Compiler.Backend.RegAlloc.ExceptionFunctions
import Flapjack.Compiler.Backend.RegAlloc.Accessors
namespace Flapjack.Test.RegAllocExceptionFunctionsParity
open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-! Kernel replay of `scripts/hol-probes/reg_alloc_exception_functions_probe.out`:
original HOL generated `raise_`/`handle_` rows. HOL strings are `HolChar`
(`BitVec 8`) lists: `"x" = [120]`, `"ab" = [97, 98]`, `"q" = [113]`. -/

private def s0 : State :=
  { adj_ls := [[1], [0]], node_tag := [.Fixed 0, .Atemp], degrees := [1, 1], dim := 2,
    simp_wl := [], spill_wl := [], freeze_wl := [], avail_moves_wl := [], unavail_moves_wl := [],
    coalesced := [0, 1], move_related := [false, false], stack := [] }
private def x : List Basis.Pure.MlString.HolChar := [120#8]

-- ef_raise_fail=T
example : (raiseFail (α := Nat) x s0) = (.failure (.Fail x), s0) := rfl
-- ef_raise_sub=T
example : (raiseSubscript (α := Nat) s0) = (.failure .Subscript, s0) := rfl
-- ef_hs_success=M_success 5
example : (handleSubscript (fun s => (.success (5 : Nat), s)) (fun s => (.success 9, s)) s0).1 =
    .success 5 := rfl
-- ef_hs_catch=M_success 9
example : (handleSubscript raiseSubscript (fun s => (.success (9 : Nat), s)) s0).1 = .success 9 :=
  rfl
-- ef_hs_pass_fail=M_failure (Fail "x")
example : (handleSubscript (raiseFail x) (fun s => (.success (9 : Nat), s)) s0).1 =
    .failure (.Fail x) := rfl
-- ef_hs_failing_state=M_success 7
example : (handleSubscript (fun s => (.failure .Subscript, { s with dim := 7 }))
    (fun s => (.success s.dim, s)) s0).1 = .success 7 := rfl
-- ef_hs_accessor=M_success Atemp
example : (handleSubscript (nodeTagSub 9) (fun s => (.success .Atemp, s)) s0).1 = .success .Atemp :=
  by decide
-- ef_hf_catch=M_success 2
example : (handleFail (raiseFail [97#8, 98#8]) (fun e s => (.success e.length, s)) s0).1 =
    .success 2 := rfl
-- ef_hf_pass_sub=M_failure Subscript
example : (handleFail raiseSubscript (fun _ s => (.success (0 : Nat), s)) s0).1 =
    .failure .Subscript := rfl
-- ef_hf_success=M_success 4
example : (handleFail (fun s => (.success (4 : Nat), s)) (fun _ s => (.success 0, s)) s0).1 =
    .success 4 := rfl
-- ef_hf_failing_state=M_success 6
example : (handleFail (fun s => (.failure (.Fail [113#8]), { s with dim := 5 }))
    (fun e s => (.success (s.dim + e.length), s)) s0).1 = .success 6 := rfl

end Flapjack.Test.RegAllocExceptionFunctionsParity
