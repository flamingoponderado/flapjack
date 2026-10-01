import Flapjack.Compiler.Backend.RegAlloc.Proofs.AccessorEqns
namespace Flapjack.Test.RegAllocAccessorsParity
open Flapjack Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-! Kernel replay of `scripts/hol-probes/reg_alloc_accessors_probe.out`: the
original HOL generated `ra_state` accessors on one concrete state, with the
`update_*` and (provisional) `*_sub` equations applied to the same inputs. -/

private def s0 : State :=
  { adj_ls := [[1], [0, 2], [1]], node_tag := [.Fixed 0, .Atemp, .Stemp], degrees := [1, 2, 1],
    dim := 3, simp_wl := [0], spill_wl := [1], freeze_wl := [2],
    avail_moves_wl := [(5, 0, 1)], unavail_moves_wl := [(6, 1, 2)], coalesced := [0, 1, 2],
    move_related := [true, false, true], stack := [2, 0] }

abbrev E := StateException

-- acc_get_dim=M_success 3
example : (getDim (γ := E) s0).1 = .success 3 := rfl
-- acc_get_stack=M_success [2; 0]
example : (getStack (γ := E) s0).1 = .success [2, 0] := rfl
-- acc_get_avail=M_success [(5,0,1)]
example : (getAvailMovesWl (γ := E) s0).1 = .success [(5, 0, 1)] := rfl
-- acc_set_dim=7
example : (setDim (γ := E) 7 s0).2.dim = 7 := rfl
-- acc_set_keeps=[1]
example : (setSimpWl (γ := E) [9, 8] s0).2.spill_wl = [1] := rfl
-- acc_adj_length=M_success 3
example : (adjLsLength (γ := E) s0).1 = .success 3 := rfl
-- acc_tag_sub=M_success Atemp
example : (nodeTagSub 1 s0).1 = .success .Atemp := by decide
-- acc_tag_sub_oob=M_failure Subscript
example : (nodeTagSub 3 s0).1 = .failure .Subscript := by decide
-- acc_adj_sub=M_success [0; 2]
example : (adjLsSub 1 s0).1 = .success [0, 2] := by decide
-- acc_large_oob=M_failure Subscript
example : (degreesSub 36893488147419103232 s0).1 = .failure .Subscript := by
  rw [degreesSubEqn]; simp [s0]
-- acc_update_deg=(M_success (),[1; 2; 9])
example : ((updateDegrees 2 9 s0).1, (updateDegrees 2 9 s0).2.degrees) = (.success (), [1, 2, 9]) := by
  decide
-- acc_update_oob=(M_failure Subscript,[1; 2; 1])
example : ((updateDegrees 3 9 s0).1, (updateDegrees 3 9 s0).2.degrees) =
    (.failure .Subscript, [1, 2, 1]) := by decide
-- acc_update_mr=[T; T; T]
example : (updateMoveRelated 1 true s0).2.move_related = [true, true, true] := by decide
-- acc_update_tag=[Stemp; Atemp; Stemp]
example : (updateNodeTag 0 .Stemp s0).2.node_tag = [.Stemp, .Atemp, .Stemp] := by decide
-- acc_coalesced_sub=M_success 2
example : (coalescedSub 2 s0).1 = .success 2 := by decide
-- acc_map_sub=M_success [[1]; [1]]
example : (stExMap adjLsSub [2, 0] s0).1 = .success [[1], [1]] := by decide
-- acc_map_oob=M_failure Subscript
example : (stExMap nodeTagSub [0, 5, 1] s0).1 = .failure .Subscript := by decide
-- acc_mupdate=M_success [1; 7; 3]
example : mUpdate StateException.Subscript (7 : Nat) 1 [1, 2, 3] = .success [1, 7, 3] := by decide

/-- `update_degrees_eqn` and the provisional `degrees_sub_eqn` at the probe inputs. -/
example : updateDegrees 2 9 s0 = (.success (), { s0 with degrees := [1, 2, 9] }) := by
  rw [updateDegreesEqn]; decide
example : degreesSub 1 s0 = (.success (holEl 1 s0.degrees), s0) := by
  rw [degreesSubEqn]; simp [s0]

/-- `st_ex_MAP_adj_ls_sub` (provisional) at `acc_map_sub`. -/
example : stExMap adjLsSub [2, 0] s0 = (.success ([2, 0].map fun i => holEl i s0.adj_ls), s0) :=
  stExMapAdjLsSub [2, 0] s0 (by decide)

end Flapjack.Test.RegAllocAccessorsParity
