import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstall

/-! Same-input kernel applications of the original no-install helper observations.
These checks do not establish cross-language equivalence or compiler correctness. -/
namespace Flapjack.Test.WordToStackNoInstallHelpersParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native

-- ni_moves_empty
example : noInstall (wMoveAuxNative (width := 64) [] (0,0,0)) = true :=
  wMoveAuxNoInstall [] (0,0,0)
-- ni_moves_all_pairs
example : noInstall (wMoveAuxNative (width := 1)
    [(.inl 1,.inl 2),(.inl 1,.inr 2),(.inr 1,.inl 2),(.inr 1,.inr 2)] (0,0,0)) = true :=
  wMoveAuxNoInstall _ _
-- ni_load_install
example : noInstall (wStackLoadNative [(9,0),(0,99)] (.install 0 1 2 3 4 : HolProg 64)) =
    noInstall (.install 0 1 2 3 4 : HolProg 64) := wStackLoadNoInstall _ _
-- ni_load_skip
example : noInstall (wStackLoadNative [] (.skip : HolProg 1)) = noInstall (.skip : HolProg 1) :=
  wStackLoadNoInstall _ _
-- ni_reg1_direct
example : noInstall (wRegWrite1Native (fun r => .inst (.const r 7)) 2 (3,0,9) : HolProg 64) = true :=
  wRegWrite1NoInstall _ _ _ (by intro r; rfl)
-- ni_reg1_spill
example : noInstall (wRegWrite1Native (fun r => .inst (.const r 7)) 99 (0,0,9) : HolProg 1) = true :=
  wRegWrite1NoInstall _ _ _ (by intro r; rfl)
-- ni_reg2_direct
example : noInstall (wRegWrite2Native (fun r => .inst (.const r 7)) 2 (3,0,9) : HolProg 64) = true :=
  wRegWrite2NoInstall _ _ _ (by intro r; rfl)
-- ni_reg2_spill
example : noInstall (wRegWrite2Native (fun r => .inst (.const r 7)) 99 (0,0,9) : HolProg 1) = true :=
  wRegWrite2NoInstall _ _ _ (by intro r; rfl)
-- ni_live_zero
example : noInstall (wLiveNative (width := 64) (.ln,.ln) (.nil,99) (0,0,17)).1 = true :=
  wLiveNoInstall _ _ _
-- ni_live_frame
example : noInstall (wLiveNative (width := 1) (.ln,.ln) (.list [8,2],99) (4,7,3)).1 = true :=
  wLiveNoInstall _ _ _
-- ni_stack_move_install
example : noInstall (stackMoveNative 4 2 7 99 (.install 0 1 2 3 4 : HolProg 64)) =
    noInstall (.install 0 1 2 3 4 : HolProg 64) := stackMoveNoInstall _ _ _ _ _
-- ni_stack_move_zero
example : noInstall (stackMoveNative 0 99 0 7 (.skip : HolProg 1)) =
    noInstall (.skip : HolProg 1) := stackMoveNoInstall _ _ _ _ _
-- ni_copy_aux_zero
example : noInstall (copyRetAuxNative (width := 64) 0 99 0) = true := copyRetAuxNoInstall _ _ _
-- ni_copy_aux_many
example : noInstall (copyRetAuxNative (width := 1) 99 0 4) = true := copyRetAuxNoInstall _ _ _

-- Failure-bearing continuations are preserved, rather than assumed safe.
example : noInstall (wStackLoadNative [(9,0),(0,99)] (.install 0 1 2 3 4 : HolProg 64)) = false := by
  rw [wStackLoadNoInstall]; rfl
example : noInstall (stackMoveNative 4 2 7 99 (.install 0 1 2 3 4 : HolProg 64)) = false := by
  rw [stackMoveNoInstall]; rfl

end Flapjack.Test.WordToStackNoInstallHelpersParity
