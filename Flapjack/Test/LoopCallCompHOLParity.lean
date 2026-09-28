import Flapjack.Pancake.LoopLive

/-! Direct parity for the exact `loopCallCompHOL` port of `loop_call$comp`
    (`loop_callScript.sml:18-98`) and `optimiseHOL` of `loop_live$optimise`
    (`loop_liveScript.sml:221`).  Each row matches a committed original-HOL
    `EVAL` row in `scripts/hol-probes/loop_call_comp_probe.out` and
    `scripts/hol-probes/loop_live_optimise_probe.out`, evaluated here over the
    exact `HolLoopProg`/`Spt` carriers. -/

namespace Flapjack.Test.LoopCallCompHOLParity

open Flapjack

private instance : NeZero 32 := ⟨by decide⟩
private instance : NeZero 8 := ⟨by decide⟩

private abbrev P32 : Type := HolLoopProg 32
private abbrev P8 : Type := HolLoopProg 8

private def live (key value : Nat) : Spt Nat := sptInsert key value (.ln : Spt Nat)
private def live2 (k1 v1 k2 v2 : Nat) : Spt Nat := sptInsert k2 v2 (sptInsert k1 v1 (.ln : Spt Nat))

/-- Replay all 21 direct original-HOL `loop_call$comp` rows at width 32. -/
def loopCallCompHOLGuard : Bool :=
  -- skip=Skip
  (match (loopCallCompHOL (.ln : Spt Nat) (.skip : P32)).1 with
   | .skip => true | _ => false) &&
  -- call_dest=Call NONE (SOME 3) [1; 2] NONE
  (match (loopCallCompHOL (.ln : Spt Nat) (.call none (some 3) [1, 2] none : P32)).1 with
   | .call none (some 3) [1, 2] none => true | _ => false) &&
  -- call_last=Call NONE (SOME 9) [1] NONE
  (match (loopCallCompHOL (live 2 9) (.call none none [1, 2] none : P32)).1 with
   | .call none (some 9) [1] none => true | _ => false) &&
  -- call_last_loc=NONE
  (sptLookup 2 (loopCallCompHOL (live 2 9) (.call none none [1, 2] none : P32)).2 == none) &&
  -- call_empty=Skip
  (match (loopCallCompHOL (.ln : Spt Nat) (.call none none ([] : List Nat) none : P32)).1 with
   | .skip => true | _ => false) &&
  -- loc_value=SOME 7
  (sptLookup 1 (loopCallCompHOL (.ln : Spt Nat) (.locValue 1 7 : P32)).2 == some 7) &&
  -- assign_var_copy=SOME 7
  (sptLookup 1 (loopCallCompHOL (live 2 7) (.assign 1 (.var 2) : P32)).2 == some 7) &&
  -- assign_var_kill=NONE
  (sptLookup 1 (loopCallCompHOL (live 1 7) (.assign 1 (.var 2) : P32)).2 == none) &&
  -- assign_expr_kill=NONE
  (sptLookup 1 (loopCallCompHOL (live 1 7) (.assign 1 (.const 9) : P32)).2 == none) &&
  -- shmem_clears=NONE
  (sptLookup 1 (loopCallCompHOL (live 1 7) (.shMem .load 1 (.const 0) : P32)).2 == none) &&
  -- load32_kill=NONE
  (sptLookup 1 (loopCallCompHOL (live 1 7) (.load32 0 1 : P32)).2 == none) &&
  -- loadbyte_keep=NONE
  (sptLookup 1 (loopCallCompHOL (.ln : Spt Nat) (.loadByte 0 1 : P32)).2 == none) &&
  -- seq_clears=Seq (LocValue 2 8) (Assign 3 (Var 2))
  (match (loopCallCompHOL (live 1 7)
      (.seq (.locValue 2 8) (.assign 3 (.var 2)) : P32)).1 with
   | .seq (.locValue 2 8) (.assign 3 (.var 2)) => true | _ => false) &&
  -- if_clears=If Equal 0 (Reg 2) (LocValue 2 8) (Assign 3 (Var 2)) LN
  (match (loopCallCompHOL (live 1 7)
      (.ite .equal 0 (.reg 2) (.locValue 2 8) (.assign 3 (.var 2)) (.ln : NumSet) : P32)).1 with
   | .ite .equal 0 (.reg 2) (.locValue 2 8) (.assign 3 (.var 2)) .ln => true | _ => false) &&
  -- loop_clears=Loop LN (LocValue 2 8) LN
  (match (loopCallCompHOL (live 1 7)
      (.loop (.ln : NumSet) (.locValue 2 8) (.ln : NumSet) : P32)).1 with
   | .loop .ln (.locValue 2 8) .ln => true | _ => false) &&
  -- mark_keeps=SOME 8
  (sptLookup 2 (loopCallCompHOL (live 1 7) (.mark (.locValue 2 8) : P32)).2 == some 8) &&
  -- ffi_clears=NONE
  (sptLookup 1 (loopCallCompHOL (live 1 7)
      (.ffi (Flapjack.Basis.Pure.MlString.ofString "host") 1 2 3 4 (.ln : NumSet) : P32)).2 == none) &&
  -- primitive_deletes=NONE
  (sptLookup 1 (loopCallCompHOL (live2 1 7 2 8)
      (.primitive [1] .addCarry [2, 3] : P32)).2 == none) &&
  -- longmul_deletes=NONE
  (sptLookup 1 (loopCallCompHOL (live2 1 7 2 8)
      (.arith (.longMul 1 2 3 4) : P32)).2 == none) &&
  -- div_deletes=NONE
  (sptLookup 1 (loopCallCompHOL (live 1 7) (.arith (.div 1 2 3) : P32)).2 == none) &&
  -- fallback_keeps=SOME 7
  (sptLookup 1 (loopCallCompHOL (live 1 7) (.store (.const 0) 1 : P32)).2 == some 7)

#guard loopCallCompHOLGuard

/-- Replay all 4 direct original-HOL `optimise` rows at width 8. -/
def optimiseHOLGuard : Bool :=
  -- skip=Mark Skip
  (match optimiseHOL (.skip : P8) with
   | .mark .skip => true | _ => false) &&
  -- loc_value=Mark Skip
  (match optimiseHOL (.locValue 3 7 : P8) with
   | .mark .skip => true | _ => false) &&
  -- seq=Mark (Seq (Mark Skip) (Mark Skip))
  (match optimiseHOL (.seq (.skip : P8) (.skip : P8)) with
   | .mark (.seq (.mark .skip) (.mark .skip)) => true | _ => false) &&
  -- ffi=Mark (FFI «f» 1 2 3 4 LN)
  (match optimiseHOL
      (.ffi (Flapjack.Basis.Pure.MlString.ofString "f") 1 2 3 4 (.ln : NumSet) : P8) with
   | .mark (.ffi _ 1 2 3 4 .ln) => true | _ => false)

#guard optimiseHOLGuard

def runChecks : IO Bool := do
  if loopCallCompHOLGuard then
    IO.println "PASS exact loopCallCompHOL matches all 21 loop_call$comp HOL rows"
  else
    IO.println "FAIL exact loopCallCompHOL matches all 21 loop_call$comp HOL rows"
  if optimiseHOLGuard then
    IO.println "PASS exact optimiseHOL matches all 4 optimise HOL rows"
  else
    IO.println "FAIL exact optimiseHOL matches all 4 optimise HOL rows"
  pure (loopCallCompHOLGuard && optimiseHOLGuard)

end Flapjack.Test.LoopCallCompHOLParity
