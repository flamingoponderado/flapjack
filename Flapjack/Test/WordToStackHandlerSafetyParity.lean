import Flapjack.Compiler.Backend.WordToStack.Proofs.HandlerLabels

/-! Same-input original actual-compiler guard/handler-safety observations.
These kernel regressions do not establish cross-language equivalence. -/
namespace Flapjack.Test.WordToStackHandlerSafetyParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

private def snapshot {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (registers : Nat) (rows : List (Nat × Nat × WordLangProgHOL (BitVec width))) : Bool × Prop :=
  (rows.all (fun row => goodHandlersHOL row.1 row.2.2),
   stackGoodHandlerLabels (compileWordToStackNative c false registers rows (.append (.list [8]) (.list [2]),5)).1)

macro "handler_safety_replay" : tactic => `(tactic|
  (dsimp only [snapshot]
   apply Prod.ext
   · simp +decide [goodHandlersHOL]
   · apply propext
     simp only [stackGoodHandlerLabels, compileWordToStackNative, compileProgNative,
       List.map_cons, List.map_nil, List.mem_cons, List.mem_nil_iff, or_false,
       Set.ofPred_or, Set.ofPred_eq_eq_singleton, Set.ofPred_false,
       Set.image_union, Set.image_singleton, Set.image_empty,
       Set.sUnion_union, Set.sUnion_singleton, Set.sUnion_empty]
     simp +decide [BackendProps.restrictNonzero, Set.subset_def,
       maxVarHOL, compNative, getCodeLabels, getCodeLabelsHOL,
         stackGetHandlerLabels, goodHandlersHOL, wRegWrite1Native, wRegWrite2Native,
         wStackLoadNative, WordToStackRegFormat.wReg1, WordToStackRegFormat.wReg2,
         callDestNative, seqStackFreeNative, wLiveNative, stackArgsNative,
         stackHandlerArgsNative, stackMoveNative, copyRetNative, copyRetAuxNative,
         popHandlerNative, pushHandlerNative, listSeq, WordToStack.stackArgCount,
         WordToStack.numStackRet, WordToStack.skipFree, WordToStack.stackFree,
         WordToStack.insertBitmap, or_assoc, or_left_comm, or_comm]))

-- hls_empty
example (c : AsmConfigExact 64) : snapshot c 4 [] = (true,True) := by
  handler_safety_replay

-- hls_duplicates
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.locValue 0 8),(7,0,.locValue 99 9)] = (true,True) := by
  handler_safety_replay

-- hls_owned
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,5)))] = (true,True) := by
  handler_safety_replay

-- hls_wrong_owner
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,9,5)))] = (false,False) := by
  handler_safety_replay

-- hls_wrong_zero
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,9,0)))] = (false,True) := by
  handler_safety_replay

-- hls_wrong_one
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,9,1))),(9,0,.skip)] = (false,True) := by
  handler_safety_replay

-- hls_tail_drop
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.call none (some 8) [] (some (0,.locValue 0 9,999,6)))] = (true,True) := by
  handler_safety_replay

-- hls_same_owner_twice
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,5))),(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,6)))] = (true,True) := by
  handler_safety_replay

-- hls_nested
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.seq (.loop .ln (.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,5))) .ln) (.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,6))))] = (true,True) := by
  handler_safety_replay

-- hls_nested_bad
example (c : AsmConfigExact 64) : snapshot c 4 [(7,0,.seq (.loop .ln (.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,9,5))) .ln) (.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,6))))] = (false,False) := by
  handler_safety_replay

-- hls_threaded
example (c : AsmConfigExact 64) : snapshot c 4 [(7,5,.alloc 0 (.ln,.ln)),(8,0,.storeConsts 0 0 0 0 [])] = (true,True) := by
  handler_safety_replay

-- hls_width_one
example (c : AsmConfigExact 1) : snapshot c 0 [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) [] (some (0,.locValue 0 9,7,5)))] = (true,True) := by
  handler_safety_replay

-- Apply the full public theorem with arbitrary config/registers/bitmap input,
-- complete output residual and a genuinely returning owned handler.
example {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (registers : Nat) (bs : AppList (BitVec width) × Nat) :
    let rows : List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
      [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) []
        (some (0,.locValue 0 9,7,5)))]
    stackGoodHandlerLabels (compileWordToStackNative c false registers rows bs).1 := by
  let rows : List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
    [(7,0,.call (some ([],(.ln,.ln),.locValue 0 8,11,12)) (some 10) []
      (some (0,.locValue 0 9,7,5)))]
  let result := compileWordToStackNative c false registers rows bs
  change stackGoodHandlerLabels result.1
  exact wordToStackGoodHandlerLabelsIncr c registers rows bs result.1
    result.2.1 result.2.2 rfl rfl

end Flapjack.Test.WordToStackHandlerSafetyParity
