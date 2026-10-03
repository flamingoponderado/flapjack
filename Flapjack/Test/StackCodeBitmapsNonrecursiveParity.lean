import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Nonrecursive

namespace Flapjack.Test.StackCodeBitmapsNonrecursiveParity
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Nonrecursive

example {width : Nat} [NeZero width] {C F : Type} (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.skip : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsSkip s post result execution

example {width : Nat} [NeZero width] {C F : Type} (v : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.halt v : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsHalt v s post result execution

example {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.ret n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsRet n s post result execution

example {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.raise n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsRaise n s post result execution

example {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.break n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsBreak n s post result execution

example {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.continue n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsContinue n s post result execution

example {width : Nat} [NeZero width] {C F : Type} (v : Nat) (name : StoreName) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.get v name : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsGet v name s post result execution

example {width : Nat} [NeZero width] {C F : Type} (name : StoreName) (v : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.set name v : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsSet name v s post result execution

example {width : Nat} [NeZero width] {C F : Type} (binop : HolBinop) (v src : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.opCurrHeap binop v src : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsOpCurrHeap binop v src s post result execution

example {width : Nat} [NeZero width] {C F : Type} (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.tick : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsTick s post result execution

example {width : Nat} [NeZero width] {C F : Type} (r l1 l2 : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.locValue r l1 l2 : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsLocValue r l1 l2 s post result execution

example {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackAlloc n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsStackAlloc n s post result execution

example {width : Nat} [NeZero width] {C F : Type} (n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackFree n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsStackFree n s post result execution

example {width : Nat} [NeZero width] {C F : Type} (r n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackLoad r n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsStackLoad r n s post result execution

example {width : Nat} [NeZero width] {C F : Type} (r rn : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackLoadAny r rn : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsStackLoadAny r rn s post result execution

example {width : Nat} [NeZero width] {C F : Type} (r n : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackStore r n : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsStackStore r n s post result execution

example {width : Nat} [NeZero width] {C F : Type} (r rn : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackStoreAny r rn : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsStackStoreAny r rn s post result execution

example {width : Nat} [NeZero width] {C F : Type} (r : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackGetSize r : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsStackGetSize r s post result execution

example {width : Nat} [NeZero width] {C F : Type} (r : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.stackSetSize r : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsStackSetSize r s post result execution

example {width : Nat} [NeZero width] {C F : Type} (r v : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.bitmapLoad r v : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsBitmapLoad r v s post result execution

example {width : Nat} [NeZero width] {C F : Type} (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.codeBufferWrite r1 r2 : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsCodeBufferWrite r1 r2 s post result execution

example {width : Nat} [NeZero width] {C F : Type} (r1 r2 : Nat) (s : StackSemStateFiniteExact width C F)
    (post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.dataBufferWrite r1 r2 : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsDataBufferWrite r1 r2 s post result execution

example {width : Nat} [NeZero width] {C F : Type}
    (op : HolMemop) (r a : Nat) (w : BitVec width)
    (s post : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (execution : StackSemEvaluate.evaluate ((.shMemOp op r (.addr a w) : HolProg width), s) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count s.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (s.compileOracle index).2.1)).foldl sptUnion s.code ∧
      post.bitmaps = s.bitmaps ++ ((List.range count).map
        (fun index => (s.compileOracle index).2.2)).flatten :=
  evaluateCodeBitmapsShMemOp op r a w s post result execution

end Flapjack.Test.StackCodeBitmapsNonrecursiveParity
