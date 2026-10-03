import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompileSemantics

namespace Flapjack.Test.StackRawCallCompileSemanticsParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall

example {width : Nat} [NeZero width] {C F : Type} (code : List (Nat × HolProg width))
    (source : StackSemStateFiniteExact width C F) (start : Nat)
    (distinct : (code.map Prod.fst).Nodup) (useStack : source.useStack = true)
    (sourceCode : source.code = sptFromAList code)
    (nonFail : StackSemEvaluate.semantics start source ≠ .fail) :
    StackSemEvaluate.semantics start {source with code := sptFromAList (compile code)} =
      StackSemEvaluate.semantics start source :=
  CompileSemantics.compileSemantics code source start distinct useStack sourceCode nonFail

example {C F : Type} (code : List (Nat × HolProg 1))
    (source : StackSemStateFiniteExact 1 C F) (start : Nat)
    (distinct : (code.map Prod.fst).Nodup) (useStack : source.useStack = true)
    (sourceCode : source.code = sptFromAList code)
    (nonFail : StackSemEvaluate.semantics start source ≠ .fail) :
    StackSemEvaluate.semantics start {source with code := sptFromAList (compile code)} =
      StackSemEvaluate.semantics start source :=
  CompileSemantics.compileSemantics code source start distinct useStack sourceCode nonFail

example {C F : Type} (code : List (Nat × HolProg 8))
    (source : StackSemStateFiniteExact 8 C F) (start : Nat)
    (distinct : (code.map Prod.fst).Nodup) (useStack : source.useStack = true)
    (sourceCode : source.code = sptFromAList code)
    (nonFail : StackSemEvaluate.semantics start source ≠ .fail) :
    StackSemEvaluate.semantics start {source with code := sptFromAList (compile code)} =
      StackSemEvaluate.semantics start source :=
  CompileSemantics.compileSemantics code source start distinct useStack sourceCode nonFail

example {C F : Type} (code : List (Nat × HolProg 64))
    (source : StackSemStateFiniteExact 64 C F) (start : Nat)
    (distinct : (code.map Prod.fst).Nodup) (useStack : source.useStack = true)
    (sourceCode : source.code = sptFromAList code)
    (nonFail : StackSemEvaluate.semantics start source ≠ .fail) :
    StackSemEvaluate.semantics start {source with code := sptFromAList (compile code)} =
      StackSemEvaluate.semantics start source :=
  CompileSemantics.compileSemantics code source start distinct useStack sourceCode nonFail

example {C F : Type} (code : List (Nat × HolProg 80))
    (source : StackSemStateFiniteExact 80 C F) (start : Nat)
    (distinct : (code.map Prod.fst).Nodup) (useStack : source.useStack = true)
    (sourceCode : source.code = sptFromAList code)
    (nonFail : StackSemEvaluate.semantics start source ≠ .fail) :
    StackSemEvaluate.semantics start {source with code := sptFromAList (compile code)} =
      StackSemEvaluate.semantics start source :=
  CompileSemantics.compileSemantics code source start distinct useStack sourceCode nonFail

end Flapjack.Test.StackRawCallCompileSemanticsParity
