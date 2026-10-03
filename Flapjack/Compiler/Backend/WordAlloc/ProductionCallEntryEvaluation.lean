import Flapjack.Misc.Sptree.FromList2
import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeSSAEvaluation

namespace Flapjack.WordAlloc
open Compiler.Backend.WordAlloc WordSemStateFiniteExact

/-- The actual native call environment supplies the complete original SSA
entry domain from its argument list. Size, stack and payloads are unrestricted.
This is derived caller infrastructure without an independent HOL original. -/
theorem nativeCallEntry_domain {width : Nat} [NeZero width] {C F : Type}
    (arguments : List (WordLocW width)) (size : Option Nat)
    (state : WordSemStateFiniteExact width C F) :
    sptDomain (WordSemStateFiniteExact.callEnv arguments size state).locals =
      (fun key => key ∈ evenList arguments.length) := by
  simpa only [WordSemStateFiniteExact.callEnv, evenList] using sptDomainFromList2 arguments

open Classical in
/-- On the real call environment the actual SSA facade satisfies the full
original semantic conclusion without a caller-supplied locals-domain premise.
Its count is the real argument length, as in the source call branch after
the code lookup's arity check. Actual output availability and literal body
encoding are constructed, not assumed. This API composition has no separate
HOL original; cleanup and production-evaluator simulation remain separate. -/
theorem nativeSsa_callEntryEvaluation {width : Nat} [NeZero width] {C F : Type}
    (source : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (arguments : List (WordLocW width)) (size : Option Nat)
    (state : WordSemStateFiniteExact width C F) :
    ∃ (output : WordSsaState × List Nat × WordProg (BitVec width))
        (nativeOutput : WordLangProgHOL (BitVec width)),
      wordFullSsaCcTransNativeWithState arguments.length source = some output ∧
      wordLangProgToHOL output.2.2 = some nativeOutput ∧
      ∃ permutation : Nat → Nat → Nat,
        let sourceRun := evaluate native {(WordSemStateFiniteExact.callEnv arguments size state) with permute := permutation}
        if sourceRun.1 = some .error then True else
          let targetRun := evaluate nativeOutput (WordSemStateFiniteExact.callEnv arguments size state)
          sourceRun.1 = targetRun.1 ∧ wordStateEqRel sourceRun.2 targetRun.2 ∧
            match sourceRun.1 with
            | none => True
            | some (.break _) => True
            | some (.continue _) => True
            | some _ => sourceRun.2.locals = targetRun.2.locals :=
  nativeSsa_evaluation arguments.length source native encoded (WordSemStateFiniteExact.callEnv arguments size state)
    (nativeCallEntry_domain arguments size state)

end Flapjack.WordAlloc
