import Flapjack.Misc.Sptree.FromList2
import Flapjack.Compiler.Backend.WordAlloc.ProductionFullSSACanonicalImage
import Flapjack.Compiler.Backend.WordAlloc.Proofs.FullSSACorrect

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

end Flapjack.WordAlloc
