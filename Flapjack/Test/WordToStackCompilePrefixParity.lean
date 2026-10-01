import Flapjack.Compiler.Backend.WordToStack.Proofs.CompilePrefix

namespace Flapjack.Test.WordToStackCompilePrefixParity
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm

/-- Same-input regression application of the entire source theorem to actual
compiler outputs. This test helper has no separate HOL original. -/
private theorem actualPrefix (conf : AsmConfigExact 64) (perf : Bool)
    (program : WordLangProgHOL (BitVec 64))
    (bs : AppList (BitVec 64) × Nat) (frame : Nat × Nat × Nat) :
    (appListAppend bs.1).IsPrefix (appListAppend (compNative conf perf program bs frame).2.1) :=
  compImpIsPrefix conf perf program bs frame _ _ rfl

private def initial : AppList (BitVec 64) × Nat := (.append (.list [4]) (.list [7]),0)
private def allocation : WordLangProgHOL (BitVec 64) := .alloc 0 (.ln,.ln)

example (c : AsmConfigExact 64) : (appListAppend initial.1).IsPrefix
    (appListAppend (compNative c false .skip initial (4,1,2)).2.1) := actualPrefix c false .skip initial (4,1,2)
example (c : AsmConfigExact 64) : (appListAppend initial.1).IsPrefix
    (appListAppend (compNative c false allocation initial (4,1,2)).2.1) := actualPrefix c false allocation initial (4,1,2)
example (c : AsmConfigExact 64) : (appListAppend initial.1).IsPrefix
    (appListAppend (compNative c false (.mustTerminate allocation) initial (4,1,2)).2.1) :=
  actualPrefix c false (.mustTerminate allocation) initial (4,1,2)
example (c : AsmConfigExact 64) : (appListAppend initial.1).IsPrefix
    (appListAppend (compNative c false (.seq allocation allocation) initial (4,1,2)).2.1) :=
  actualPrefix c false (.seq allocation allocation) initial (4,1,2)
example (c : AsmConfigExact 64) : (appListAppend initial.1).IsPrefix
    (appListAppend (compNative c false (.ite .equal 0 (.reg 1) allocation allocation)
      initial (4,1,2)).2.1) := actualPrefix c false (.ite .equal 0 (.reg 1) allocation allocation) initial (4,1,2)
example (c : AsmConfigExact 64) : (appListAppend initial.1).IsPrefix
    (appListAppend (compNative c false (.loop .ln allocation .ln) initial (4,1,2)).2.1) :=
  actualPrefix c false (.loop .ln allocation .ln) initial (4,1,2)
example (c : AsmConfigExact 64) : (appListAppend initial.1).IsPrefix
    (appListAppend (compNative c true (.call (some ([],(.ln,.ln),allocation,7,8))
      (some 9) [] none) initial (4,1,2)).2.1) := actualPrefix c true (.call (some ([],(.ln,.ln),allocation,7,8)) (some 9) [] none) initial (4,1,2)
example (c : AsmConfigExact 64) : (appListAppend initial.1).IsPrefix
    (appListAppend (compNative c false (.call (some ([],(.ln,.ln),allocation,7,8))
      (some 9) [] (some (99,allocation,11,12))) initial (4,1,2)).2.1) := actualPrefix c false (.call (some ([],(.ln,.ln),allocation,7,8)) (some 9) [] (some (99,allocation,11,12))) initial (4,1,2)
example (c : AsmConfigExact 64) : (appListAppend initial.1).IsPrefix
    (appListAppend (compNative c false (.storeConsts 0 1 2 3 [(true,7),(false,8)])
      initial (4,1,2)).2.1) := actualPrefix c false (.storeConsts 0 1 2 3 [(true,7),(false,8)]) initial (4,1,2)

end Flapjack.Test.WordToStackCompilePrefixParity
