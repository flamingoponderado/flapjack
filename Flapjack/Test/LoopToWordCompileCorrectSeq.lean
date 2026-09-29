import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Seq

/-!
# Loop-to-Word `compile_correct` Seq regression

The proof case relies on `compHOL` threading the label pair returned by the
first child into compilation of the second child. Keep that exact recursive
equation pinned here, beside a direct typecheck of the tagged Seq case.
-/

namespace Flapjack.Test.LoopToWordCompileCorrectSeq

open Flapjack Flapjack.LoopToWord

example {width : Nat} [NeZero width] (ctxt : Spt Nat)
    (c1 c2 : HolLoopProg width) (labels : Nat × Nat) :
    (LoopToWord.compHOL ctxt (.seq c1 c2) labels).1 =
      .seq (LoopToWord.compHOL ctxt c1 labels).1
        (LoopToWord.compHOL ctxt c2 (LoopToWord.compHOL ctxt c1 labels).2).1 := by
  simp only [LoopToWord.compHOL]

example {width : Nat} [NeZero width] {C F : Type}
    (c1 c2 : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    ((∀ res s1, (res, s1) = LoopSemStateFiniteExact.evaluate c1 s ∧ res = none →
        LoopToWord.CompileCorrect.PropertyAt C c2 s1) ∧
      LoopToWord.CompileCorrect.PropertyAt C c1 s) →
      LoopToWord.CompileCorrect.PropertyAt C (.seq c1 c2) s :=
  compileCorrect_Seq c1 c2 s

end Flapjack.Test.LoopToWordCompileCorrectSeq
