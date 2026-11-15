module

import Flapjack.Compiler.Inference.Unify.Encoding
meta import Flapjack.Compiler.Inference.Unify.Encoding
meta import Flapjack.HOL.Unification.Term

/-! Constructor and malformed-input checks for the source term encoding. -/
open Flapjack.HOL.Unification Flapjack.Compiler.Inference Flapjack.Compiler.Inference.Unify

#guard decide (encodeInferT (.app [.uvar 4, .varDb 2] 9) =
  .pair (.const .tappTag) (.pair (.const (.tcTag 9))
    (.pair (.var 4) (.pair (.const (.dbTag 2)) (.const .nullTag)))))

#guard decodeInferT (.pair (.const .tappTag) (.const .nullTag)) == .uvar 5
#guard decodeInferTs (.const (.tcTag 9)) == []
#guard pairCount (α := Atom) (.pair (.var 1) (.pair (.var 2) (.const .nullTag))) == 2

example : vars (α := Atom) (.pair (.var 1) (.pair (.var 2) (.const .nullTag))) 2 := by
  simp [vars]
