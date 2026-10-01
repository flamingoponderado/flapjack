import Flapjack.Pancake.WordLang.MaxVar

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Literal native program limit. The source rounds its program maximum to the
next strictly larger multiple of four, then adds one. This includes the full
native occurrence analysis, rather than taking a precomputed numeric maximum.
The executed numeric helper and its upstream production maximum are tracked
separately by bead .30.1.2.1; this native definition alone does not complete
that route. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "limit_var_def"
  (words_as_type_indexed_bitvec)]
def limitVar {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : Nat :=
  let maximum := maxVarHOL program
  maximum + (4 - maximum % 4) + 1

end Flapjack.Compiler.Backend.WordAlloc
