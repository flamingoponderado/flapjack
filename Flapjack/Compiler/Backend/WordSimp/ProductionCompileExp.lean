import Flapjack.Compiler.Backend.WordSimp.ProductionConstFp
import Flapjack.Compiler.Backend.WordSimp.ProductionDuplicateIf
import Flapjack.Compiler.Backend.WordSimp.ProductionPushOutIf

namespace Flapjack.Compiler.Backend.WordSimp

open RiscV
set_option autoImplicit false

/-- The executed pre-SSA simplification `wordToWordPreSsa`
(`wordPushOutIf ∘ wordSimpDuplicateIf ∘ wordConstFp`, with `wordConstFp` starting with
`Seq_assoc`) is the reviewed native `word_simp$compile_exp` (`word_simpScript.sml:491-497`:
`Seq_assoc Skip`, `const_fp`, `simp_duplicate_if`, `push_out_if`) on the input codec image.
Composes the per-pass transports; no output encoding is assumed. Flapjack carrier
infrastructure; no separate HOL declaration. -/
theorem wordToWordPreSsa_production {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    wordLangProgToHOL (wordToWordPreSsa program) = some (compileExp native) := by
  simp only [wordToWordPreSsa, compileExp]
  exact pushOutIf_production _ _
    (simpDuplicateIf_production _ _ (wordConstFp_production program native encoded))

end Flapjack.Compiler.Backend.WordSimp
