module

public import Flapjack.Compiler.Backend.DataToWord.Total
public import Flapjack.Compiler.Backend.DataToWord.MaxHeapLimit

@[expose] public section

/-! Configuration and part-name simplifications for data-to-word compilation
(`data_to_wordProofScript.sml` lines 2469-2480). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.Compiler.Backend.DataToWord

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "max_heap_limit_has_fp_ops"
  (word_dimension_as_width := width)]
theorem maxHeapLimit_hasFpOps (width : Nat) [NeZero width] (conf : Config) (b : Bool) :
    maxHeapLimit width { conf with hasFpOps := b } = maxHeapLimit width conf := by
  simp [maxHeapLimit, shiftLength]

@[hol "cakeml/compiler/backend/proofs/data_to_wordProofScript.sml" "FST_compile_part"
  (words_as_type_indexed_bitvec)]
theorem fst_compilePart {width : Nat} [NeZero width] (a : Config)
    (b : Nat × Nat × Flapjack.Compiler.Backend.DataLang.Prog) :
    (compilePart a b : Nat × Nat × WordLangProgHOL (BitVec width)).1 = b.1 := by
  rcases b with ⟨n, m, p⟩
  rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs
