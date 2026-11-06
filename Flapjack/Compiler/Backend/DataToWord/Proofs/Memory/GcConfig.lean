import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Abstract
import Flapjack.Compiler.Backend.GenGc

/-! Source configuration for the abstract collector. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

open Classical in
/-- The source configuration classifies mutable heap tags as references. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "make_gc_conf_def"]
noncomputable def makeGcConf {α : Type} (limit : Nat) : GenGc.Config (HeapTag × α) :=
  ⟨limit, fun value => decide (isMutTag value.1)⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
