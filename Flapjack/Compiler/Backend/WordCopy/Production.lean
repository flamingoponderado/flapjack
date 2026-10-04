import Flapjack.Compiler.Backend.WordCopy.ProductionDecoderDomain
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAInputCodec
import Flapjack.RiscV.WordCopyProp

namespace Flapjack.RiscV
open Compiler.Backend

/-! Fixed-width production routing through the reviewed copyProp definition.
There is no independent HOL declaration for this carrier adapter. Input codec
rejection preserves the broader executable extension; on the source image,
the actual decoder result is returned using a proved availability obligation.
There is no output fallback or supplied successful-decoder premise. -/

def wordCopyPropViaHOL {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) : WordProg (BitVec width) :=
  match encoded : wordLangProgToHOL program with
  | none => wordCopyProp program
  | some native =>
      (wordLangProgFromHOL (WordCopy.copyProp native)).get
        (WordCopy.copyProp_decoderDomain native
          (WordAlloc.ssaInput_decoderClosure program native encoded))

/-- Every accepted actual input returns the full reviewed native pass output.
Decoder availability is derived from the actual encoder and the native pass;
no successful output or desired correspondence is a premise. -/
theorem wordCopyPropViaHOL_sourceNative {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    ∃ output : WordProg (BitVec width),
      wordLangProgFromHOL (WordCopy.copyProp native) = some output ∧
      wordCopyPropViaHOL program = output := by
  have available := WordCopy.copyProp_decoderDomain native
    (WordAlloc.ssaInput_decoderClosure program native encoded)
  obtain ⟨output, decoded⟩ := Option.isSome_iff_exists.mp available
  refine ⟨output, decoded, ?_⟩
  unfold wordCopyPropViaHOL
  split
  · rename_i missing
    rw [encoded] at missing
    cases missing
  · rename_i selected selectedEq
    have equal : selected = native := Option.some.inj (selectedEq.symm.trans encoded)
    subst selected
    simp only [decoded, Option.get_some]

/-- Broader executable-only input keeps its previous copy propagation. -/
theorem wordCopyPropViaHOL_rejected {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (rejected : wordLangProgToHOL program = none) :
    wordCopyPropViaHOL program = wordCopyProp program := by
  unfold wordCopyPropViaHOL
  split
  · rfl
  · rename_i selected selectedEq
    rw [rejected] at selectedEq
    cases selectedEq

end Flapjack.RiscV
