import Flapjack.Compiler.Backend.WordAlloc.ProductionAllocatorSetWF

namespace Flapjack.WordAlloc

private theorem numSetCodec_wf (keys : List Nat) :
    sptWf (LoopToWord.toNumSetHOL keys) = true := by
  induction keys with
  | nil => rfl
  | cons key keys ih => exact sptWfInsert _ _ _ ih

/-- Canonical native sparse trees are fixed by the actual list-backed cutset
codec. Lookup preservation alone is insufficient for malformed tree shapes;
the original canonical-tree invariant supplies the genuine identity domain.
This is Flapjack codec infrastructure without a separate HOL original. -/
theorem canonicalNumSet_codec (tree : Spt Unit) (valid : sptWf tree = true) :
    LoopToWord.toNumSetHOL (LoopToWord.fromNumSetHOL tree) = tree := by
  apply (sptEqThm _ _ ⟨numSetCodec_wf _, valid⟩).2
  exact toNumSet_fromNumSet_lookup tree

/-- Both canonical native cutset fields survive the production codec exactly.
This is a representation theorem, not an assumed transition equivalence. -/
theorem canonicalCutsets_codec (sets : WordLangCutsetsHOL)
    (valid : sptWf sets.1 = true ∧ sptWf sets.2 = true) :
    wordCutsetsToHOL (wordCutsetsFromHOL sets) = sets := by
  rcases sets with ⟨first, second⟩
  rcases valid with ⟨firstWf, secondWf⟩
  simp only [wordCutsetsToHOL, wordCutsetsFromHOL,
    canonicalNumSet_codec first firstWf, canonicalNumSet_codec second secondWf]

/-- Actual cutset normalization is the identity on the complete canonical
native program image, including returning and non-returning call handlers.
The stronger existing source-codec invariant is explicit here; no output
well-formedness or evaluator result is assumed by a pass theorem. This is
Flapjack representation infrastructure with no independent HOL original. -/
theorem canonicalProgram_normalize {width : Nat}
    (program : WordLangProgHOL (BitVec width))
    (valid : WordAllocatorProgramSetsWf program) :
    wordLangProgNormalizeCutsets program = program := by
  fun_induction wordLangProgNormalizeCutsets program <;>
    simp_all [WordAllocatorProgramSetsWf, StackOnlySetsWf,
      canonicalNumSet_codec, canonicalCutsets_codec]
  case case9 =>
    unfold WordAllocatorProgramSetsWf at valid
    repeat' (split at valid <;>
      simp_all [StackOnlySetsWf, canonicalCutsets_codec])

/-- On a genuinely canonical native input the actual decoder/re-encoder
roundtrip is literal full-program identity, rather than merely normalized
identity. Decoder success names the observed projection; its existence is
not inferred here. There is no HOL declaration for this production codec. -/
theorem canonicalProgram_codec {width : Nat}
    (native : WordLangProgHOL (BitVec width)) (production : WordProg (BitVec width))
    (valid : WordAllocatorProgramSetsWf native)
    (decoded : wordLangProgFromHOL native = some production) :
    wordLangProgToHOL production = some native := by
  rw [wordLangProgToHOL_of_fromHOL native production decoded,
    canonicalProgram_normalize native valid]

/-- Every actually accepted production encoding is already a fixed point of
cutset normalization. The invariant is obtained from the source encoder,
without a well-formed-output premise. This is source-codec infrastructure. -/
theorem productionProgram_normalize {width : Nat}
    (production : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL production = some native) :
    wordLangProgNormalizeCutsets native = native :=
  canonicalProgram_normalize native (productionProgram_setsWf production native encoded)

end Flapjack.WordAlloc
