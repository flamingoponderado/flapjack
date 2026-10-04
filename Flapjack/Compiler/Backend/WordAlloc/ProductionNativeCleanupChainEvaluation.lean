import Flapjack.Compiler.Backend.WordAlloc.ProductionNativeCleanupSuffixEvaluation
import Flapjack.Compiler.Backend.WordCse.ProductionProgram
import Flapjack.Compiler.Backend.WordCse.Proofs.CompCorrect
import Flapjack.Pancake.Proofs.WordConvs.WordCse
import Flapjack.Pancake.Proofs.WordConvs.RemoveDead

/-! Executed post-SSA allocator cleanup chain.

After its SSA producer, the executed allocator
(`cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy`, `RiscV/WordDeadCode.lean`)
runs `wordRemoveDeadProgramViaHOL`, `wordCseProp` and then the suffix of
`ProductionNativeCleanupSuffixEvaluation`. Together these are the cleanup of HOL
`compile_single` (`word_to_wordScript.sml:27-32`: `remove_dead_prog`,
`word_common_subexp_elim`, `copy_prop`, `three_to_two_reg_prog`, `remove_unreach`,
`remove_dead_prog`). This module composes the whole chain with the original evaluation
theorems. It is Flapjack API infrastructure with no separate HOL original; the SSA and
colouring phases and the production/native evaluator relation are separate obligations. -/

namespace Flapjack.WordAlloc
open WordSemStateFiniteExact Compiler.Backend.WordCopy Compiler.Backend.WordInst
  Compiler.Backend.WordUnreach Compiler.Backend.WordCse RiscV
set_option autoImplicit false

/-- Native dead-code removal keeps every retained cutset field and Call body (Flapjack codec
infrastructure; no HOL declaration). -/
theorem removeDead_setsWf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (live : NumSet) (nlive : List WordStoreHOL)
    (lt : List (NumSet × NumSet)) (valid : WordAllocatorProgramSetsWf program) :
    WordAllocatorProgramSetsWf (removeDead program live nlive lt).1 := by
  refine WordConvs.removeDead_induct
    (fun p q => WordAllocatorProgramSetsWf p → WordAllocatorProgramSetsWf q)
    (fun _ h => h) (fun _ _ _ => by simp [WordAllocatorProgramSetsWf])
    (fun _ _ _ _ => by simp [WordAllocatorProgramSetsWf]) ?_ ?_ ?_ ?_ ?_ ?_
    program live nlive lt valid
  · intro s1 s2 s1' s2' ih1 ih2 h
    simp only [WordAllocatorProgramSetsWf] at h
    have h1 := ih1 h.1
    have h2 := ih2 h.2
    unfold WordConvs.rdSeq
    repeat' (first | split | simp_all [WordAllocatorProgramSetsWf])
  · intro b b' ih h
    simp only [WordAllocatorProgramSetsWf] at h ⊢
    exact ih h
  · intro cmp r ri e2 e3 e2' e3' ih2 ih3 h
    simp only [WordAllocatorProgramSetsWf] at h
    have h2 := ih2 h.1
    have h3 := ih3 h.2
    unfold WordConvs.rdIte
    repeat' (first | split | simp_all [WordAllocatorProgramSetsWf])
  · intro n b e b' ih h
    simp only [WordAllocatorProgramSetsWf] at h ⊢
    exact ⟨h.1, ih h.2⟩
  · intro v cut ret l1 l2 dest args ret' ih h
    simp only [WordAllocatorProgramSetsWf] at h ⊢
    exact ⟨⟨h.1.1, ih h.1.2⟩, trivial⟩
  · intro v cut ret l1 l2 dest args hn hp a b ret' hp' ihr ihh h
    simp only [WordAllocatorProgramSetsWf] at h ⊢
    exact ⟨⟨h.1.1, ihr h.1.2⟩, ihh h.2⟩

/-- Native `remove_dead_prog` keeps the canonical cutset image (Flapjack codec infrastructure). -/
theorem removeDeadProg_setsWf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (valid : WordAllocatorProgramSetsWf program) :
    WordAllocatorProgramSetsWf (removeDeadProg program) :=
  removeDead_setsWf program .ln [] [] valid

/-! The CSE fact producers and Get/Set/instruction clauses emit a move, a cutset-free
instruction-level program or the given original program (Flapjack codec infrastructure;
no HOL declarations). -/

theorem addToDataAux_setsWf {width : Nat} [NeZero width] (data : Knowledge)
    (destination : Nat) (key : List Nat) (original : WordLangProgHOL (BitVec width))
    (valid : WordAllocatorProgramSetsWf original) :
    WordAllocatorProgramSetsWf (addToDataAux data destination key original).2 := by
  unfold addToDataAux
  repeat' (first | split | simp_all [WordAllocatorProgramSetsWf])

theorem addToLoadAux_setsWf {width : Nat} [NeZero width] (data : Knowledge)
    (destination : Nat) (key : List Nat) (original : WordLangProgHOL (BitVec width))
    (valid : WordAllocatorProgramSetsWf original) :
    WordAllocatorProgramSetsWf (addToLoadAux data destination key original).2 := by
  unfold addToLoadAux
  repeat' (first | split | simp_all [WordAllocatorProgramSetsWf])

theorem addToDataConst_setsWf {width : Nat} [NeZero width] (data : Knowledge)
    (destination : Nat) (w : BitVec width) :
    WordAllocatorProgramSetsWf (addToDataConst data destination w).2 := by
  unfold addToDataConst
  repeat' (first | split | simp_all [WordAllocatorProgramSetsWf])

theorem wordCseInst_setsWf {width : Nat} [NeZero width] (data : Knowledge)
    (i : Compiler.Encoders.Asm.HolInst width) :
    WordAllocatorProgramSetsWf (Compiler.Backend.WordCse.wordCseInst data i).2 := by
  unfold Compiler.Backend.WordCse.wordCseInst
  repeat' (first | split | simp_all [WordAllocatorProgramSetsWf, addToData, addToDataAux_setsWf,
    addToLoadAux_setsWf, addToDataConst_setsWf])

theorem getClause_setsWf {width : Nat} [NeZero width] (data : Knowledge) (r : Nat)
    (x : WordStoreHOL) :
    WordAllocatorProgramSetsWf (getClause (width := width) data r x).2 := by
  unfold getClause
  repeat' (first | split | simp_all [WordAllocatorProgramSetsWf])

theorem setClause_setsWf {width : Nat} [NeZero width] (data : Knowledge) (x : WordStoreHOL)
    (e : WordLangExpHOL (BitVec width)) :
    WordAllocatorProgramSetsWf (setClause data x e).2 := by
  unfold setClause
  repeat' (first | split | simp_all [WordAllocatorProgramSetsWf])

/-- Native `word_cse` keeps every retained cutset field (Flapjack codec infrastructure). -/
theorem wordCse_setsWf {width : Nat} [NeZero width] (data : Knowledge)
    (program : WordLangProgHOL (BitVec width)) (valid : WordAllocatorProgramSetsWf program) :
    WordAllocatorProgramSetsWf (wordCse data program).2 := by
  fun_induction wordCse data program
  case case2 data i data' p produced =>
    simpa only [produced] using wordCseInst_setsWf data (Compiler.Encoders.Asm.HolInst.ofWordLangInst i)
  all_goals simp_all [WordAllocatorProgramSetsWf, getClause_setsWf, setClause_setsWf,
    addToDataAux_setsWf]

/-- Native `word_common_subexp_elim` keeps the canonical cutset image (Flapjack codec
infrastructure). -/
theorem wordCommonSubexpElim_setsWf {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (valid : WordAllocatorProgramSetsWf program) :
    WordAllocatorProgramSetsWf (wordCommonSubexpElim program) := by
  simpa only [wordCommonSubexpElim] using wordCse_setsWf emptyData program valid

/-- The whole executed post-SSA cleanup chain on an encoded flat program satisfies the
complete original evaluation conclusion for HOL `compile_single`'s cleaned program
`remove_dead_prog (remove_unreach (three_to_two_reg_prog F (copy_prop
(word_common_subexp_elim (remove_dead_prog p)))))`. Every executed phase succeeds and every
intermediate re-encoding is literal, derived from the source encoder; the only premises are
the original flat convention, source evaluation and non-error result. Locals may differ
only on non-returning results, exactly as in `evaluate_remove_dead_prog`. Flapjack
composition; no HOL original. -/
theorem nativeCleanupChain_evaluation {width : Nat} [NeZero width] {C F : Type}
    (source : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (state finalState : WordSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (sourceConditions : flatExpConventions native = true ∧
      evaluate native state = (result, finalState) ∧ result ≠ some .error) :
    ∃ unreached output : WordProg (BitVec width),
      wordRemoveUnreachViaHOL? (wordThreeToTwoReg (wordCopyPropViaHOL
        (wordCseProp (wordRemoveDeadProgramViaHOL source)))) = some unreached ∧
      wordRemoveDeadProgramViaHOL unreached = output ∧
      wordLangProgFromHOL (removeDeadProg (removeUnreach (threeToTwoRegProg false (copyProp
        (wordCommonSubexpElim (removeDeadProg native)))))) = some output ∧
      ∃ targetLocals : Spt (WordLocW width),
        evaluate (removeDeadProg (removeUnreach (threeToTwoRegProg false (copyProp
            (wordCommonSubexpElim (removeDeadProg native)))))) state =
          (result, {finalState with locals := targetLocals}) ∧
        match (generalizing := false) result with
        | none => True
        | some (.break _) => True
        | some (.continue _) => True
        | some _ => finalState.locals = targetLocals := by
  obtain ⟨flat, run, nonerror⟩ := sourceConditions
  -- first dead-code removal
  obtain ⟨dead, deadDecoded, deadRouted, deadLocals, deadRun, deadSame⟩ :=
    nativeDead_evaluation source native encoded state finalState result ⟨flat, run, nonerror⟩
  have sourceWf := productionProgram_setsWf source native encoded
  -- the actual configuration-independent flat preservation of `remove_dead_prog_conventions`
  have deadFlat : flatExpConventions (removeDeadProg native) = true :=
    (WordConvs.removeDeadProgConventions (fun _ => true) native
      { isa := .riscv, encode := fun _ => [], bigEndian := false, codeAlignment := 0,
        linkReg := none, avoidRegs := [], regCount := 0, fpRegCount := 0,
        twoRegArith := false, validImm := fun _ _ => false, addrOffset := (0, 0),
        hwOffset := (0, 0), byteOffset := (0, 0), jumpOffset := (0, 0),
        cjumpOffset := (0, 0), locOffset := (0, 0) }).1 flat
  -- CSE: executed/native transport, literal re-encoding, original correctness
  have cseDecoded := wordCommonSubexpElim_production_transport _ dead deadDecoded
  have cseEncoded : wordLangProgToHOL (wordCseProp (wordRemoveDeadProgramViaHOL source)) =
      some (wordCommonSubexpElim (removeDeadProg native)) := by
    rw [deadRouted]
    exact canonicalProgram_codec _ _
      (wordCommonSubexpElim_setsWf _ (removeDeadProg_setsWf native sourceWf)) cseDecoded
  have cseFlat := WordConvs.flat_exp_conventions_word_common_subexp_elim _ deadFlat
  have cseRun := word_common_subexp_elim_correct _ state result _ ⟨deadRun, deadFlat, nonerror⟩
  -- the post-CSE suffix
  obtain ⟨unreached, output, unreachRouted, finalRouted, finalDecoded, targetLocals, finalRun,
    finalSame⟩ := nativeCleanupSuffix_evaluation _ _ cseEncoded state _ result
      ⟨cseFlat, cseRun, nonerror⟩
  refine ⟨unreached, output, unreachRouted, finalRouted, finalDecoded, targetLocals, ?_, ?_⟩
  · simpa only using finalRun
  · cases result with
    | none => trivial
    | some value => cases value <;> simp_all
end Flapjack.WordAlloc
