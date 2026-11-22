module

public import Flapjack.Compiler.Backend.BackendProof.LabelsOk
public import Flapjack.Compiler.Backend.DataToWord.Proofs.CompileLabPres
public import Flapjack.Compiler.Backend.BackendProof.PerfCalls
public import Flapjack.Compiler.Backend.StackToLab.Proofs.CompileLabPres
public import Flapjack.Compiler.Backend.WordToStack.Proofs.ExtractLabelsCompiler

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 1499-1528 and 1563-1585: the data-to-word stubs lie
above the store-constants stub, the word-language programs of the staged
pipeline have distinct names above it and well-formed labels, and the
lab-language code is `labels_ok`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.Backend Flapjack.Compiler.Backend.BackendDefs
open Flapjack.Compiler.Backend.BackendCommon

/-- Exact HOL `data_to_word_stubs_above_store_consts_stub`
(`backendProofScript.sml:1499-1503`). `EVERY` over `MAP FST` is a membership
forall over the stub keys; `dc` and the word width are free. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "data_to_word_stubs_above_store_consts_stub" (words_as_type_indexed_bitvec)]
theorem dataToWord_stubsAboveStoreConstsStub {width : Nat} [NeZero width]
    (dc : DataToWord.Config) :
    ∀ n ∈ (DataToWord.stubs dc : List (Nat × Nat × WordLangProgHOL (BitVec width))).map Prod.fst,
      n > storeConstsStubLocation := by
  rw [DataToWord.Proofs.stubsFst_eq]
  have : ∀ n ∈ DataToWord.Proofs.stubsFst, n > 6 := by decide
  exact this

/-- Exact HOL `to_word_labels_ok` (`backendProofScript.sml:1505-1528`). HOL's
free `asm_conf`, `c`, `prog`, `b`, `bm` and `c'` are explicit parameters; the
`let (_, p, _)` pattern binds the programs of `to_word`, `EVERY` is a
membership forall, `ALL_DISTINCT` is `List.Nodup` and `extract_labels` is the
reviewed `extractLabels`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "to_word_labels_ok"
  (words_as_type_indexed_bitvec)]
theorem toWord_labelsOk {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec)
    (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ backendConfigOk asmConf c →
      let (_, p, _) := toWord asmConf c prog
      (p.map Prod.fst).Nodup ∧ (∀ n ∈ p.map Prod.fst, n > storeConstsStubLocation) ∧
        ∀ e ∈ p,
          let labs := extractLabels e.2.2
          (∀ q ∈ labs, q.1 = e.1 ∧ q.2 ≠ 0 ∧ q.2 ≠ 1) ∧ labs.Nodup := by
  intro h
  have hdata := toData_labelsOk asmConf c prog b bm c' h
  rcases hd : toData c prog with ⟨c1, p1, names⟩
  rw [hd] at hdata
  obtain ⟨habove, hdist⟩ := hdata
  have hlab := DataToWord.Proofs.dataToWord_compileLabPres (width := width) c1.dataConf
    c1.wordToWordConf asmConf p1
  simp only [toWord, hd]
  rcases hc : DataToWord.compile c1.dataConf c1.wordToWordConf asmConf p1 with ⟨col, p⟩
  rw [hc] at hlab
  obtain ⟨hfst, hlabs⟩ := hlab
  rw [DataToWord.Proofs.stubsFst_eq] at hfst
  have hstubs : ∀ n ∈ DataToWord.Proofs.stubsFst, n < dataNumStubs ∧ n > 6 := by decide
  have hnum : dataNumStubs = 62 := rfl
  have hsc : storeConstsStubLocation = 6 := rfl
  refine ⟨?_, ?_, hlabs⟩
  · rw [hfst]
    refine List.nodup_append.2 ⟨by decide, hdist, fun x hx y hy hxy => ?_⟩
    have := (hstubs x hx).1
    have := habove y hy
    omega
  · intro n hn
    rw [hfst] at hn
    rcases List.mem_append.1 hn with hn | hn
    · have := (hstubs n hn).2; omega
    · have := habove n hn; omega

/-- Exact HOL `to_lab_labels_ok` (`backendProofScript.sml:1563-1585`). HOL's
free `asm_conf`, `c`, `prog`, `b`, `bm` and `c'` are explicit parameters;
`FST (SND (SND x))` is `x.2.2.1` and `stack_to_labProof$labels_ok` is the
reviewed `labelsOk`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "to_lab_labels_ok"
  (words_as_type_indexed_bitvec)]
theorem toLab_labelsOk {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec)
    (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ backendConfigOk asmConf c →
      StackToLab.Proofs.CodeInstalled.labelsOk (toLab asmConf c prog).2.2.1 := by
  intro h
  have hperf : c.stackConf.perfCalls = false := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hword := toWord_labelsOk asmConf c prog b bm c' h
  rcases hw : toWord asmConf c prog with ⟨cw, pw, names⟩
  rw [hw] at hword
  obtain ⟨hdist, habove, hlabs⟩ := hword
  have hperf' : cw.stackConf.perfCalls = false := by
    rw [← toWord_perfCalls asmConf c cw prog pw names hw, hperf]
  have hstack := WordToStack.Native.ExtractLabelsCompiler.wordToStackCompileLabPres asmConf pw
    hlabs
  simp only [toLab, toStack, hw, hperf']
  apply StackToLab.Proofs.CompileLabPres.stackToLabCompileLabPres
  obtain ⟨hkeys, hslabs⟩ := hstack
  have hsc : storeConstsStubLocation = 6 := rfl
  have hrs : raiseStubLocation = 5 := rfl
  have hgc : StackLang.gcStubLocation = 4 := rfl
  refine ⟨?_, hslabs, ?_⟩
  · rw [hkeys]
    intro n hn
    simp only [List.mem_cons] at hn
    rcases hn with rfl | rfl | hn
    · simp only [hrs, hgc]; omega
    · simp only [hsc, hgc]; omega
    · have := habove n hn; simp only [hsc] at this; simp only [hgc]; omega
  · rw [hkeys]
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, hdist⟩⟩
    · intro hm
      simp only [List.mem_cons] at hm
      rcases hm with hm | hm
      · simp [hrs, hsc] at hm
      · have := habove _ hm; simp only [hsc, hrs] at this; omega
    · intro hm; have := habove _ hm; simp only [hsc] at this; omega

end Flapjack.Compiler.Backend.BackendProof
