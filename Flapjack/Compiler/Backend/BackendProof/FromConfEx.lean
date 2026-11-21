module

public import Flapjack.Compiler.Backend.Backend.FromSource

@[expose] public section

/-! backendProofScript.sml 630-692: each stage of the staged backend pipeline
`from_clos` ... `from_lab` is the next stage applied to some program and to
the configuration updated only in the stage's own fields. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.Backend Flapjack.Compiler.Backend.BackendDefs

/-- Exact HOL `from_clos_conf_EX` (`backendProofScript.sml:630-637`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "from_clos_conf_EX"
  (words_as_type_indexed_bitvec)]
theorem fromClos_confEx {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (p : List ClosLang.Exp)
    (v : Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config)) :
    fromClos asmConf c p = v →
      ∃ (cc : ClosToBvl.Config) (names : Spt MlString) (p : List (Nat × Nat × Bvl.Exp)),
        fromBvl asmConf { c with closConf := cc } names p = v := by
  intro h
  rcases hc : ClosToBvl.compileSource c.closConf p with ⟨cc, q, names⟩
  simp only [fromClos, hc] at h
  exact ⟨cc, names, q, h⟩

/-- Exact HOL `from_bvl_conf_EX` (`backendProofScript.sml:639-648`). HOL's
`c with <|bvl_conf updated_by bvlcu; clos_conf updated_by (λc. c with start := st)|>`
is the record update of both fields. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "from_bvl_conf_EX"
  (words_as_type_indexed_bitvec)]
theorem fromBvl_confEx {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (p : List (Nat × Nat × Bvl.Exp))
    (v : Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config)) :
    fromBvl asmConf c names p = v →
      ∃ (st : Nat) (bvlcu : BvlToBvi.Config → BvlToBvi.Config) (names : Spt MlString)
        (p : List (Nat × Nat × Bvi.Exp)),
        fromBvi asmConf { c with
          bvlConf := bvlcu c.bvlConf
          closConf := { c.closConf with start := st } } names p = v := by
  intro h
  rcases hc : BvlToBvi.compileSource c.closConf.start c.bvlConf names p with
    ⟨s, q, l, bl, n1, n2, n3, names'⟩
  simp only [fromBvl, hc] at h
  exact ⟨s, fun b => { b with
    inlines := l, bviInlines := bl, nextName1 := n1, nextName2 := n2, nextName3 := n3 }, _, q, h⟩

/-- Exact HOL `from_bvi_conf_EX` (`backendProofScript.sml:650-656`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "from_bvi_conf_EX"
  (words_as_type_indexed_bitvec)]
theorem fromBvi_confEx {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (p : List (Nat × Nat × Bvi.Exp))
    (v : Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config)) :
    fromBvi asmConf c names p = v →
      ∃ p : List (Nat × Nat × DataLang.Prog), fromData asmConf c names p = v :=
  fun h => ⟨_, h⟩

/-- Exact HOL `from_data_conf_EX` (`backendProofScript.sml:658-665`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "from_data_conf_EX"
  (words_as_type_indexed_bitvec)]
theorem fromData_confEx {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (p : List (Nat × Nat × DataLang.Prog))
    (v : Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config)) :
    fromData asmConf c names p = v →
      ∃ (wcu : WordToWord.Config → WordToWord.Config)
        (p : List (Nat × Nat × WordLangProgHOL (BitVec width))),
        fromWord asmConf { c with wordToWordConf := wcu c.wordToWordConf } names p = v := by
  intro h
  rcases hc : DataToWord.compile c.dataConf c.wordToWordConf asmConf p with ⟨col, q⟩
  simp only [fromData, hc] at h
  exact ⟨fun w => { w with colOracle := col }, q, h⟩

/-- Exact HOL `from_word_conf_EX` (`backendProofScript.sml:667-674`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "from_word_conf_EX"
  (words_as_type_indexed_bitvec)]
theorem fromWord_confEx {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (p : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (v : Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config)) :
    fromWord asmConf c names p = v →
      ∃ (wc : WordToStack.Native.Config) (p : List (Nat × StackLang.HolProg width))
        (bm : List (BitVec width)),
        fromStack asmConf { c with wordConf := wc } names p bm = v := by
  intro h
  rcases hc : WordToStack.Native.compileNative asmConf c.stackConf.perfCalls p with
    ⟨bm, wc, fs, q⟩
  simp only [fromWord, hc] at h
  exact ⟨wc, q, bm, h⟩

/-- Exact HOL `from_stack_conf_EX` (`backendProofScript.sml:676-682`); the
bitmap payload type is independent, as captured. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "from_stack_conf_EX"
  (words_as_type_indexed_bitvec)]
theorem fromStack_confEx {width : Nat} [NeZero width] {α : Type} (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (p : List (Nat × StackLang.HolProg width)) (bm : α)
    (v : Option (List (BitVec 8) × α × Flapjack.Compiler.Backend.Backend.Config)) :
    fromStack asmConf c names p bm = v →
      ∃ p : LabSem.LabProgHOL width, fromLab asmConf c names p bm = v :=
  fun h => ⟨_, h⟩

/-- Exact HOL `from_lab_conf_EX` (`backendProofScript.sml:684-692`). HOL's
`«NOTFOUND»` is `ofString "NOTFOUND"`, as in the reviewed `attachBitmaps`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "from_lab_conf_EX"
  (words_as_type_indexed_bitvec)]
theorem fromLab_confEx {width : Nat} [NeZero width] {α : Type} (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (names : Spt MlString)
    (p : LabSem.LabProgHOL width) (bm : α) (bytes : List (BitVec 8)) (bitmap : α)
    (c' : Flapjack.Compiler.Backend.Backend.Config) :
    fromLab asmConf c names p bm = some (bytes, bitmap, c') →
      ∃ lc : LabToTarget.Config, c' = { c with
        labConf := lc
        symbols := lc.secPosLen.map fun (n, p, l) =>
          (lookupAny n names (ofString "NOTFOUND"), p, l) } := by
  intro h
  simp only [fromLab] at h
  cases hc : LabToTarget.compile asmConf c.labConf p with
  | none => simp [hc, attachBitmaps] at h
  | some r =>
      obtain ⟨b, lc⟩ := r
      simp only [hc, attachBitmaps, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨lc, h.2.2.symm⟩

end Flapjack.Compiler.Backend.BackendProof
