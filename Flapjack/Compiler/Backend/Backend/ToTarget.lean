module

public import Flapjack.Compiler.Backend.Backend.Compile
public import Flapjack.Compiler.Backend.Backend.SourcePipeline

@[expose] public section

/-! backendScript.sml 127-197: the lower stages `to_word_0`, `to_word`,
`to_stack`, `to_lab`, `to_target` of the staged backend pipeline continuing
the reviewed `to_data`, and their equations with `compile`. -/
namespace Flapjack.Compiler.Backend.BackendDefs

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.Backend

/-- Exact HOL `backend$to_word_0_def` (`backendScript.sml:127-132`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_word_0_def"
  (words_as_type_indexed_bitvec)]
noncomputable def toWord0 {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (p : List AstHOL.Dec) :
    Flapjack.Compiler.Backend.Backend.Config ×
      List (Nat × Nat × WordLangProgHOL (BitVec width)) × Spt MlString :=
  let (c, p, names) := toData c p
  let p := DataToWord.compile0 c.dataConf asmConf p
  (c, p, names)

/-- Exact HOL `backend$to_word_def` (`backendScript.sml:134-140`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_word_def"
  (words_as_type_indexed_bitvec)]
noncomputable def toWord {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (p : List AstHOL.Dec) :
    Flapjack.Compiler.Backend.Backend.Config ×
      List (Nat × Nat × WordLangProgHOL (BitVec width)) × Spt MlString :=
  let (c, p, names) := toData c p
  let (col, p) := DataToWord.compile c.dataConf c.wordToWordConf asmConf p
  let c := { c with wordToWordConf := { c.wordToWordConf with colOracle := col } }
  (c, p, names)

/-- Exact HOL `backend$to_word_thm` (`backendScript.sml:142-151`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_word_thm"
  (words_as_type_indexed_bitvec)]
theorem toWord_thm {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (p : List AstHOL.Dec) :
    toWord asmConf c p =
      (let (c, p, names) := toWord0 asmConf c p
       let (col, p) := WordToWord.compile c.wordToWordConf asmConf p
       let c := { c with wordToWordConf := { c.wordToWordConf with colOracle := col } }
       (c, p, names)) := rfl

/-- Exact HOL `backend$to_stack_def` (`backendScript.sml:153-159`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_stack_def"
  (words_as_type_indexed_bitvec)]
noncomputable def toStack {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (p : List AstHOL.Dec) :
    List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config ×
      List (Nat × StackLang.HolProg width) × Spt MlString :=
  let (c, p, names) := toWord asmConf c p
  let (bm, c', _fs, p) := WordToStack.Native.compileNative asmConf c.stackConf.perfCalls p
  let c := { c with wordConf := c' }
  (bm, c, p, names)

/-- Exact HOL `backend$to_lab_def` (`backendScript.sml:161-169`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_lab_def"
  (words_as_type_indexed_bitvec)]
noncomputable def toLab {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (p : List AstHOL.Dec) :
    List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config ×
      LabSem.LabProgHOL width × Spt MlString :=
  let (bm, c, p, names) := toStack asmConf c p
  let p := StackToLab.compile c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    (asmConf.regCount - (asmConf.avoidRegs.length + 3)) asmConf.addrOffset p
  (bm, c, p, names)

/-- Exact HOL `backend$to_target_def` (`backendScript.sml:171-177`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "to_target_def"
  (words_as_type_indexed_bitvec)]
noncomputable def toTarget {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (p : List AstHOL.Dec) :
    Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config) :=
  let (bm, c, p, names) := toLab asmConf c p
  attachBitmaps names c bm (LabToTarget.compile asmConf c.labConf p)

/-- Exact HOL `backend$compile_eq_to_target` (`backendScript.sml:179-197`). -/
@[hol "cakeml/compiler/backend/backendScript.sml" "compile_eq_to_target"
  (words_as_type_indexed_bitvec)]
theorem compile_eq_toTarget {width : Nat} [NeZero width] :
    (compile : AsmConfigExact width → Flapjack.Compiler.Backend.Backend.Config →
        List AstHOL.Dec →
        Option (List (BitVec 8) × List (BitVec width) × Flapjack.Compiler.Backend.Backend.Config)) =
      toTarget := by
  funext asmConf c p
  rfl

end Flapjack.Compiler.Backend.BackendDefs
