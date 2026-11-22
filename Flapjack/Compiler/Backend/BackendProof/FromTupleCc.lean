import Flapjack.Compiler.Backend.Backend.IncProgs
import Flapjack.Compiler.Backend.BackendProps.Pure
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CommonCompiler
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.FullOracle
import Flapjack.Compiler.Backend.ClosToBvl.SourceInc
import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.StackAlloc.Compile
import Flapjack.Compiler.Backend.StackRemove.ProgComp
import Flapjack.Compiler.Backend.StackToLab.Native

set_option autoImplicit false

/-! backendProofScript.sml 2930-2963 (a non-`module` file because the
reviewed `compile_common_inc` and closure-to-BVL semantics are): the incremental compiler callbacks
installed at the data and flat levels of the top-level correctness proof. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.BackendDefs
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.Backend

/-- Exact HOL `backend_from_data_tuple_cc_def` (`backendProofScript.sml:2930-2954`),
term for term. HOL `I ## MAP upper_w2w ## I` is `Prod.map id (Prod.map
(List.map upperW2w) id)`, `OPTION_MAP` is `Option.map`, the paired lambdas are
pattern-matching lambdas, `MAP (prog_comp c.stack_conf.reg_names)` uses the
reviewed `stack_names$prog_comp` (`progCompEntryHOL`), and
`compile asm_conf cfg` is `lab_to_target$compile`. `'a asm_config` is
`AsmConfigExact width`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "backend_from_data_tuple_cc_def"
  (words_as_type_indexed_bitvec)]
noncomputable def backendFromDataTupleCc {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (cfg : Nat × LabToTarget.Config) :
    List (Nat × Nat × DataLang.Prog) →
      Option (List (BitVec 8) × List (BitVec 64) × Nat × LabToTarget.Config) :=
  Option.map (Prod.map id (Prod.map (List.map upperW2w) id)) ∘
    (fun progs : List (Nat × Nat × WordLangProgHOL (BitVec width)) =>
      (fun (bmCfg : Nat × LabToTarget.Config)
          (progs : List (Nat × Nat × WordLangProgHOL (BitVec width))) =>
        let (bm0, cfg) := bmCfg
        (fun (r : List (Nat × StackLang.HolProg width) × List Nat × (AppList (BitVec width) × Nat)) =>
          let (progs, _fs, bm) := r
          Option.map (fun (x : List (BitVec 8) × LabToTarget.Config) =>
              let (bytes, cfg) := x
              (bytes, appListAppend bm.1, bm.2, cfg))
            (LabToTarget.compile asmConf cfg
              ((((progs.map StackAlloc.progComp).map
                (StackRemove.progComp c.stackConf.jump asmConf.addrOffset
                  (asmConf.regCount - (asmConf.avoidRegs.length + 3)))).map
                (StackNames.progCompEntryHOL c.stackConf.regNames)).map
                StackToLab.progToSectionHOL)))
          (WordToStack.Native.compileWordToStackNative asmConf false
            ((asmConf.regCount - (asmConf.avoidRegs.length + 3)) - 2) progs (.nil, bm0)))
        cfg
        (progs.map fun p => WordToWord.fullCompileSingle asmConf.twoRegArith
          (asmConf.regCount - (asmConf.avoidRegs.length + 5))
          c.wordToWordConf.regAlg asmConf (p, none))) ∘
    List.map (DataToWord.compilePart (ensureFpConfOk asmConf c.dataConf))

/-- Exact HOL `backend_from_flat_tuple_cc_def` (`backendProofScript.sml:2956-2963`).
`compile_prog` is `bvi_to_data$compile_prog`; `clos_to_bvl$compile_inc` is
`ClosToBvl.compileInc`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "backend_from_flat_tuple_cc_def"
  (words_as_type_indexed_bitvec)]
noncomputable def backendFromFlatTupleCc {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config) :=
  pureCc FlatToClos.incCompileDecs
    (ClosToBvl.compileCommonInc c.closConf
      (pureCc (ClosToBvl.compileInc c.closConf.maxApp)
        (BvlToBvi.Proofs.fullCc c.bvlConf (pureCc BviToData.compileProg
          (backendFromDataTupleCc asmConf c)))))

end Flapjack.Compiler.Backend.BackendProof
