import Flapjack.Compiler.Backend.Backend.IncProgs
import Flapjack.Compiler.Backend.BackendProps.Pure
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CommonCompiler
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.FullOracle
import Flapjack.Compiler.Backend.ClosToBvl.SourceInc
import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.StackAlloc.Compile
import Flapjack.Compiler.Backend.StackRemove.ProgComp
import Flapjack.Compiler.Backend.StackToLab.Native
import Flapjack.Compiler.Backend.StackToLab.Compile
import Flapjack.Compiler.Backend.BackendProof.CakeOracConfig
import Flapjack.Compiler.Backend.BackendProof.StateOracle
import Flapjack.Compiler.Backend.BackendProof.ConfigTuple
import Flapjack.Compiler.Backend.Backend.PrimSrcConfig

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

/-- `compile_common_inc` only reads the static closure fields (Flapjack helper). -/
private theorem compileCommonInc_congr {C : Type} (c1 c2 : ClosToBvl.Config) (cc : ClosSem.Compiler C)
    (hm : c1.doMti = c2.doMti) (ha : c1.maxApp = c2.maxApp) (hd : c1.doCall = c2.doCall)
    (hk : ClosKnown.knownStaticConf c1.knownConf = ClosKnown.knownStaticConf c2.knownConf) :
    ClosToBvl.compileCommonInc c1 cc = ClosToBvl.compileCommonInc c2 cc := by
  unfold ClosToBvl.compileCommonInc
  rw [knownCc_eq_stateCc_inc, knownCc_eq_stateCc_inc, hm, ha, hd, hk]

/-- `full_cc` only reads the static BVL-to-BVI fields (Flapjack helper). -/
private theorem fullCc_congr {C Code Data CNext : Type} (b1 b2 : BvlToBvi.Config)
    (cc : C → List (Nat × Nat × Bvi.Exp) → Option (Code × Data × CNext))
    (h1 : b1.inlineSizeLimit = b2.inlineSizeLimit) (h2 : b1.splitMainAtSeq = b2.splitMainAtSeq)
    (h3 : b1.expCut = b2.expCut) (h4 : b1.doTailrec = b2.doTailrec) (h5 : b1.doTmc = b2.doTmc) :
    BvlToBvi.Proofs.fullCc b1 cc = BvlToBvi.Proofs.fullCc b2 cc := by
  unfold BvlToBvi.Proofs.fullCc
  rw [h1, h2, h3, h4, h5]

/-- `backend_from_data_tuple_cc` only reads the data, register-allocation and
stack fields of the configuration (Flapjack helper). -/
private theorem backendFromDataTupleCc_congr {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c1 c2 : Flapjack.Compiler.Backend.Backend.Config)
    (hd : c1.dataConf = c2.dataConf) (hr : c1.wordToWordConf.regAlg = c2.wordToWordConf.regAlg)
    (hs : c1.stackConf = c2.stackConf) :
    backendFromDataTupleCc asmConf c1 = backendFromDataTupleCc asmConf c2 := by
  funext cfg
  unfold backendFromDataTupleCc
  rw [hd, hr, hs]

/-- `backend_from_flat_tuple_cc` only reads the static configuration fields
compared by `cake_orac_config_inv_f` (Flapjack helper). -/
private theorem backendFromFlatTupleCc_congr {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c1 c2 : Flapjack.Compiler.Backend.Backend.Config)
    (h : cakeOracConfigInvF asmConf c1 = cakeOracConfigInvF asmConf c2) :
    backendFromFlatTupleCc asmConf c1 = backendFromFlatTupleCc asmConf c2 := by
  simp only [cakeOracConfigInvF, Function.comp_apply, Prod.mk.injEq] at h
  obtain ⟨-, ha, hd, -, hk, hm, b1, b2, b3, b4, b5, hdc, hr, hs, -⟩ := h
  unfold backendFromFlatTupleCc
  rw [compileCommonInc_congr c1.closConf c2.closConf _ hm ha hd hk, ha,
    fullCc_congr c1.bvlConf c2.bvlConf _ b1 b2 b3 b4 b5,
    backendFromDataTupleCc_congr asmConf c1 c2 hdc hr hs]

/-- Exact HOL `backend_from_flat_tuple_cc_eq_compile_inc_progs`
(`backendProofScript.sml:2992-3031`). The spliced `^cake_orac_config_inv_f`
is the untagged `cakeOracConfigInvF` notation; `(perf_calls ⇔ F)` is
`= false`; `flat_pattern$compile_dec` is `FlatPattern.compileDec`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "backend_from_flat_tuple_cc_eq_compile_inc_progs" (words_as_type_indexed_bitvec)]
theorem backendFromFlatTupleCc_eq_compileIncProgs {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (c c' : Flapjack.Compiler.Backend.Backend.Config)
    (srcCfg : SourceToFlat.Config) (envId : Nat × Nat) (decs : List AstHOL.Dec) :
    cakeOracConfigInvF asmConf c' = cakeOracConfigInvF asmConf c ∧ srcCfg = c'.sourceConf ∧
        c.stackConf.perfCalls = false ∧ c.sourceConf.patternCfg = primSrcConfig.patternCfg →
      backendFromFlatTupleCc asmConf c (configTuple1 c').2
          ((SourceToFlat.incCompileProg envId srcCfg (SourceToSource.compile decs)).2.map
            (FlatPattern.compileDec primSrcConfig.patternCfg)) =
        (let (c'', ps) := compileIncProgs true asmConf c' (envId, decs)
         ps.targetProg.map fun (x : List (BitVec 8) × List (BitVec width)) =>
           (x.1, x.2.map upperW2w, (configTuple1 c'').2)) := by
  rintro ⟨hinv, rfl, hperf, hpat⟩
  rw [backendFromFlatTupleCc_congr asmConf c c' hinv.symm]
  have hinv' := hinv
  simp only [cakeOracConfigInvF, Function.comp_apply, Prod.mk.injEq] at hinv'
  obtain ⟨hp, -, -, hsome, hk, -, -, -, -, -, -, -, -, hs, -⟩ := hinv'
  rw [← hs] at hperf
  rw [← hp] at hpat
  simp only [backendFromFlatTupleCc, pureCc, ClosToBvl.compileCommonInc, knownCc_eq_stateCc_inc,
    BvlToBvi.Proofs.fullCc, compileIncProgs,
    ClosToBvl.closToBvlCompileInc, BvlToBvi.bvlToBviCompileIncAll, SourceToFlat.incCompile,
    configTuple1, configTuple2, StackToLab.compileNoStubs, hperf]
  have hpc : (SourceToFlat.incCompileProg envId c'.sourceConf
      (SourceToSource.compile decs)).1.patternCfg = primSrcConfig.patternCfg :=
    ((sourceCompile_patternCfg c'.sourceConf (SourceToSource.compile decs)
      (SourceToFlat.incCompile envId c'.sourceConf (SourceToSource.compile decs)).1
      (SourceToFlat.incCompile envId c'.sourceConf (SourceToSource.compile decs)).2 envId).2
      rfl).trans hpat
  rw [hpc]
  generalize ClosMti.condCompileInc c'.closConf.doMti c'.closConf.maxApp
    (FlatToClos.incCompileDecs (List.map (FlatPattern.compileDec primSrcConfig.patternCfg)
      (SourceToFlat.incCompileProg envId c'.sourceConf (SourceToSource.compile decs)).2)) = P1
  simp only [stateCc, pureCc]
  generalize ClosNumber.ignoreTable ClosNumber.compileInc c'.closConf.nextLoc P1 = N
  have hret : ClosKnown.optionValApproxSpt (ClosKnown.optionUpdValSpt
      (ClosKnown.knownCompileIncSource (ClosKnown.knownStaticConf c'.closConf.knownConf)
        (ClosKnown.optionValApproxSpt c'.closConf.knownConf) N.2).1 c'.closConf.knownConf) =
      (ClosKnown.knownCompileIncSource (ClosKnown.knownStaticConf c'.closConf.knownConf)
        (ClosKnown.optionValApproxSpt c'.closConf.knownConf) N.2).1 :=
    knownCompileInc_retreiveSpt _ _ _ _ _ ⟨rfl, rfl⟩
  rw [hret]
  generalize ClosKnown.knownCompileIncSource (ClosKnown.knownStaticConf c'.closConf.knownConf)
    (ClosKnown.optionValApproxSpt c'.closConf.knownConf) N.2 = K
  generalize ClosCall.condCallCompileInc c'.closConf.doCall c'.closConf.callState.1 K.2 = L
  generalize ClosToBvl.compileInc c'.closConf.maxApp (ClosAnnotate.compileIncSource L.2) = M
  generalize BvlInline.compileInc c'.bvlConf.inlineSizeLimit c'.bvlConf.splitMainAtSeq
    c'.bvlConf.expCut c'.bvlConf.inlines M = I1
  generalize BvlToBvi.compileIncSource c'.bvlConf.nextName1 I1.2 = I2
  generalize BviTailrec.compileProgSource c'.bvlConf.doTailrec c'.bvlConf.nextName2 I2.2 = I3
  generalize BviTmc.compileProgSource c'.bvlConf.doTmc c'.bvlConf.nextName3 I3.2 = I4
  generalize BviInline.compileIncSource c'.bvlConf.bviInlines I4.2 = I5
  generalize BviToData.compileProg I5.2 = D
  unfold backendFromDataTupleCc
  have r1 : asmConf.regCount - (3 + asmConf.avoidRegs.length) - 2 =
      asmConf.regCount - (5 + asmConf.avoidRegs.length) := by omega
  have r2 : asmConf.avoidRegs.length + 5 = 5 + asmConf.avoidRegs.length := Nat.add_comm _ _
  have r3 : asmConf.avoidRegs.length + 3 = 3 + asmConf.avoidRegs.length := Nat.add_comm _ _
  simp only [Function.comp_apply, r2, r3, StackNames.compileHOL, List.map_map]
  simp only [r1]
  generalize WordToStack.Native.compileWordToStackNative asmConf false
    (asmConf.regCount - (5 + asmConf.avoidRegs.length))
    (List.map ((fun p => WordToWord.fullCompileSingle asmConf.twoRegArith
      (asmConf.regCount - (5 + asmConf.avoidRegs.length)) c'.wordToWordConf.regAlg asmConf (p, none)) ∘
      DataToWord.compilePart (ensureFpConfOk asmConf c'.dataConf)) D)
    (AppList.nil, c'.wordConf.bitmapsLength) = W
  generalize LabToTarget.compile asmConf c'.labConf
    (List.map (StackToLab.progToSectionHOL ∘ StackNames.progCompEntryHOL c'.stackConf.regNames ∘
      StackRemove.progComp c'.stackConf.jump asmConf.addrOffset
        (asmConf.regCount - (3 + asmConf.avoidRegs.length)) ∘ StackAlloc.progComp) W.1) = T
  cases T <;> simp

end Flapjack.Compiler.Backend.BackendProof
