import Flapjack.Pancake.Proofs.PanToTarget.LabelsChain
import Flapjack.Pancake.Proofs.PanToTarget.InitHelpers
import Flapjack.Compiler.Backend.BackendProof.ConfigOk
import Flapjack.Compiler.Backend.Proofs.WordConventions
import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmConventions
import Flapjack.Compiler.Backend.StackRawCall.Proofs.AsmNames
import Flapjack.Compiler.Backend.StackAlloc.Proofs.Conventions
import Flapjack.Compiler.Backend.StackRemove.Proofs.AsmName
import Flapjack.Compiler.Backend.StackNames.AsmAdmissibility.Assembly
import Flapjack.Compiler.Backend.StackToLab.Proofs.Encoding.Full

/-!
# `pan_to_target_compile_semantics` assembly, stage A2 (`good_code`)

Intermediate step of the single HOL proof of `pan_to_target_compile_semantics`
(`pan_to_targetProofScript.sml:1376-1428`): `good_code mc.target.config LN lprog` for
the lab program of `compile_prog_max`, via `pan_to_lab_good_code_lemma`,
`pan_to_lab_labels_ok` and the `all_enc_ok_pre` chain through every backend pass.
Not a HOL theorem, so untagged.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.BackendProof Flapjack.Pancake.PanLang

/-- The two spellings of `wordConvs$two_reg_inst` agree (Flapjack infrastructure:
`twoRegInst` is over `wordLang` instructions, `twoRegInstExact` over the exact
`asm` instruction carrier). -/
theorem twoRegInst_eq_exact {width : Nat} [NeZero width] (i : WordLangInst (BitVec width)) :
    twoRegInst i = twoRegInstExact (HolInst.ofWordLangInst i) := by
  rcases i with _ | _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _⟩ | _ | _ <;> rfl

/-- Stage A2 of the HOL proof (lines 1376-1428): the lab program that
`compile_prog_max` hands to `lab_to_target$compile` satisfies
`good_code mc.target.config LN`.  `col`/`wprog`/`wconf`/`p` are the
`word_to_word`/`word_to_stack` results of `compile_prog_max`; `hinst` is the
conclusion of `pan_to_word_every_inst_ok_less` (stage .20), the remaining premises
are the top theorem's own. -/
theorem panToTargetGoodCode {width : Nat} [NeZero width] {S Q β : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat))) (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × StackLang.HolProg width))
    (hcfg : backendConfigOk mc.target.config c) (hgood : goodDimindex width)
    (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (hinst : ∀ q ∈ panToWordCompileProgHOL mc.target.config.isa panCode,
      everyInst (fun i => instOkLessExact mc.target.config (HolInst.ofWordLangInst i)) q.2.2 =
        true) :
    LabToTarget.goodCode mc.target.config (.ln : Spt (Spt β))
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset p) := by
  obtain ⟨-, -, -, hregs, -, -, hconf, -, -, -, -, hao, hho, hbo, h8, h4, h1, hs1, -, -,
    hnames, hfixed, hstore, -, himm⟩ := hcfg
  have ⟨hz8, hm8z⟩ := good_dimindex_0w_8w hgood
  have hbyte : asmByteOffsetOkExact mc.target.config 0 = true := hbo 0 ⟨hm8z, hz8⟩
  obtain ⟨-, -, hrows⟩ := compileToWordConventions2
    c.wordToWordConf mc.target.config _ col wprog hwtw (fun _ _ => Or.inr hisa)
  have hconvs := WordToStackProofs.AsmConventions.wordToStackStackAsmConvs mc.target.config wprog
    (fun row hr => by
      obtain ⟨-, hpost, hfull, htwo, hns⟩ := hrows row hr
      refine ⟨hfull ⟨hinst, hao, hho, hbyte⟩, fun h => ?_, hns, ?_⟩
      · rw [← htwo h]
        congr 1
        funext i
        exact (twoRegInst_eq_exact i).symm
      · rwa [Nat.add_comm mc.target.config.avoidRegs.length 5])
    (by omega)
  rw [hwts] at hconvs
  have hp : (∀ np ∈ p, StackProps.stackAsmName mc.target.config np.2) ∧
      (∀ np ∈ p, StackProps.stackAsmRemove mc.target.config np.2) :=
    ⟨fun np h => (hconvs np h).1, fun np h => (hconvs np h).2⟩
  have hraw := StackRawCall.stackAllocStackAsmConvs (c := mc.target.config) (prog := p)
  rw [← hraw.1, ← hraw.2] at hp
  have halloc := StackAlloc.stack_alloc_stack_asm_convs
    ⟨hp.1, hp.2, hconf, hao, by simp [StackProps.regName]; omega, hgood, h8, h4, h1, hs1⟩
  have hremove := StackRemove.Proofs.AsmName.stackRemoveStackAsmName
    (jump := c.stackConf.jump) (genGc := StackToLab.isGenGc c.dataConf.gcKind)
    (maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    (k := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
    (start := BvlToBvi.initGlobalsLocation)
    ⟨halloc.1, halloc.2, hao, hgood, himm, h4, h8, hstore,
      by simp [StackProps.regName]; omega, by simp [StackProps.regName]; omega,
      by simp [StackProps.regName]; omega, by simp [StackProps.regName]; omega, by omega⟩
  have hok := StackNames.stackNamesStackAsmOk mc.target.config
    c.stackConf.regNames _ ⟨hremove, hnames, hfixed⟩
  have henc := StackToLab.Proofs.compileAllEncOkPreHOL mc.target.config _ hbyte hok
  have hlabels := pan_to_lab_labels_ok mc panCode _ c col wprog bitmaps wconf fs p
    (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)) _
    ⟨rfl, hwtw, hisa, hwts, rfl, hnodup⟩
  exact pan_to_lab_good_code_lemma c _ _ mc.target.config.addrOffset p _ mc.target.config wprog
    bitmaps wconf fs c.wordToWordConf _ col panCode mc.target.config
    ⟨rfl, hwts, hwtw, rfl, hlabels, henc⟩

end Flapjack.Pancake.Proofs.PanToTarget
