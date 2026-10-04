import Flapjack.Pancake.Proofs.PanToTarget.CompileSemanticsStatement
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTopResource
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMachineToLab
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyLabToTarget
import Flapjack.Pancake.Proofs.PanToWord.CompileProgInstOkLess

/-!
# `pan_to_target_compile_semantics`: final assembly

The complete proof of the statement interface `PanToTargetCompileSemanticsStatement`
(`pan_to_targetProofScript.sml:1257-2506`): `compile_prog_max` and `pan_installed`
are unfolded into the stage inputs; `pan_to_word_every_inst_ok_less` supplies the
instruction validity, the machine-to-lab stage (`lab_to_target` `semantics_compile`)
relates the machine semantics to the lab semantics of the initial lab state, and the
lab-state chain with the resource-limit stage concludes.

Untagged: `PanToTargetCompileSemanticsStatement` is the untagged statement interface
(see its docstring for the recorded `pan_installed` memory-domain carrier gap); the
tag decision for the final theorem belongs to its statement review.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL

open Classical in
/-- `pan_to_target_compile_semantics` over the reviewed carriers: the hypotheses and
conclusion of `PanToTargetCompileSemanticsStatement` hold for every input. -/
theorem panToTargetCompileSemantics {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (pan_code : List (DeclHOL width))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec width)) (c' : Backend.Config)
    (stack_max : Option Nat) (s : PanSemStateFiniteExact width σ) (ffi : HolFfiState σ)
    (ms : S) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec width)
    (cbspace data_sp : Nat) (start : MlS) :
    PanToTargetCompileSemanticsStatement c mc pan_code bytes bitmaps c' stack_max s ffi ms
      globals_size heap_len adj_ptr2 adj_ptr4 cbspace data_sp start := by
  rintro ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hcfg, hmc,
    hinit, hisa, -, hsize, hlt, hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign,
    rfl, rfl, hlo, hhi, hheap, hheapLt, hffi, hbe, hffiOk, hinst, hstart, hfail⟩ b hb
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab, rfl, hmax⟩ :=
    compileProgMax_some c mc pan_code bytes bitmaps _ stack_max hcomp
  obtain ⟨t, m, bitmapPtr, bitmapsDm, sdm, hpm, hgi, hsdm, a1, a2, a3, hle, hbig, hdisj, m0, m1,
    m2, m3, m4, hstar, hffiN, hmmio⟩ := hinst
  -- `pan_to_word_every_inst_ok_less` (stage .20), from `pancake_good_code`
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hao, -, hbo, -⟩ := id hcfg
  have hz := good_dimindex_0w_8w hmc.1
  have hevery := PanToWord.panToWordEveryInstOkLess mc.target.config pan_code _ rfl
    (hbo 0 ⟨hz.2, hz.1⟩) hao hgood
  -- the machine-to-lab stage (`lab_to_target` `semantics_compile`)
  have hA4 := panToTargetMachineLab c mc ffi t m bitmapsDm sdm ms bytes cbspace pan_code col
    wprog bitmaps wconf fs p ltconf hcfg hmc hisa hwtw hwts hlab hnodup hffiOk hgi hffiN hmmio
    hevery
  -- the lab-state chain with the resource-limit stage
  have hres := panToTargetLabSemanticsResource (C := LabToTarget.Config) c mc ffi t m bitmapPtr
    bitmapsDm sdm ms (LabToTarget.compile mc.target.config) bytes cbspace ltconf pan_code col wprog
    bitmaps wconf fs p data_sp s start globals_size heap_len stack_max hcfg hmc hinit hisa hwtw
    hwts hmax hnodup (fun a h => hpm a (of_decide_eq_true h)) hgi
    (by funext a; rw [hsdm]; simp only [Bool.decide_and, Bool.decide_eq_true]) ⟨a1, a2, a3, hle, hbig, hdisj, m0, m1, m2, m3, m4, hstar⟩ hbase
    hlt hlo hhi hheap hheapLt halign hbe hffi hheapLen hglobLe hmemaddrs htop hstart hsize hparams
    halloc hcode hglobals hlocals heids heshapes hfail
  have hlabne := extendPrime_singleton_ne_fail _ _ _ hres hfail
  have hb' := hA4 (fun h => hlabne h.symm) b hb
  simp only [extendWithResourceLimitPrimeHOL, if_true] at hb'
  rw [hb']
  exact hres

end Flapjack.Pancake.Proofs.PanToTarget
