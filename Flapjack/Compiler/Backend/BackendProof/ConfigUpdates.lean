module

public import Flapjack.Compiler.Backend.Backend.SetOracle
public import Flapjack.Compiler.Backend.BackendProof.ConfigOk
public import Flapjack.Compiler.Backend.BackendProof.MachineInit

@[expose] public section

/-! backendProofScript.sml 90-168: `backend_config_ok` and `mc_init_ok` are
insensitive to the configuration fields that the incremental compiler and the
oracle installer change. HOL's `cc with f_conf updated_by g` is the Lean record
update `{ cc with fConf := g cc.fConf }`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.Backend

/-- Exact HOL `backend_config_ok_with_bvl_conf_updated`
(`backendProofScript.sml:90-95`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "backend_config_ok_with_bvl_conf_updated" (words_as_type_indexed_bitvec)]
theorem backendConfigOk_withBvlConfUpdated {width : Nat} [NeZero width]
    (f : BvlToBvi.Config → BvlToBvi.Config)
    (cc : Flapjack.Compiler.Backend.Backend.Config)
    (asmConf : AsmConfigExact width) :
    (f cc.bvlConf).nextName2 = cc.bvlConf.nextName2 →
      (backendConfigOk asmConf { cc with bvlConf := f cc.bvlConf } ↔
        backendConfigOk asmConf cc) := by
  intro h
  simp only [backendConfigOk, h]

/-- Exact HOL `backend_config_ok_with_word_to_word_conf_updated`
(`backendProofScript.sml:97-101`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "backend_config_ok_with_word_to_word_conf_updated" (words_as_type_indexed_bitvec)]
theorem backendConfigOk_withWordToWordConfUpdated {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width) (cc : Flapjack.Compiler.Backend.Backend.Config)
    (f : WordToWord.Config → WordToWord.Config) :
    backendConfigOk asmConf { cc with wordToWordConf := f cc.wordToWordConf } ↔
      backendConfigOk asmConf cc := Iff.rfl

/-- Exact HOL `backend_config_ok_call_empty_ffi` (`backendProofScript.sml:103-111`):
`conf_ok` and `max_heap_limit` do not read `call_empty_ffi`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "backend_config_ok_call_empty_ffi" (words_as_type_indexed_bitvec)]
theorem backendConfigOk_callEmptyFfi {width : Nat} [NeZero width]
    (asmConf : AsmConfigExact width)
    (cc : Flapjack.Compiler.Backend.Backend.Config)
    (x : Bool → Bool) :
    backendConfigOk asmConf
        { cc with dataConf := { cc.dataConf with callEmptyFfi := x cc.dataConf.callEmptyFfi } } ↔
      backendConfigOk asmConf cc := Iff.rfl

/-- Exact HOL `mc_init_ok_with_bvl_conf_updated` (`backendProofScript.sml:132-137`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "mc_init_ok_with_bvl_conf_updated" (words_as_type_indexed_bitvec)]
theorem mcInitOk_withBvlConfUpdated {width : Nat} [NeZero width] {β γ : Type}
    (asmConf : AsmConfigExact width)
    (cc : Flapjack.Compiler.Backend.Backend.Config)
    (f : BvlToBvi.Config → BvlToBvi.Config)
    (mc : MachineConfig width β γ) :
    mcInitOk asmConf { cc with bvlConf := f cc.bvlConf } mc ↔ mcInitOk asmConf cc mc :=
  Iff.rfl

/-- Exact HOL `mc_init_ok_with_word_to_word_conf_updated`
(`backendProofScript.sml:139-144`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "mc_init_ok_with_word_to_word_conf_updated" (words_as_type_indexed_bitvec)]
theorem mcInitOk_withWordToWordConfUpdated {width : Nat} [NeZero width] {β γ : Type}
    (asmConf : AsmConfigExact width)
    (cc : Flapjack.Compiler.Backend.Backend.Config)
    (f : WordToWord.Config → WordToWord.Config)
    (mc : MachineConfig width β γ) :
    mcInitOk asmConf { cc with wordToWordConf := f cc.wordToWordConf } mc ↔
      mcInitOk asmConf cc mc :=
  Iff.rfl

/-- Exact HOL `mc_init_ok_with_clos_conf_updated` (`backendProofScript.sml:146-151`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml"
  "mc_init_ok_with_clos_conf_updated" (words_as_type_indexed_bitvec)]
theorem mcInitOk_withClosConfUpdated {width : Nat} [NeZero width] {β γ : Type}
    (asmConf : AsmConfigExact width)
    (cc : Flapjack.Compiler.Backend.Backend.Config)
    (f : ClosToBvl.Config → ClosToBvl.Config)
    (mc : MachineConfig width β γ) :
    mcInitOk asmConf { cc with closConf := f cc.closConf } mc ↔ mcInitOk asmConf cc mc :=
  Iff.rfl

/-- Exact HOL `set_oracle_simp` (`backendProofScript.sml:153-159`). The middle
conjunct is HOL's equality of the partially applied `mc_init_ok`, at the
captured machine-configuration type `(α, β, γ) machine_config`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "set_oracle_simp"
  (words_as_type_indexed_bitvec)]
theorem setOracle_simp {width : Nat} [NeZero width] {β γ : Type}
    (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config)
    (x : List (Option (Flapjack.Spt Nat))) :
    (backendConfigOk asmConf (setOracle c x) ↔ backendConfigOk asmConf c) ∧
    (mcInitOk (state := β) (projection := γ) asmConf (setOracle c x) =
      mcInitOk (state := β) (projection := γ) asmConf c) ∧
    (setOracle c x).stackConf = c.stackConf :=
  ⟨Iff.rfl, rfl, rfl⟩

/-- Exact HOL `mc_init_ok_call_empty_ffi` (`backendProofScript.sml:161-168`), an
equality of the partially applied `mc_init_ok` at the captured
`(α, β, γ) machine_config` type. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "mc_init_ok_call_empty_ffi"
  (words_as_type_indexed_bitvec)]
theorem mcInitOk_callEmptyFfi {width : Nat} [NeZero width] {β γ : Type}
    (asmConf : AsmConfigExact width)
    (cc : Flapjack.Compiler.Backend.Backend.Config)
    (x : Bool → Bool) :
    mcInitOk (state := β) (projection := γ) asmConf
        { cc with dataConf := { cc.dataConf with callEmptyFfi := x cc.dataConf.callEmptyFfi } } =
      mcInitOk (state := β) (projection := γ) asmConf cc :=
  rfl

end Flapjack.Compiler.Backend.BackendProof
