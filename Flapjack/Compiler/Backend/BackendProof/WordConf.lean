module

public import Flapjack.Compiler.Backend.Backend.ToTarget
public import Flapjack.Compiler.Backend.BackendProof.CakeOracConfig

@[expose] public section

/-! backendProofScript.sml 2723-2771: the stack-frame configuration of a
successful compilation is the one computed by `to_stack`, and `to_word` keeps
the lab configuration. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.Backend Flapjack.Compiler.Backend.BackendDefs

/-- Exact HOL `compile_word_conf_eq` (`backendProofScript.sml:2723-2750`). `bm`
is free in HOL and an explicit parameter here. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "compile_word_conf_eq"
  (words_as_type_indexed_bitvec)]
theorem compileWordConf_eq {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (bm : List (BitVec width)) :
    ∀ (c : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec)
      (code : List (BitVec 8)) (data : List (BitVec width))
      (conf wConf : Flapjack.Compiler.Backend.Backend.Config)
      (stackProg : List (Nat × StackLang.HolProg width)) (stackNames : Spt MlString),
      BackendDefs.compile asmConf c prog = some (code, data, conf) ∧
        toStack asmConf c prog = (bm, wConf, stackProg, stackNames) →
      conf.wordConf.stackFrameSize = wConf.wordConf.stackFrameSize := by
  intro c prog code data conf wConf stackProg stackNames ⟨h1, h2⟩
  rw [compile_eq_toTarget] at h1
  simp only [toTarget, toLab, h2] at h1
  obtain ⟨bytes, lc, -, hr⟩ := attachBitmaps_some _ _ _ _ _ h1
  simp only [Prod.mk.injEq] at hr
  rw [hr.2.2]

/-- Exact HOL `to_word_lab_conf` (`backendProofScript.sml:2752-2771`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "to_word_lab_conf"
  (words_as_type_indexed_bitvec)]
theorem toWord_labConf {width : Nat} [NeZero width] (asmConf : AsmConfigExact width) :
    ∀ (c c' : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec)
      (p : List (Nat × Nat × WordLangProgHOL (BitVec width))) (n : Spt MlString),
      toWord asmConf c prog = (c', p, n) → c.labConf = c'.labConf := by
  intro c c' prog p n h
  have e : (toWord asmConf c prog).1.labConf = c.labConf := rfl
  rw [h] at e
  exact e.symm

end Flapjack.Compiler.Backend.BackendProof
