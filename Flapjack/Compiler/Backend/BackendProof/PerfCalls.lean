module

public import Flapjack.Compiler.Backend.Backend.ToTarget

@[expose] public section

/-! backendProofScript.sml 1531-1561: the staged pipeline `to_bvi`, `to_data`
and `to_word` keeps the stack configuration's `perf_calls` flag. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.Backend Flapjack.Compiler.Backend.BackendDefs

/-- Exact HOL `to_bvi_perf_calls` (`backendProofScript.sml:1531-1539`). HOL's
`⇔` on the boolean `perf_calls` flags is Lean `Bool` equality. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "to_bvi_perf_calls"]
theorem toBvi_perfCalls :
    ∀ (c c' : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec)
      (p : List (Nat × Nat × Bvi.Exp)) (n : Spt MlString),
      toBvi c prog = (c', p, n) →
      c.stackConf.perfCalls = c'.stackConf.perfCalls := by
  intro c c' prog p n h
  simp only [toBvi, toBvl, toClos, toFlat] at h
  rw [← (Prod.mk.inj h).1]

/-- Exact HOL `to_data_perf_calls` (`backendProofScript.sml:1541-1550`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "to_data_perf_calls"]
theorem toData_perfCalls :
    ∀ (c c' : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec)
      (p : List (Nat × Nat × DataLang.Prog)) (n : Spt MlString),
      toData c prog = (c', p, n) →
      c.stackConf.perfCalls = c'.stackConf.perfCalls := by
  intro c c' prog p n h
  have := toBvi_perfCalls c (toBvi c prog).1 prog (toBvi c prog).2.1 (toBvi c prog).2.2 rfl
  rw [this, ← (Prod.mk.inj h).1]
  rfl

/-- Exact HOL `to_word_perf_calls` (`backendProofScript.sml:1552-1561`).
HOL's `asm_conf` is free and is an explicit parameter here. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "to_word_perf_calls"
  (words_as_type_indexed_bitvec)]
theorem toWord_perfCalls {width : Nat} [NeZero width] (asmConf : AsmConfigExact width) :
    ∀ (c c' : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec)
      (p : List (Nat × Nat × WordLangProgHOL (BitVec width))) (n : Spt MlString),
      toWord asmConf c prog = (c', p, n) →
      c.stackConf.perfCalls = c'.stackConf.perfCalls := by
  intro c c' prog p n h
  have := toData_perfCalls c (toData c prog).1 prog (toData c prog).2.1 (toData c prog).2.2 rfl
  rw [this, ← (Prod.mk.inj h).1]
  rfl

end Flapjack.Compiler.Backend.BackendProof
