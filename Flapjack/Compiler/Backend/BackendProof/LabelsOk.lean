module

public import Flapjack.Compiler.Backend.Backend.ToTarget
public import Flapjack.Compiler.Backend.BackendProof.ConfigOk
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.WholeDistinct
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.WholeNames

@[expose] public section

/-! backendProofScript.sml 1481-1497: the function names produced by the
staged pipeline up to data language are distinct and above the data stubs. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.Backend Flapjack.Compiler.Backend.BackendDefs

/-- Exact HOL `to_data_labels_ok` (`backendProofScript.sml:1481-1497`). HOL's
free `asm_conf`, `c`, `prog`, `b`, `bm` and `c'` are explicit parameters. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "to_data_labels_ok"
  (words_as_type_indexed_bitvec)]
theorem toData_labelsOk {width : Nat} [NeZero width] (asmConf : AsmConfigExact width)
    (c : Flapjack.Compiler.Backend.Backend.Config) (prog : List AstHOL.Dec)
    (b : List (BitVec 8)) (bm : List (BitVec width))
    (c' : Flapjack.Compiler.Backend.Backend.Config) :
    BackendDefs.compile asmConf c prog = some (b, bm, c') ∧ backendConfigOk asmConf c →
      let (_, p, _) := toData c prog
      (∀ n ∈ p.map Prod.fst, dataNumStubs ≤ n) ∧ (p.map Prod.fst).Nodup := by
  intro ⟨_, hok⟩
  have hname : c.bvlConf.nextName2 = bvlNumStubs + 2 := hok.2.2.1
  rcases hb : toBvl c prog with ⟨c1, p1, n1⟩
  have hc1 : c1.bvlConf = c.bvlConf := by
    simp only [toBvl, toClos, toFlat] at hb
    rw [← (Prod.mk.inj hb).1]
  have hd : (p1.map Prod.fst).Nodup := by
    simp only [toBvl] at hb
    have h2 := (Prod.mk.inj hb).2
    exact ClosToBvl.compileSource_allDistinct (toClos c prog).1.closConf (toClos c prog).2
      _ p1 n1 (by rw [← (Prod.mk.inj h2).1, ← (Prod.mk.inj h2).2])
  rcases hs : BvlToBvi.compileSource c1.closConf.start c1.bvlConf n1 p1 with
    ⟨loc, code, inl, binl, m1, m2, m3, names⟩
  have key := BvlToBvi.Proofs.compile_distinctNames c1.closConf.start c1.bvlConf n1 p1
    loc code inl binl m1 m2 (m3, names) 0 ⟨hs, hd, by rw [hc1, hname]; simp⟩
  have hmap : (BviToData.compileProg code).map Prod.fst = code.map Prod.fst := by
    simp [BviToData.compileProg, BviToData.compilePart, Function.comp_def]
  simp only [toData, toBvi, hb, hs, hmap]
  exact key

end Flapjack.Compiler.Backend.BackendProof
