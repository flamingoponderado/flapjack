module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.WholeSemantics
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.Namespace
public import Flapjack.Compiler.Backend.BackendProps.OracleMonotonic
public import Flapjack.Compiler.Backend.BviTailrec.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation

@[expose] public section

/-! backendProofScript.sml 760-820: `bvl_to_bvi_compile_semantics2`, the
BVL-to-BVI whole-program theorem with its fresh-name oracle conditions
replaced by the state-oracle shape produced by the backend's incremental
compiler. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Compiler.Backend Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.BackendProps Flapjack.Compiler.Backend.BvlToBvi.Proofs

/-- Exact HOL `bvl_to_bvi_compile_semantics2` (`backendProofScript.sml:760-820`).
`ALL_DISTINCT` is `List.Nodup`, `FST (co 0) = (…, v)` is stated on `(co 0).1`,
`fromAList` is `sptFromAList`, and the oracle, compiler and semantics are the
reviewed bvl_to_bvi renderings used by `compile_semantics`. The semantics
inherit the real-model assumption of SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "bvl_to_bvi_compile_semantics2"]
theorem bvlToBvi_compileSemantics2 {C F : Type} (start : Nat) (c : BvlToBvi.Config)
    (names : Spt MlString) (prog : List (Nat × Nat × Bvl.Exp)) (start' : Nat)
    (prog' : List (Nat × Nat × Bvi.Exp)) (inlines : Spt (Nat × Bvl.Exp))
    (bviInlines : Spt (Nat × Bvi.Exp)) (n1 n2 n3 : Nat) (names1 : Spt MlString)
    (co : Nat → (Spt (Nat × Bvl.Exp) × Nat × Nat × Nat × Spt (Nat × Bvi.Exp) × C) ×
      List (Nat × Nat × Bvl.Exp))
    (ffi0 : HolFfiState F) (cc : BviSem.Compiler C) :
    BvlToBvi.compileSource start c names prog =
        (start', prog', inlines, bviInlines, n1, n2, n3, names1) ∧
      (∃ v, (co 0).1 = (inlines, n1, n2, n3, bviInlines, v)) ∧
      (∀ n, ((co n).2.map Prod.fst).Nodup) ∧
      (prog.map Prod.fst).Nodup ∧
      isStateOracle (BviTailrec.compileProgSource c.doTailrec)
        (stateCo BvlToBvi.compileIncSource
          (stateCo (BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut) co)) ∧
      isStateOracle (BviTmc.compileProgSource c.doTmc)
        (stateCo (BviTailrec.compileProgSource c.doTailrec)
          (stateCo BvlToBvi.compileIncSource
            (stateCo (BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut) co))) →
    BvlSem.semantics ffi0 (sptFromAList prog) co (fullCc c cc) start ≠ .fail →
    BviSem.semantics ffi0 (sptFromAList prog') (fullCo c co) cc start' =
      BvlSem.semantics ffi0 (sptFromAList prog) co (fullCc c cc) start := by
  intro ⟨run, ⟨v, h0⟩, hdist, hprog, htail, htmc⟩ nonfail
  -- the names produced by the whole-program pass
  have hn : (∃ r, n2 = (BviTailrec.compileProgSource c.doTailrec (bvlNumStubs + 2) r).1) ∧
      (∃ r, n3 = (BviTmc.compileProgSource c.doTmc (bvlNumStubs + 3) r).1) := by
    simp only [BvlToBvi.compileSource] at run
    simp only [Prod.mk.injEq] at run
    exact ⟨⟨_, run.2.2.2.2.2.1.symm⟩, ⟨_, run.2.2.2.2.2.2.1.symm⟩⟩
  obtain ⟨⟨r2, hr2⟩, ⟨r3, hr3⟩⟩ := hn
  have h2_0 : ∃ k, n2 = bvlNumStubs + 2 + bvlToBviNamespaces * k := by
    rcases hc : BviTailrec.compileProgSource c.doTailrec (bvlNumStubs + 2) r2 with ⟨a, b⟩
    rw [hc] at hr2
    obtain ⟨k, hk⟩ := BviTailrec.Proofs.compileProg_nextMono _ _ _ a b hc
    exact ⟨k, by rw [hr2, hk]⟩
  have h3_0 : ∃ k, n3 = bvlNumStubs + 3 + bvlToBviNamespaces * k := by
    rcases hc : BviTmc.compileProgSource c.doTmc (bvlNumStubs + 3) r3 with ⟨a, b⟩
    rw [hc] at hr3
    obtain ⟨k, hk⟩ := BviTmc.compileProgSource_next_mono _ _ a r3 b hc
    exact ⟨k, by rw [hr3, hk]⟩
  have hns : ∀ i, (∃ k, (co i).1.2.2.1 = bvlNumStubs + 2 + bvlToBviNamespaces * k) ∧
      (∃ k, (co i).1.2.2.2.1 = bvlNumStubs + 3 + bvlToBviNamespaces * k) := by
    intro i
    induction i with
    | zero => rw [h0]; exact ⟨h2_0, h3_0⟩
    | succ i ih =>
        obtain ⟨⟨k2, hk2⟩, ⟨k3, hk3⟩⟩ := ih
        have t2 := htail i
        have t3 := htmc i
        simp only [stateCo] at t2 t3
        constructor
        · rcases hc : BviTailrec.compileProgSource c.doTailrec (co i).1.2.2.1
              (BvlToBvi.compileIncSource (co i).1.2.1
                (BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut
                  (co i).1.1 (co i).2).2).2 with ⟨a, b⟩
          rw [hc] at t2
          obtain ⟨j, hj⟩ := BviTailrec.Proofs.compileProg_nextMono _ _ _ a b hc
          refine ⟨k2 + j, ?_⟩
          rw [t2, hj, hk2]
          simp only [Flapjack.bvlToBviNamespaces]
          omega
        · rcases hc : BviTmc.compileProgSource c.doTmc (co i).1.2.2.2.1
              (BviTailrec.compileProgSource c.doTailrec (co i).1.2.2.1
                (BvlToBvi.compileIncSource (co i).1.2.1
                  (BvlInline.compileInc c.inlineSizeLimit c.splitMainAtSeq c.expCut
                    (co i).1.1 (co i).2).2).2).2 with ⟨a, b⟩
          rw [hc] at t3
          obtain ⟨j, hj⟩ := BviTmc.compileProgSource_next_mono _ _ a _ b hc
          refine ⟨k3 + j, ?_⟩
          rw [t3, hj, hk3]
          simp only [Flapjack.bvlToBviNamespaces]
          omega
  refine compile_semantics start c names names1 prog start' prog' inlines bviInlines n1 n2 n3
    co ffi0 cc ⟨run, by rw [h0], by rw [h0], by rw [h0], by rw [h0], by rw [h0], ?_, hprog⟩ nonfail
  intro i
  obtain ⟨⟨k2, hk2⟩, ⟨k3, hk3⟩⟩ := hns i
  refine ⟨hdist i, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hk2, hk3, inNs, bvlNumStubs, dataNumStubs, wordNumStubs, stackNumStubs,
      Flapjack.bvlToBviNamespaces] <;> omega

end Flapjack.Compiler.Backend.BackendProof
