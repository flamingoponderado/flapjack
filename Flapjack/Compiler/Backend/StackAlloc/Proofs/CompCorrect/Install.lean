import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.Leaves
import Flapjack.Misc.Sptree.Wf

/-!
# `stack_allocProof` `comp_correct`: `Install`

The `Install` case of `comp_correct` (`stack_allocProofScript.sml:5297-5894`).
The target's compiler oracle is the source's mapped through `prog_comp`, its
compiler is `compile_rest`, and the source premise
`s.compile = (λc. compile_rest c o MAP prog_comp)` makes both compile the same
code. As in HOL (`spt_eq_thm`, `lookup_union`, `lookup_fromAList`,
`ALOOKUP_APPEND`, `ALOOKUP_MAP_2`, `ALOOKUP_toAList`), the installed compiled code
is the compiled union of the old code and the installed functions.
-/

namespace Flapjack.Compiler.Backend.StackAlloc.CompCorrect

open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open ProgCompSupport

variable {width : Nat} [NeZero width] {C F : Type}
variable (anything : WordSemGcFun width) (cr : CompileFn width C)

/-- Lookup in the compiled code: the GC stub, or the compiled function. -/
theorem sptLookup_compile (c : DataToWord.Config) (xs : List (Nat × HolProg width)) (k : Nat) :
    sptLookup k (sptFromAList (compile c xs)) =
      if k = gcStubLocation then some (.seq (wordGcCode c) (.ret 0))
      else (sptAListLookup k xs).map (fun p => (comp k (nextLabHOL p 2) p).1) := by
  rw [sptLookup_sptFromAList, compile, stubs]
  by_cases hk : k = gcStubLocation
  · simp [sptAListLookup, hk]
  · simp [sptAListLookup, hk, sptAListLookup_map_progComp]

/-- The compiled code of an installed union (HOL's `spt_eq_thm` step). -/
theorem compiled_union (c : DataToWord.Config) (code : Spt (HolProg width))
    (progs : List (Nat × HolProg width)) :
    sptUnion (sptFromAList (compile c (sptToAList code))) (sptFromAList (progs.map progComp)) =
      sptFromAList (compile c (sptToAList (sptUnion code (sptFromAList progs)))) := by
  refine (sptEqThm _ _ ⟨sptWfUnion _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩,
    sptWfFromAList _⟩).mpr fun k => ?_
  rw [sptLookup_sptUnion, sptLookup_compile, sptLookup_compile, sptAListLookup_sptToAList,
    sptAListLookup_sptToAList, sptLookup_sptUnion, sptLookup_sptFromAList,
    sptAListLookup_map_progComp, sptLookup_sptFromAList]
  by_cases hk : k = gcStubLocation
  · simp [hk]
  · simp only [hk, if_false]
    cases sptLookup k code <;> rfl

theorem goal_install (s : StackSemStateFiniteExact width C F) (ptr len dptr dlen ret : Nat) :
    Goal anything cr (.install ptr len dptr dlen ret : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_install] at h
  split at h
  · rename_i w1 w2 w3 w4 h1 h2 h3 h4
    show ∃ ck regs1, evaluate (.install ptr len dptr dlen ret, Tgt anything cr c s ck regs) = _ ∧ _
    rcases hco : s.compileOracle 0 with ⟨cfg, progs, bm⟩
    rw [hco] at h
    dsimp only at h
    simp only [hpre.useStack, if_true] at h
    split at h
    · rename_i bytes cb data db hcb hdb
      split at h
      · rename_i _ bytes' cfg' k p tail hcomp
        split at h
        · rename_i hc
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hcomp' : cr cfg (((k, p) :: tail).map progComp) = some (bytes', cfg') := by
            have := hpre.compile
            rw [this] at hcomp
            exact hcomp
          refine ⟨0, (restrictIn regs s.ffiSaveRegs).updateEq (ptr, .loc k 0), ?_,
            submap_fupdate_both (restrictIn_submap _ hpre.regs), ?_, fun _ => hpre.stack⟩
          · rw [tgt_zero, evaluate_install, getVar_res anything cr c s regs hpre.regs h1,
              getVar_res anything cr c s regs hpre.regs h2, getVar_res anything cr c s regs hpre.regs h3,
              getVar_res anything cr c s regs hpre.regs h4]
            have hoc : (oracleMap ∘ s.compileOracle) 0 = (cfg, ((k, p) :: tail).map progComp, bm) := by
              show oracleMap (s.compileOracle 0) = _
              rw [hco]; rfl
            dsimp only
            rw [hoc]
            dsimp only
            rw [hcb, if_pos rfl, hdb]
            simp only [List.map_cons, progComp]
            simp only [List.map_cons, progComp] at hcomp'
            rw [hcomp']
            dsimp only
            rw [if_pos ⟨hc.1, hc.2.1, hc.2.2⟩]
            simp only [Prod.mk.injEq, true_and, StackSemStateFiniteExact.mk.injEq]
            have hu := compiled_union c s.code ((k, p) :: tail)
            simp only [List.map_cons, progComp] at hu
            exact ⟨funext fun _ => rfl, hu, trivial⟩
          · have hb := hpre.buf
            simp only [wordSemBufferFlush] at hdb
            split at hdb
            · simp only [Option.some.injEq, Prod.mk.injEq] at hdb
              obtain ⟨rfl, rfl⟩ := hdb
              obtain ⟨-, rfl, -⟩ := hc
              unfold BufBound at hb ⊢
              simp only [List.length_append, List.length_nil]
              omega
            · simp at hdb
        · simp only [Prod.mk.injEq] at h
          exact absurd h.1.symm hr
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hr
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

end Flapjack.Compiler.Backend.StackAlloc.CompCorrect
