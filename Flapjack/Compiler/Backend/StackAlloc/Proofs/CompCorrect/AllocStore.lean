import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.Leaves
import Flapjack.Compiler.Backend.StackProps.AllocationConstants

/-!
# `stack_allocProof` `comp_correct`: `Alloc` and `StoreConsts`

The two cases of `comp_correct` (`stack_allocProofScript.sml:5297-5894`) that
`comp` rewrites into returning calls to stubs. `Alloc` follows HOL through
`alloc_correct` on the state with the compiled compiler and oracle (which
`alloc` leaves untouched) and `alloc_length_stack`; `StoreConsts (SOME loc)`
runs the found stub `Seq (StoreConsts t1 t2 NONE) (Return 0)` with one extra
clock tick, as HOL's `qexists_tac '1'`.
-/

namespace Flapjack.Compiler.Backend.StackAlloc.CompCorrect

open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

variable {width : Nat} [NeZero width] {C F : Type}
variable (anything : WordSemGcFun width) (cr : CompileFn width C)

/-- `gc` leaves the compiler and its oracle untouched. -/
theorem gc_withCompile (s : StackSemStateFiniteExact width C F) (X : CompileFn width C)
    (Y : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    StackSemAllocation.gc { s with compile := X, compileOracle := Y } =
      (StackSemAllocation.gc s).map (fun s => { s with compile := X, compileOracle := Y }) := by
  simp only [StackSemAllocation.gc]
  repeat' first | split | simp_all

/-- `alloc` leaves the compiler and its oracle untouched (as HOL's
`alloc_def,set_store_def,gc_def` step of the `Alloc` case). -/
theorem alloc_withCompile (w : BitVec width) (s : StackSemStateFiniteExact width C F)
    (X : CompileFn width C) (Y : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    StackSemAllocation.alloc w { s with compile := X, compileOracle := Y } =
      Prod.map id (fun s => { s with compile := X, compileOracle := Y })
        (StackSemAllocation.alloc w s) := by
  simp only [StackSemAllocation.alloc]
  rw [show setStore .allocSize (.word w) { s with compile := X, compileOracle := Y } =
    { setStore .allocSize (.word w) s with compile := X, compileOracle := Y } from rfl,
    gc_withCompile]
  cases hg : StackSemAllocation.gc (setStore .allocSize (.word w) s) <;> simp only [Option.map]
  · rfl
  · repeat' first | split | simp_all [emptyEnv]

theorem goal_alloc (s : StackSemStateFiniteExact width C F) (k : Nat) :
    Goal anything cr (.alloc k : HolProg width) s := by
  intro r t m n c regs h hr ha hpre
  have hk : k = 1 := ha
  subst hk
  rw [evaluate_alloc] at h
  simp only [hpre.useAlloc, Bool.not_true, Bool.false_eq_true, if_false] at h
  split at h
  · rename_i w hw
    have hac := StackPropsAllocationConstants.allocConst w s t r h
    obtain ⟨-, -, -, -, -, hcode, -, -, -, -, hbm, -, hdb, -, hor⟩ := hac
    have h' := alloc_withCompile w s cr (oracleMap ∘ s.compileOracle)
    rw [h] at h'
    have hb := hpre.buf
    obtain ⟨ck, l2, he, hsub⟩ := AllocCorrect.alloc_correct (c := c) (l := regs) (n' := n) (m := m)
      (anything := anything) h' hr hpre.gcFun
      (by unfold BufBound at hb; show s.bitmaps.length < 2 ^ width - 1; omega)
      hpre.stack (hpre.regs _ _ hw)
    refine ⟨ck, l2, ?_, hsub, ?_, fun hh => ?_⟩
    · show evaluate (.call (some (.skip, 0, n, m)) (.inl gcStubLocation) none, _) = _
      convert he using 3
      all_goals first | rfl | rw [hcode] | rw [hor]
    · unfold BufBound at hb ⊢
      rw [hbm, hdb]; exact hb
    · unfold StackBound
      rw [AllocCorrect.alloc_length_stack h hpre.gcFun hh]
      exact hpre.stack
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

open StackSemStoreConsts in
/-- `store_const_sem` run from the compiled state, whose registers extend the
source registers away from register 0 and where `use_alloc` is false (so the
source's `unset_var 0` is not repeated): the target keeps register 0. -/
theorem storeConstSem_res (c : DataToWord.Config) (s t : StackSemStateFiniteExact width C F)
    (R : HolFiniteMapExact Nat (WordLocW width)) (hR : (s.regs.eraseEq 0).submap R)
    (hA : s.useAlloc = true) (t1 t2 : Nat) (r : Option (StackSemResult width))
    (hr : r ≠ some .error) (h : storeConstSem t1 t2 s = (r, t)) :
    ∃ R1, storeConstSem (resultWidth := width) t1 t2 (Res anything cr c s R) =
        (r, Res anything cr c t R1) ∧ t.regs.submap R1 ∧ R1.lookup 0 = R.lookup 0 ∧
      r = none ∧ t.clock = s.clock ∧ t.stack = s.stack ∧ BufBound t = BufBound s := by
  have hk : ∀ k v, k ≠ 0 → s.regs.lookup k = some v → R.lookup k = some v := by
    intro k v hk hv
    apply hR
    simp [FDOMSUB_HOL, hk, hv]
  simp only [storeConstSem] at h ⊢
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i hnd
  rw [if_neg hnd]
  have hnd' := hnd
  simp only [not_not, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hnd'
  split at h
  · rename_i i a off h1 h2 h3
    have g1 : getVar 1 (Res anything cr c s R) = some (.word i) := hk 1 _ (by decide) h1
    have g2 : getVar 2 (Res anything cr c s R) = some (.word a) := hk 2 _ (by decide) h2
    have g3 : getVar 3 (Res anything cr c s R) = some (.word off) := hk 3 _ (by decide) h3
    rw [g1, g2, g3]
    dsimp only
    split at h
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
    · rename_i a' m' hc
      rw [hc]
      simp only [hA, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨(((R.updateEq (2, .word a')).updateEq (1, .word 1)).updateEq (t2, .word 1)).updateEq
        (t1, .word 1), ?_, ?_, ?_, ?_⟩
      · rfl
      · intro k v hkv
        simp only [unsetVarZero, setVar, HolFiniteMapExact.lookup_eraseEq,
          HolFiniteMapExact.lookup_updateEq, FDOMSUB_HOL, FUPDATE_HOL] at hkv ⊢
        split_ifs at hkv ⊢ <;> first | exact hkv | exact hk k v ‹_› hkv
      · simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
        obtain ⟨⟨h01, h02, h03, h0t1, h0t2⟩, -, -, -, -⟩ := hnd'
        rw [if_neg h0t1, if_neg h0t2, if_neg (by decide), if_neg (by decide)]
      · exact ⟨rfl, rfl, rfl, rfl⟩
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

open StackSemStoreConstsGuard in
theorem goal_storeConsts (s : StackSemStateFiniteExact width C F) (t1 t2 : Nat)
    (stub : Option Nat) : Goal anything cr (.storeConsts t1 t2 stub : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_storeConsts] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i hS
  rw [if_neg (by simp [hpre.useAlloc])] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i hchk
  have hR : (s.regs.eraseEq 0).submap regs := by
    intro k v hk
    simp only [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL] at hk
    split at hk
    · simp at hk
    · exact hpre.regs _ _ hk
  cases stub with
  | none =>
      obtain ⟨R1, he, hsub, -, -, -, hst, hbuf⟩ :=
        storeConstSem_res anything cr c s t regs hR hpre.useAlloc t1 t2 r hr h
      refine ⟨0, R1, ?_, hsub, hbuf ▸ hpre.buf, fun _ => by unfold StackBound; rw [hst]; exact hpre.stack⟩
      show evaluate (.storeConsts t1 t2 none, Res anything cr c s regs) = _
      rw [evaluate_storeConsts]
      simp only [not_true_eq_false, if_false, Option.isSome_none, Bool.false_eq_true, and_false]
      simp only [checkStoreConstsOpt, not_true_eq_false, if_false]
      exact he
  | some loc =>
      have hlk : sptLookup loc s.code = some (.seq (.storeConsts t1 t2 none) (.ret 0)) :=
        (checkStoreConstsOpt_some_iff t1 t2 loc s.code).1 (by simpa using hchk)
      have hloc := (hpre.code loc _ hlk).1
      obtain ⟨m1, n1, hcl⟩ := lookup_IMP_lookup_compile (c := c) ⟨hlk, hloc⟩
      have hR' : (s.regs.eraseEq 0).submap (regs.updateEq (0, .loc n m)) := by
        intro k v hk
        simp only [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL] at hk
        split at hk
        · simp at hk
        · rename_i hk0
          simp only [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, if_neg hk0]
          exact hpre.regs _ _ hk
      obtain ⟨R1, he, hsub, h0, rfl, hclk, hst, hbuf⟩ :=
        storeConstSem_res anything cr c s t (regs.updateEq (0, .loc n m)) hR' hpre.useAlloc t1 t2 r
          hr h
      refine ⟨1, R1, ?_, hsub, hbuf ▸ hpre.buf, fun _ => by unfold StackBound; rw [hst]; exact hpre.stack⟩
      show evaluate (.call (some (.skip, 0, n, m)) (.inl loc) none, Tgt anything cr c s 1 regs) = _
      rw [evaluate_call]
      simp only [StackSemControl.findCode]
      rw [hcl]
      simp only [comp]
      rw [if_neg (by simp)]
      have hds : decClock (setVar 0 (.loc n m) (Tgt anything cr c s 1 regs)) =
          Res anything cr c s (regs.updateEq (0, .loc n m)) := rfl
      rw [hds, evaluate_seq, evaluate_storeConsts]
      simp only [not_true_eq_false, if_false, Option.isSome_none, Bool.false_eq_true, and_false,
        checkStoreConstsOpt]
      rw [he]
      simp only [StackSemControl.fixClock, hclk, Nat.min_self]
      rw [evaluate_ret]
      have hg0 : getVar 0 { Res anything cr c t R1 with clock := s.clock } = some (.loc n m) := by
        show R1.lookup 0 = _
        rw [h0]
        simp [FUPDATE_HOL]
      rw [hg0]
      simp only [ne_eq, not_true_eq_false, if_false, evaluate_skip]
      simp [hclk]

end Flapjack.Compiler.Backend.StackAlloc.CompCorrect
