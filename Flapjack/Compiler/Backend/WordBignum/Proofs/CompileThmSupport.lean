module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.CallFrame
public import Flapjack.Compiler.Backend.WordBignum.Proofs.CompileCode
public import Flapjack.Compiler.Backend.WordBignum.Proofs.Syntax
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeapWrites
public import Flapjack.Compiler.Backend.StackRemove.Proofs.StackHeap
public import Mathlib.Tactic.Set
public import Flapjack.Pancake.Semantics.LoopProps.AccVars
public import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport

@[expose] public section

/-! Flapjack-only support lemmas for the `compile_thm` port of
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`: how the compiled
straight-line code moves the `wordSem` state, and how those moves preserve
the source's `state_rel`. They have no separate HOL names. -/

namespace Flapjack.Compiler.Backend.WordBignum.CompileThmSupport

open Flapjack
open Flapjack.WordSemStateFiniteExact.BignumClauses
open Flapjack.Compiler.Backend.WordBignum

variable {width : Nat} [NeZero width] {β C F : Type}

/-- `state_rel` does not inspect the locals. -/
theorem stateRel_locals {s : MiniState width} {t t0 : WordSemStateFiniteExact width C F}
    {cs : β × List (CodeEntry width)} {frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    (l : Spt (WordLocW width)) (h : stateRel s t cs t0 frame) :
    stateRel s { t with locals := l } cs t0 frame := h

/-- `state_rel` does not inspect a `set_var`. -/
theorem stateRel_setVar {s : MiniState width} {t t0 : WordSemStateFiniteExact width C F}
    {cs : β × List (CodeEntry width)} {frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    (n : Nat) (v : WordLocW width) (h : stateRel s t cs t0 frame) :
    stateRel s (WordSemStateFiniteExact.setVar n v t) cs t0 frame := h

/-- Distinct small register numbers name distinct temporaries. -/
theorem temp_ofNat_inj {a b : Nat} (ha : a < 32) (hb : b < 32)
    (h : (WordStore.temp (BitVec.ofNat 5 a) : WordStoreHOL) = .temp (BitVec.ofNat 5 b)) :
    a = b := by
  simp only [WordStore.temp.injEq] at h
  have := congrArg BitVec.toNat h
  simp [BitVec.toNat_ofNat] at this
  omega

theorem temp_ne_tempIn1 {a : Nat} (ha : a < 25) :
    (WordStore.temp (BitVec.ofNat 5 a) : WordStoreHOL) ≠ tempIn1 := by
  intro h
  have := temp_ofNat_inj (a := a) (b := 31) (by omega) (by omega) h
  omega

theorem temp_ne_tempIn2 {a : Nat} (ha : a < 25) :
    (WordStore.temp (BitVec.ofNat 5 a) : WordStoreHOL) ≠ tempIn2 := by
  intro h
  have := temp_ofNat_inj (a := a) (b := 30) (by omega) (by omega) h
  omega

theorem temp_ne_tempOut {a : Nat} (ha : a < 25) :
    (WordStore.temp (BitVec.ofNat 5 a) : WordStoreHOL) ≠ tempOut := by
  intro h
  have := temp_ofNat_inj (a := a) (b := 29) (by omega) (by omega) h
  omega

/-- Writing one register through its temporary preserves `state_rel`. -/
theorem stateRel_write {s : MiniState width} {t t0 : WordSemStateFiniteExact width C F}
    {cs : β × List (CodeEntry width)} {frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    (j : Nat) (v : BitVec width) (hj : j < 25) (h : stateRel s t cs t0 frame) :
    stateRel (regWrite j (some v) s)
      (WordSemStateFiniteExact.setStore (.temp (BitVec.ofNat 5 j)) (.word v) t) cs t0 frame := by
  obtain ⟨hc, ha, hr, hcode, hdiv, htd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14⟩ := h
  have hstore : ∀ key, (t.store.updateEq (.temp (BitVec.ofNat 5 j), .word v)).lookup key =
      if key = .temp (BitVec.ofNat 5 j) then some (.word v) else t.store.lookup key := by
    intro key; rfl
  refine ⟨hc, ?_, ?_, hcode, hdiv, htd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    ?_, ?_⟩
  · simp only [WordSemStateFiniteExact.setStore, hstore, regWrite]
    rw [if_neg (temp_ne_tempIn1 hj).symm, if_neg (temp_ne_tempIn2 hj).symm,
      if_neg (temp_ne_tempOut hj).symm]
    exact ha
  · intro a w hw
    simp only [regWrite] at hw
    change FUPDATE_HOL s.regs.lookup (j, v) a = some w at hw
    simp only [FUPDATE_HOL] at hw
    simp only [WordSemStateFiniteExact.setStore, hstore]
    by_cases haj : a = j
    · subst haj
      simp at hw
      exact ⟨hj, by simp [hw]⟩
    · rw [if_neg haj] at hw
      obtain ⟨ha25, hl⟩ := hr a w hw
      refine ⟨ha25, ?_⟩
      rw [if_neg (fun he => haj (temp_ofNat_inj (by omega) (by omega) he))]
      exact hl
  · simp only [WordSemStateFiniteExact.setStore, hstore]
    rw [if_neg (temp_ne_tempOut hj).symm]
    exact h13
  · intro n hn
    simp only [WordSemStateFiniteExact.setStore, hstore]
    rw [if_neg (hn _)]
    exact h14 n hn

/-- A first statement that finishes normally can be peeled off a nested
sequence. -/
theorem evaluate_seq_seq_none {t t' : WordSemStateFiniteExact width C F}
    {a x p9 : WordLangProgHOL (BitVec width)}
    (h : WordSemStateFiniteExact.evaluate a t = (none, t')) :
    WordSemStateFiniteExact.evaluate (.seq (.seq a x) p9) t =
      WordSemStateFiniteExact.evaluate (.seq x p9) t' := by
  rw [← evaluate_seqSeq, evaluate_seq_of_none _ _ _ _ h]

/-- Copying a live temporary into a local. -/
theorem evaluate_seqTemp_live {t : WordSemStateFiniteExact width C F} {k r : Nat}
    {v : WordLocW width} {x p9 : WordLangProgHOL (BitVec width)}
    (h : t.store.lookup (.temp (BitVec.ofNat 5 r)) = some v) :
    WordSemStateFiniteExact.evaluate (.seq (seqTemp k r x) p9) t =
      WordSemStateFiniteExact.evaluate (.seq x p9) (WordSemStateFiniteExact.setVar k v t) := by
  unfold seqTemp
  apply evaluate_seq_seq_none
  rw [evaluate_assign]
  simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore, h]

/-- A conditional whose comparison succeeds continues with the chosen branch. -/
theorem evaluate_seq_ite {t : WordSemStateFiniteExact width C F} {c : Cmp} {r1 : Nat}
    {ri : WordRegImm (BitVec width)} {c1 c2 p9 : WordLangProgHOL (BitVec width)}
    {x y : WordLocW width} {b : Bool}
    (hx : WordSemStateFiniteExact.getVar r1 t = some x)
    (hy : WordSemStateFiniteExact.getVarImm ri t = some y)
    (hc : wordSemWordCmp c x y = some b) :
    WordSemStateFiniteExact.evaluate (.seq (.ite c r1 ri c1 c2) p9) t =
      WordSemStateFiniteExact.evaluate (.seq (if b then c1 else c2) p9) t := by
  rw [evaluate_seq, evaluate_ite, hx, hy]
  simp only [hc]
  cases b <;> simp [evaluate_seq]

theorem ev_assign {t : WordSemStateFiniteExact width C F} {k : Nat}
    {e : WordLangExpHOL (BitVec width)} {v : WordLocW width}
    (h : WordSemStateFiniteExact.wordExp t e = some v) :
    WordSemStateFiniteExact.evaluate (.assign k e) t =
      (none, WordSemStateFiniteExact.setVar k v t) := by
  rw [evaluate_assign, h]

theorem ev_set {t : WordSemStateFiniteExact width C F} {k : WordStoreHOL}
    {e : WordLangExpHOL (BitVec width)} {v : WordLocW width}
    (hk : ¬ (k = .handler ∨ k = .bitmapBase))
    (h : WordSemStateFiniteExact.wordExp t e = some v) :
    WordSemStateFiniteExact.evaluate (.set k e) t =
      (none, WordSemStateFiniteExact.setStore k v t) := by
  rw [evaluate_set, if_neg hk, h]

theorem ev_seq {t t' : WordSemStateFiniteExact width C F} {a b : WordLangProgHOL (BitVec width)}
    {r : Option (WordSemResult width) × WordSemStateFiniteExact width C F}
    (h1 : WordSemStateFiniteExact.evaluate a t = (none, t'))
    (h2 : WordSemStateFiniteExact.evaluate b t' = r) :
    WordSemStateFiniteExact.evaluate (.seq a b) t = r := by
  rw [evaluate_seq_of_none _ _ _ _ h1, h2]

theorem wordExp_lookup (t : WordSemStateFiniteExact width C F) (k : WordStoreHOL) :
    WordSemStateFiniteExact.wordExp t (.lookup k) = t.store.lookup k := by
  simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getStore]

theorem wordExp_var (t : WordSemStateFiniteExact width C F) (k : Nat) :
    WordSemStateFiniteExact.wordExp t (.var k) = WordSemStateFiniteExact.getVar k t := by
  simp [WordSemStateFiniteExact.wordExp]

theorem getVar_setVar_same (t : WordSemStateFiniteExact width C F) (k : Nat) (v : WordLocW width) :
    WordSemStateFiniteExact.getVar k (WordSemStateFiniteExact.setVar k v t) = some v :=
  sptLookup_sptInsert_same k v t.locals

theorem getVar_setVar_ne (t : WordSemStateFiniteExact width C F) {k j : Nat} (v : WordLocW width)
    (h : k ≠ j) :
    WordSemStateFiniteExact.getVar j (WordSemStateFiniteExact.setVar k v t) =
      WordSemStateFiniteExact.getVar j t :=
  sptLookup_sptInsert_ne k j v t.locals (Ne.symm h)

theorem getVar_setStore (t : WordSemStateFiniteExact width C F) (k : Nat) (n : WordStoreHOL)
    (v : WordLocW width) :
    WordSemStateFiniteExact.getVar k (WordSemStateFiniteExact.setStore n v t) =
      WordSemStateFiniteExact.getVar k t := rfl

theorem store_setStore (t : WordSemStateFiniteExact width C F) (n m : WordStoreHOL)
    (v : WordLocW width) :
    (WordSemStateFiniteExact.setStore n v t).store.lookup m =
      if m = n then some v else t.store.lookup m := rfl

theorem store_setVar (t : WordSemStateFiniteExact width C F) (k : Nat) (v : WordLocW width) :
    (WordSemStateFiniteExact.setVar k v t).store = t.store := rfl

theorem temp_not_special (a : BitVec 5) :
    ¬ ((WordStore.temp a : WordStoreHOL) = .handler ∨ (WordStore.temp a : WordStoreHOL) = .bitmapBase) := by
  simp

theorem ev_inst {t t' : WordSemStateFiniteExact width C F} {i : WordLangInst (BitVec width)}
    (h : WordSemStateFiniteExact.inst i t = some t') :
    WordSemStateFiniteExact.evaluate (.inst i) t = (none, t') := by
  rw [evaluate_inst, h]

/-- Copying a live temporary into a local, as a statement. -/
theorem ev_seqTemp {t : WordSemStateFiniteExact width C F} {k r : Nat}
    {v : WordLocW width} {x : WordLangProgHOL (BitVec width)}
    {res : Option (WordSemResult width) × WordSemStateFiniteExact width C F}
    (h : t.store.lookup (.temp (BitVec.ofNat 5 r)) = some v)
    (hx : WordSemStateFiniteExact.evaluate x (WordSemStateFiniteExact.setVar k v t) = res) :
    WordSemStateFiniteExact.evaluate (seqTemp k r x) t = res :=
  ev_seq (ev_assign (by rw [wordExp_lookup]; exact h)) hx

theorem setStore_comm (t : WordSemStateFiniteExact width C F) {a b : WordStoreHOL}
    (va vb : WordLocW width) (h : a ≠ b) :
    WordSemStateFiniteExact.setStore a va (WordSemStateFiniteExact.setStore b vb t) =
      WordSemStateFiniteExact.setStore b vb (WordSemStateFiniteExact.setStore a va t) := by
  simp only [WordSemStateFiniteExact.setStore]
  congr 1
  apply HolFiniteMapExact.ext_of_lookup
  intro k
  change FUPDATE_HOL (FUPDATE_HOL t.store.lookup (b, vb)) (a, va) k =
    FUPDATE_HOL (FUPDATE_HOL t.store.lookup (a, va)) (b, vb) k
  simp only [FUPDATE_HOL]
  by_cases hka : k = a
  · subst hka; simp [h]
  · simp [hka]

/-- Writing a temporary that holds no register or array pointer preserves
`state_rel`. -/
theorem stateRel_setStore_free {s : MiniState width} {t t0 : WordSemStateFiniteExact width C F}
    {cs : β × List (CodeEntry width)} {frame : ((BitVec width × WordLocW width) → Prop) → Prop}
    (k : Nat) (v : WordLocW width) (hk1 : 25 ≤ k) (hk2 : k < 29) (h : stateRel s t cs t0 frame) :
    stateRel s (WordSemStateFiniteExact.setStore (.temp (BitVec.ofNat 5 k)) v t) cs t0 frame := by
  obtain ⟨hc, ha, hr, hcode, hdiv, htd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14⟩ := h
  have hne : ∀ j, j < 32 → j ≠ k →
      (WordStore.temp (BitVec.ofNat 5 j) : WordStoreHOL) ≠ .temp (BitVec.ofNat 5 k) :=
    fun j hj hjk he => hjk (temp_ofNat_inj hj (by omega) he)
  have hIn1 : tempIn1 ≠ (WordStore.temp (BitVec.ofNat 5 k) : WordStoreHOL) :=
    hne 31 (by omega) (by omega)
  have hIn2 : tempIn2 ≠ (WordStore.temp (BitVec.ofNat 5 k) : WordStoreHOL) :=
    hne 30 (by omega) (by omega)
  have hOut : tempOut ≠ (WordStore.temp (BitVec.ofNat 5 k) : WordStoreHOL) :=
    hne 29 (by omega) (by omega)
  refine ⟨hc, ?_, ?_, hcode, hdiv, htd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    ?_, ?_⟩
  · simp only [WordSemStateFiniteExact.setStore]
    change arrayRel s.arrays (FUPDATE_HOL t.store.lookup (_, v) tempIn1)
      (FUPDATE_HOL t.store.lookup (_, v) tempIn2) (FUPDATE_HOL t.store.lookup (_, v) tempOut)
      t.memory t.mdomain frame
    simp only [FUPDATE_HOL]
    rw [if_neg hIn1, if_neg hIn2, if_neg hOut]
    exact ha
  · intro a w hw
    obtain ⟨ha25, hl⟩ := hr a w hw
    refine ⟨ha25, ?_⟩
    rw [store_setStore, if_neg (hne a (by omega) (by omega))]
    exact hl
  · rw [store_setStore, if_neg hOut]
    exact h13
  · intro n hn
    rw [store_setStore, if_neg (hn _)]
    exact h14 n hn

/-- The value a register-or-immediate operand contributes when copied by
`SeqTempImm`. -/
def riStoreValue (t : WordSemStateFiniteExact width C F) :
    WordRegImm (BitVec width) → Option (WordLocW width)
  | .reg r => t.store.lookup (.temp (BitVec.ofNat 5 r))
  | .imm w => some (.word w)

theorem ev_seqTempImm {t : WordSemStateFiniteExact width C F} {k : Nat}
    {ri : WordRegImm (BitVec width)} {v : WordLocW width} {x : WordLangProgHOL (BitVec width)}
    {res : Option (WordSemResult width) × WordSemStateFiniteExact width C F}
    (h : riStoreValue t ri = some v)
    (hx : WordSemStateFiniteExact.evaluate x (WordSemStateFiniteExact.setVar k v t) = res) :
    WordSemStateFiniteExact.evaluate (seqTempImm k ri x) t = res := by
  cases ri with
  | reg r => exact ev_seqTemp h hx
  | imm w =>
    simp only [riStoreValue, Option.some.injEq] at h
    subst h
    exact ev_seq (ev_assign (by simp [WordSemStateFiniteExact.wordExp])) hx

theorem ev_seqTempImmNot {t : WordSemStateFiniteExact width C F} {k : Nat}
    {ri : WordRegImm (BitVec width)} {w : BitVec width} {x : WordLangProgHOL (BitVec width)}
    {res : Option (WordSemResult width) × WordSemStateFiniteExact width C F}
    (h : riStoreValue t ri = some (.word w))
    (hx : WordSemStateFiniteExact.evaluate x
      (WordSemStateFiniteExact.setVar k (.word (~~~w)) t) = res) :
    WordSemStateFiniteExact.evaluate (seqTempImmNot k ri x) t = res := by
  cases ri with
  | reg r =>
    refine ev_seqTemp h (ev_seq (ev_assign (v := .word (~~~w)) ?_) ?_)
    · simp [WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.getVar,
        WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same, theWords, wordOpHOL, wordOp]
    · simpa [WordSemStateFiniteExact.setVar, sptInsert_insert_shadow] using hx
  | imm w' =>
    simp only [riStoreValue, Option.some.injEq, WordLocW.word.injEq] at h
    subst h
    exact ev_seq (ev_assign (by simp [WordSemStateFiniteExact.wordExp])) hx

theorem wordAddCarry_eq_singleAddWord (x y c : BitVec width) :
    wordAddCarryHOL x y c = Misc.Multiword.singleAddWord x y c := by
  simp only [wordAddCarryHOL, Misc.Multiword.singleAddWord, Misc.Multiword.singleAdd,
    Misc.Multiword.b2w, Misc.Multiword.b2n]
  by_cases hc : c = 0
  · subst hc
    simp only [beq_self_eq_true, if_true, ne_eq, not_true_eq_false, decide_false]
    refine Prod.ext ?_ ?_
    · apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    · by_cases h2 : 2 ^ width ≤ x.toNat + y.toNat <;> simp [h2]
  · have hb : (c == 0) = false := by simpa using hc
    simp only [hb, Bool.false_eq_true, if_false, ne_eq, hc, not_false_eq_true, decide_true]
    refine Prod.ext ?_ ?_
    · apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    · by_cases h2 : 2 ^ width ≤ x.toNat + y.toNat + 1 <;> simp [h2]

theorem cutEnvs_loop {l : Spt (WordLocW width)} {v : WordLocW width}
    (h : sptLookup 0 l = some v) :
    wordSemCutEnvs (.ls (), .ln) l = some (.ls v, .ln) := by
  have hsub : LoopSemStateFiniteExact.sptSubsetLive (Spt.ls ()) l := by
    intro k hk
    have hk0 : k = 0 := by
      by_contra hne
      simp [sptMem, sptDomain, sptLookup, hne] at hk
    subst hk0
    simp [sptMem, sptDomain, h]
  have hsub2 : LoopSemStateFiniteExact.sptSubsetLive (Spt.ln : Spt Unit) l := by
    intro k hk
    simp [sptMem, sptDomain, sptLookup] at hk
  have hinter : sptInter l (Spt.ls ()) = .ls v := by
    cases l with
    | ln => simp [sptLookup] at h
    | ls a => simp [sptLookup] at h; subst h; simp [sptInter]
    | bn a b => simp [sptLookup] at h
    | bs a b c => simp [sptLookup] at h; subst h; simp [sptInter]
  have hinter2 : sptInter l (Spt.ln : Spt Unit) = .ln := by
    cases l <;> simp [sptInter]
  simp only [wordSemCutEnvs, wordSemCutNames, if_pos hsub, if_pos hsub2, hinter, hinter2]

theorem envToList_ln (p : Nat → Nat → Nat) :
    wordSemEnvToList (.ln : Spt (WordLocW width)) p = ([], fun n => p (n + 1)) := by
  simp [wordSemEnvToList, sptToAList, sptFoldi, Basis.Pure.MlList.sort,
    Basis.Pure.MlList.mergesortTail, Basis.Pure.MlList.mergesortNTail, wordSemListRearrange]

theorem sptToAList_ls (v : WordLocW width) : sptToAList (.ls v) = [(0, v)] := by
  simp [sptToAList, sptFoldi]

/-- The state after a compiled loop call returns. -/
def loopFrame (t : WordSemStateFiniteExact width C F) (i n l : Nat) (retVal : WordLocW width)
    (st : List (WordSemStackFrame width)) (ls : Option Nat) : WordSemStateFiniteExact width C F :=
  { t with locals := sptInsert i (.loc n l) (.ls retVal), stack := st, localsSize := ls }

theorem evaluate_return_loc {t : WordSemStateFiniteExact width C F} {n l : Nat}
    (h : WordSemStateFiniteExact.getVar 0 t = some (.loc n l)) :
    WordSemStateFiniteExact.evaluate (.return 0 [0]) t =
      (some (.result (.loc n l) [.loc n l]), WordSemStateFiniteExact.flushState false t) := by
  rw [evaluate_return]
  simp [h, WordSemStateFiniteExact.getVars]

/-- One compiled loop call: the callee runs from the pushed frame, returns
through `Return 0 [0]`, and the frame is popped. -/
theorem evaluate_loopCall {t1 t2' : WordSemStateFiniteExact width C F} {i y n l : Nat}
    {p1' p9 : WordLangProgHOL (BitVec width)} {retVal : WordLocW width}
    (_hi : 0 < i) (hret : WordSemStateFiniteExact.getVar 0 t1 = some retVal)
    (hlook : sptLookup y t1.code = some (1, .seq p1' (.return 0 [0])))
    (hclock : t1.clock ≠ 0)
    (hbody : WordSemStateFiniteExact.evaluate (.seq p1' (.return 0 [0]))
        (WordSemStateFiniteExact.callEnv [.loc n l] (sptLookup y t1.stackSize)
          (WordSemStateFiniteExact.pushEnv (.ls retVal, .ln) none
            (WordSemStateFiniteExact.decClock t1))) =
      WordSemStateFiniteExact.evaluate (.return 0 [0]) t2')
    (hret2 : WordSemStateFiniteExact.getVar 0 t2' = some (.loc n l))
    (hst2 : t2'.stack = (WordSemStateFiniteExact.callEnv [.loc n l] (sptLookup y t1.stackSize)
          (WordSemStateFiniteExact.pushEnv (.ls retVal, .ln) none
            (WordSemStateFiniteExact.decClock t1))).stack) :
    WordSemStateFiniteExact.evaluate
        (.seq (.call (some ([i], (.ls (), .ln), .skip, n, l)) (some y) [] none) p9) t1 =
      WordSemStateFiniteExact.evaluate p9 (loopFrame t2' i n l retVal t1.stack t1.localsSize) := by
  apply evaluate_seq_of_none
  rw [evaluate_call]
  have hcut := cutEnvs_loop (v := retVal) hret
  have hdom : ¬ (sptDomainEmpty (Spt.ls ()) ∨ ¬ [i].Nodup) := by
    simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self,
      not_true_eq_false, or_false]
    intro h
    exact h 0 (by simp [sptMem, sptDomain, sptLookup])
  simp only [WordSemStateFiniteExact.getVars, wordSemBadDestArgs, Bool.false_eq_true, if_false,
    wordSemAddRetLoc, wordSemFindCode, hlook, List.length_singleton, if_true]
  rw [if_neg hdom, hcut]
  simp only [hclock, if_false]
  rw [hbody, evaluate_return_loc hret2]
  simp only [ne_eq, not_true_eq_false, List.length_singleton, or_self, if_false]
  have hpop : WordSemStateFiniteExact.popEnv (WordSemStateFiniteExact.flushState false t2') =
      some { WordSemStateFiniteExact.flushState false t2' with
        locals := sptUnion (sptFromAList []) (sptFromAList [(0, retVal)]),
        stack := t1.stack, localsSize := t1.localsSize } := by
    simp only [WordSemStateFiniteExact.popEnv, WordSemStateFiniteExact.flushState, hst2,
      WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.pushEnv, sptToAList_ls,
      envToList_ln, WordSemStateFiniteExact.decClock]
  rw [hpop]
  simp only
  have hunion : sptUnion (sptFromAList ([] : List (Nat × WordLocW width)))
      (sptFromAList [(0, retVal)]) = .ls retVal := by
    simp [sptFromAList, sptUnion]
  rw [hunion]
  have hdeq : sptDomainEqUnion (Spt.ls retVal) (Spt.ls retVal) (Spt.ln : Spt (WordLocW width)) := by
    intro k
    simp [sptMem, sptDomain, sptLookup]
  rw [if_pos hdeq, evaluate_skip]
  rfl

theorem getVar_zero_loopFrame (t : WordSemStateFiniteExact width C F) {i n l : Nat} (hi : 0 < i)
    (retVal : WordLocW width) (st : List (WordSemStackFrame width)) (ls : Option Nat) :
    WordSemStateFiniteExact.getVar 0 (loopFrame t i n l retVal st ls) = some retVal := by
  show sptLookup 0 (sptInsert i (.loc n l) (.ls retVal)) = some retVal
  rw [sptLookup_sptInsert_ne i 0 _ _ (by omega)]
  rfl

theorem forall₂_imp_mem {α γ : Type} {R S : α → γ → Prop} :
    ∀ {xs : List α} {ys : List γ}, List.Forall₂ R xs ys →
      (∀ x y, x ∈ xs → R x y → S x y) → List.Forall₂ S xs ys
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons hr hrest, h =>
    .cons (h _ _ List.mem_cons_self hr)
      (forall₂_imp_mem hrest (fun x y hx => h x y (List.mem_cons_of_mem _ hx)))

/-- The saved registers are readable at their shifted locals after
`list_update`. -/
theorem listUpdate_lookup_saved {L : Spt (WordLocW width)} :
    ∀ {save : List Nat} {vals : List (BitVec width)} {P : Nat → BitVec width → Prop},
      List.Forall₂ P save vals → save.Nodup →
      List.Forall₂ (fun n v => sptLookup (n + 2)
        (listUpdateSpt (save.map (fun n => n + 2)) (vals.map WordLocW.word) L) = some (.word v))
        save vals
  | [], [], _, .nil, _ => .nil
  | h :: save, v :: vals, P, .cons _ hrest, hnd => by
    have ih := listUpdate_lookup_saved (L := L) hrest (List.nodup_cons.mp hnd).2
    refine .cons ?_ ?_
    · simp [listUpdateSpt, sptLookup_sptInsert_same]
    · refine forall₂_imp_mem ih ?_
      intro n w hmem hl
      simp only [List.map_cons, listUpdateSpt]
      rw [sptLookup_sptInsert_ne _ _ _ _ (by
        intro he
        have : n = h := by omega
        exact (List.nodup_cons.mp hnd).1 (this ▸ hmem))]
      exact hl

theorem cutNames_ls {l : Spt (WordLocW width)} {v : WordLocW width}
    (h : sptLookup 0 l = some v) :
    wordSemCutNames (Spt.ls ()) l = some (.ls v) := by
  have hcut := cutEnvs_loop h
  simp only [wordSemCutEnvs] at hcut
  cases hc : wordSemCutNames (Spt.ls ()) l with
  | none => simp [hc] at hcut
  | some e => rw [hc] at hcut; cases hcl : wordSemCutNames (Spt.ln : Spt Unit) l <;> simp_all

/-- Restoring the saved registers into the temporaries matches HOL's
`copy_vars` on the register file. -/
theorem copyVars_listStore_rel :
    ∀ (save : List Nat) (regs : HolFiniteMapExact Nat (BitVec width)) (s2 s3 : MiniState width)
      (vals : List (BitVec width)) (st : HolFiniteMapExact WordStoreHOL (WordLocW width)),
      copyVars save regs s2 = some s3 →
      List.Forall₂ (fun n v => regs.lookup n = some v) save vals → save.Nodup →
      (∀ n ∈ save, n < 25) →
      (∀ a v, s2.regs.lookup a = some v →
        a < 25 ∧ st.lookup (.temp (BitVec.ofNat 5 a)) = some (.word v)) →
      ∀ a v, s3.regs.lookup a = some v →
        a < 25 ∧ (listStore save (vals.map WordLocW.word) st).lookup
          (.temp (BitVec.ofNat 5 a)) = some (.word v)
  | [], regs, s2, s3, vals, st, hcopy, hrel, _, _, hst => by
    cases hrel
    simp only [copyVars, Option.some.injEq] at hcopy
    subst hcopy
    exact hst
  | h :: rest, regs, s2, s3, vals, st, hcopy, hrel, hnd, hlt, hst => by
    cases hrel with
    | cons hv hrest =>
      rename_i v vs
      simp only [copyVars, hv] at hcopy
      have hh : h < 25 := hlt h List.mem_cons_self
      have hlt' : ∀ n ∈ rest, n < 25 := fun n hn => hlt n (List.mem_cons_of_mem _ hn)
      have hnotin : h ∉ rest := (List.nodup_cons.mp hnd).1
      have ih := copyVars_listStore_rel rest regs (regWrite h (some v) s2) s3 vs
        (st.updateEq (.temp (BitVec.ofNat 5 h), .word v)) hcopy hrest (List.nodup_cons.mp hnd).2
        hlt' (by
          intro a w hw
          change FUPDATE_HOL s2.regs.lookup (h, v) a = some w at hw
          simp only [FUPDATE_HOL] at hw
          by_cases hah : a = h
          · subst hah
            simp only [if_true, Option.some.injEq] at hw
            subst hw
            exact ⟨hh, by simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]⟩
          · rw [if_neg hah] at hw
            obtain ⟨ha25, hl⟩ := hst a w hw
            refine ⟨ha25, ?_⟩
            change FUPDATE_HOL st.lookup (_, _) _ = _
            simp only [FUPDATE_HOL]
            rw [if_neg (fun he => hah (temp_ofNat_inj (by omega) (by omega) he))]
            exact hl)
      intro a w hw
      obtain ⟨ha25, hl⟩ := ih a w hw
      refine ⟨ha25, ?_⟩
      rw [listStore_FUPDATE rest st (vs.map WordLocW.word) h v ⟨hnotin, hh, hlt'⟩] at hl
      simpa [listStore, holHd] using hl

end Flapjack.Compiler.Backend.WordBignum.CompileThmSupport
