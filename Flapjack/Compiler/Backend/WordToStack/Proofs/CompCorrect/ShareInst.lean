import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadRegisterTwo
import Flapjack.Compiler.Backend.WordToStack.Proofs.LoadContinuations
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelGetVar
import Flapjack.Compiler.Backend.WordToStack.Proofs.StateRelRegisterUpdate
import Flapjack.Compiler.Backend.WordToStack.NativeSharedMemory
import Flapjack.Misc.Option

/-!
# Word-to-Stack `comp_correct`: the `ShareInst` case

`word_to_stackProofScript.sml:7166-7545`, with `word_exp_Op_SOME_Word` (4396).
A shared-memory instruction's address is a variable or a variable plus a
constant; the address register is loaded by `wReg1`, a load writes its result
through `wRegWrite1`, and a store loads its value register by `wReg2`.
Shared-memory accesses are FFI calls, so both sides may end in `FinalFFI`.
-/

namespace Flapjack.WordToStackProofs.CompCorrect.ShareInst
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Genuine canonical source codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_WordSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Genuine canonical target codec re-export for the relation qualifier. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- HOL `word_exp_Op_SOME_Word` (4396-4400): an operator expression evaluates
only to a word. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_exp_Op_SOME_Word"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem wordExpOpSomeWord {width : Nat} [NeZero width] {C F : Type}
    {s : WordSemStateFiniteExact width C F} {op : BinOp}
    {wexps : List (WordLangExpHOL (BitVec width))} {x : WordLocW width} :
    WordSemStateFiniteExact.wordExp s (.op op wexps) = some x → ∃ w, x = .word w := by
  intro h
  simp only [WordSemStateFiniteExact.wordExp] at h
  split at h
  · obtain ⟨w, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨w, rfl⟩
  · cases h

/-- HOL `flat_exp_conventions_ShareInst_exp_simp` (7166-7173). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "flat_exp_conventions_ShareInst_exp_simp" (words_as_type_indexed_bitvec)]
theorem flatExpConventionsShareInstExpSimp {width : Nat} [NeZero width]
    {op : WordMemOp} {v : Nat} {exp : WordLangExpHOL (BitVec width)} :
    flatExpConventions (.shareInst op v exp : WordLangProgHOL (BitVec width)) = true →
      (∃ ad, exp = .var ad) ∨ (∃ ad offset, exp = .op .add [.var ad, .const offset]) := by
  intro h
  unfold flatExpConventions at h
  split at h <;> simp_all

/-- HOL `word_exp_Op_Add_0` (7175-7184). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "word_exp_Op_Add_0"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem wordExpOpAdd0 {width : Nat} [NeZero width] {C F : Type}
    {s : WordSemStateFiniteExact width C F} {exp : WordLangExpHOL (BitVec width)}
    {x : BitVec width} :
    WordSemStateFiniteExact.wordExp s exp = some (.word x) ↔
      WordSemStateFiniteExact.wordExp s (.op .add [exp, .const 0]) = some (.word x) := by
  rcases h : WordSemStateFiniteExact.wordExp s exp with _ | (w | ⟨a, b⟩) <;>
    simp [WordSemStateFiniteExact.wordExp, h, theWords, wordOpHOL, wordOp]

/-- HOL `evaluate_ShareInst_Var_eq_Op_Add` (7186-7205): a bare variable
address behaves as that variable plus zero. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "evaluate_ShareInst_Var_eq_Op_Add"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem evaluateShareInstVarEqOpAdd {width : Nat} [NeZero width] {C F : Type}
    {op : WordMemOp} {v ad : Nat} {s : WordSemStateFiniteExact width C F} :
    WordSemStateFiniteExact.evaluate (.shareInst op v (.var ad)) s =
      WordSemStateFiniteExact.evaluate (.shareInst op v (.op .add [.var ad, .const 0])) s := by
  simp only [WordSemStateFiniteExact.evaluate]
  rcases hv : WordSemStateFiniteExact.wordExp s (.var ad) with _ | (w | ⟨a, b⟩)
  · rcases ho : WordSemStateFiniteExact.wordExp s (.op .add [.var ad, .const 0]) with
      _ | (w' | ⟨a', b'⟩)
    · rfl
    · exact absurd (wordExpOpAdd0.mpr ho) (by simp [hv])
    · rfl
  · rw [wordExpOpAdd0.mp hv]
  · rcases ho : WordSemStateFiniteExact.wordExp s (.op .add [.var ad, .const 0]) with
      _ | (w' | ⟨a', b'⟩)
    · rfl
    · exact absurd (wordExpOpAdd0.mpr ho) (by simp [hv])
    · rfl

/-- Installing the same FFI state on both sides preserves the relation.
Flapjack infrastructure; no separate HOL declaration. -/
theorem stateRelFfi {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat}
    {source : WordSemStateFiniteExact width (Nat × C) F}
    {target : StackSemStateFiniteExact width C F} {lens : List Nat} {extra : Nat}
    (newFfi : HolFfiState F) (related : stateRel ac k f frame source target lens extra) :
    stateRel ac k f frame { source with ffi := newFfi } { target with ffi := newFfi }
      lens extra := by
  unfold stateRel at related ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38,hloc⟩ := related
  exact ⟨h1,h2,h3,rfl,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,rfl,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38,hloc⟩

/-- HOL `share_load_lemma2` (7254-7296): a shared-memory load into a
register-placed variable. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_load_lemma2"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem shareLoadLemma2 {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v : Nat}
    {ad' : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.shareInst op (2 * v) ad' s = (res, s1) ∧
      stateRel ac k f frame s t lens 0 ∧ v < k ∧
      (op = .load ∨ op = .load8 ∨ op = .load16 ∨ op = .load32) ∧ res ≠ some .error →
    ∃ t1, StackSemShMem.shMemOp op v ad' t = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  rintro ⟨hrun, related, hv, hop, notError⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, r4, -, -, -, -, -, -, r11, -⟩ := related'
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [WordSemStateFiniteExact.shareInst, WordSemStateFiniteExact.shMemSetVar,
      WordSemStateFiniteExact.shMemLoad, WordSemStateFiniteExact.shMemLoadByte,
      WordSemStateFiniteExact.shMemLoad16, WordSemStateFiniteExact.shMemLoad32] at hrun <;>
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad, StackSemShMem.shMemLoadByte,
      StackSemShMem.shMemLoad16, StackSemShMem.shMemLoad32, r4]
  all_goals
    rw [← r11] at hrun
    split
    · rename_i hD
      split
      · rename_i o hc
        simp only [hD, if_true, hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inl ⟨_, rfl, r4.symm, r1⟩⟩
      · rename_i nf nb hc
        simp only [hD, if_true, hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inr ⟨rfl,
          StateRelRegisterUpdate.stateRelSetVar v _ (stateRelFfi _ related) hv⟩⟩
    · rename_i hD
      simp only [hD, Bool.false_eq_true, if_false, Prod.mk.injEq] at hrun
      exact absurd hrun.1.symm notError

/-- HOL `share_load_lemma1` (7207-7252): a shared-memory load into a
stack-placed variable, through the scratch register `k`. HOL's `LUPDATE` is
`List.set` and `THE` is `holThe`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_load_lemma1"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem shareLoadLemma1 {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v : Nat}
    {ad' : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.shareInst op (2 * v) ad' s = (res, s1) ∧
      stateRel ac k f frame s t lens 0 ∧ v < frame + k ∧ k ≤ v ∧
      (op = .load ∨ op = .load8 ∨ op = .load16 ∨ op = .load32) ∧ res ≠ some .error →
    ∃ t1, StackSemShMem.shMemOp op k ad' t = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧
          stateRel ac k f frame s1
            { t1 with stack := (t1.stack.set (t1.stackSpace + (f + k - (v + 1)))
                (Flapjack.holThe (t1.regs.lookup k))) } lens 0 ∧
          (∃ x, t1.regs.lookup k = some x) ∧ t1.stackSpace = t.stackSpace ∧
          t1.stack.length = t.stack.length)) := by
  rintro ⟨hrun, related, hbound, hk, hop, notError⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, r4, -, -, -, -, -, -, r11, -⟩ := related'
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [WordSemStateFiniteExact.shareInst, WordSemStateFiniteExact.shMemSetVar,
      WordSemStateFiniteExact.shMemLoad, WordSemStateFiniteExact.shMemLoadByte,
      WordSemStateFiniteExact.shMemLoad16, WordSemStateFiniteExact.shMemLoad32] at hrun <;>
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemLoad, StackSemShMem.shMemLoadByte,
      StackSemShMem.shMemLoad16, StackSemShMem.shMemLoad32, r4]
  all_goals
    rw [← r11] at hrun
    split
    · rename_i hD
      split
      · rename_i o hc
        simp only [hD, if_true, hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inl ⟨_, rfl, r4.symm, r1⟩⟩
      · rename_i nf nb hc
        simp only [hD, if_true, hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        refine ⟨_, rfl, .inr ⟨rfl, ?_, ⟨.word (panWordOfBytesHOL false 0 nb),
          by simp [HolFiniteMapExact.updateEq, FUPDATE_HOL]⟩,
          rfl, rfl⟩⟩
        have base := StateRelRegisterUpdate.wordToStackStateRelSetVar2 v
          (.word (panWordOfBytesHOL false 0 nb)) _ _ (stateRelFfi nf related)
          (by omega) hbound rfl rfl
        have := (StateRelRegisterUpdate.stateRelSetVarHigh (ac := ac) (f := f) (frame := frame)
          (lens := lens) (extra := 0) k (.word (panWordOfBytesHOL false 0 nb))
          (Nat.le_refl k)).mpr base
        simpa [StackSemStateOps.setVar, HolFiniteMapExact.updateEq, FUPDATE_HOL,
          Flapjack.holThe] using this
    · rename_i hD
      simp only [hD, Bool.false_eq_true, if_false, Prod.mk.injEq] at hrun
      exact absurd hrun.1.symm notError

/-- HOL `share_store_lemma2` (7348-7384): a shared-memory store of a
register-placed variable. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_store_lemma2"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem shareStoreLemma2 {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v : Nat}
    {ad' : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.shareInst op (2 * v) ad' s = (res, s1) ∧
      stateRel ac k f frame s t lens 0 ∧ v < k ∧
      (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) ∧ res ≠ some .error →
    ∃ t1, StackSemShMem.shMemOp op v ad' t = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  rintro ⟨hrun, related, hv, hop, notError⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, r4, -, -, -, -, -, -, r11, -⟩ := related'
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [WordSemStateFiniteExact.shareInst] at hrun <;>
    rcases hw : WordSemStateFiniteExact.getVar (2 * v) s with _ | (w | ⟨a, b⟩) <;>
    simp only [hw, Prod.mk.injEq] at hrun <;>
    try exact absurd hrun.1.symm notError
  all_goals
    have hget : StackSemStateOps.getVar v t = some (.word w) := by
      have := StateRelGetVar.stateRelGetVarImp' ac k f frame s t lens 0 (2 * v) _
        ⟨related, hw, by omega, by omega⟩
      rwa [show 2 * v / 2 = v by omega] at this
    simp only [WordSemStateFiniteExact.shMemStore, WordSemStateFiniteExact.shMemStoreByte,
      WordSemStateFiniteExact.shMemStore16, WordSemStateFiniteExact.shMemStore32] at hrun
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore, StackSemShMem.shMemStoreByte,
      StackSemShMem.shMemStore16, StackSemShMem.shMemStore32, hget, r4]
    split
    · rename_i hD
      rw [r11] at hD
      simp only [hD, if_true] at hrun
      split
      · rename_i o hc
        simp only [hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inl ⟨_, rfl, r4.symm, r1⟩⟩
      · rename_i nf nb hc
        simp only [hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inr ⟨rfl, stateRelFfi nf related⟩⟩
    · rename_i hD
      rw [r11] at hD
      simp only [hD, Bool.false_eq_true, if_false, Prod.mk.injEq] at hrun
      exact absurd hrun.1.symm notError

/-- HOL `share_store_lemma1` (7298-7346): a shared-memory store of a
stack-placed variable, whose value is first copied from its stack slot into the
scratch register `k+1`. HOL's `EL` is `holEl` and `|+` is `updateEq`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "share_store_lemma1"
  (fmap_as_finite_support_relation := [WordSemStateFiniteExact.fpRegs,
    WordSemStateFiniteExact.store, StackSemStateFiniteExact.regs,
    StackSemStateFiniteExact.fpRegs, StackSemStateFiniteExact.store])
  (words_as_type_indexed_bitvec)]
theorem shareStoreLemma1 {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v : Nat}
    {ad' : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.shareInst op (2 * v) ad' s = (res, s1) ∧
      stateRel ac k f frame s t lens 0 ∧ ¬ v < k ∧
      (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) ∧ res ≠ some .error →
    ∃ t1, StackSemShMem.shMemOp op (k + 1) ad'
        { t with regs := (t.regs.updateEq
            (k + 1, Flapjack.holEl (t.stackSpace + (f + k - (v + 1))) t.stack)) } =
        (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  rintro ⟨hrun, related, hv, hop, notError⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, r4, -, -, -, -, -, -, r11, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, r35, -, -, -, rloc⟩ := related'
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [WordSemStateFiniteExact.shareInst] at hrun <;>
    rcases hw : WordSemStateFiniteExact.getVar (2 * v) s with _ | (w | ⟨a, b⟩) <;>
    simp only [hw, Prod.mk.injEq] at hrun <;>
    try exact absurd hrun.1.symm notError
  all_goals
    have hel : Flapjack.holEl (t.stackSpace + (f + k - (v + 1))) t.stack = .word w := by
      obtain ⟨-, hplace⟩ := rloc (2 * v) (.word w) hw
      rw [if_neg (by omega)] at hplace
      obtain ⟨hslot, hlt⟩ := hplace
      have hf : f = frame + 1 := by split at r35 <;> omega
      have hidx : f - 1 - (2 * v / 2 - k) = f + k - (v + 1) := by omega
      rw [hidx] at hslot
      simp only [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at hslot
      split at hslot
      · rename_i hin
        obtain ⟨hlen, hval⟩ := List.getElem?_eq_some_iff.mp hslot
        rw [Flapjack.holEl_eq_getElem _ _ hlen, hval]
      · cases hslot
    have hget : StackSemStateOps.getVar (k + 1)
        { t with regs := (t.regs.updateEq
            (k + 1, Flapjack.holEl (t.stackSpace + (f + k - (v + 1))) t.stack)) } =
        some (.word w) := by
      simp [StackSemStateOps.getVar, HolFiniteMapExact.updateEq, FUPDATE_HOL, hel]
    simp only [WordSemStateFiniteExact.shMemStore, WordSemStateFiniteExact.shMemStoreByte,
      WordSemStateFiniteExact.shMemStore16, WordSemStateFiniteExact.shMemStore32] at hrun
    simp only [StackSemShMem.shMemOp, StackSemShMem.shMemStore, StackSemShMem.shMemStoreByte,
      StackSemShMem.shMemStore16, StackSemShMem.shMemStore32, hget]
    simp only [r4]
    split
    · rename_i hD
      rw [r11] at hD
      simp only [hD, if_true] at hrun
      split
      · rename_i o hc
        simp only [hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, rfl, .inl ⟨_, rfl, rfl, r1⟩⟩
      · rename_i nf nb hc
        simp only [hc, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        refine ⟨_, rfl, .inr ⟨rfl, ?_⟩⟩
        exact (StateRelRegisterUpdate.stateRelSetVarHigh (k + 1) _ (by omega)).mpr
          (stateRelFfi nf related)
    · rename_i hD
      rw [r11] at hD
      simp only [hD, Bool.false_eq_true, if_false, Prod.mk.injEq] at hrun
      exact absurd hrun.1.symm notError

end Flapjack.WordToStackProofs.CompCorrect.ShareInst
