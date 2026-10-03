import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.WordInst.Proofs.ThreeToTwo
import Flapjack.Misc.SptreeLookup

/-!
# `word_cseProof`: evaluation transport facts

Counterpart of the evaluation lemmas of
`cakeml/compiler/backend/proofs/word_cseProofScript.sml` (167-421, 521-553):
a CSE-storable arithmetic instruction or a load succeeds with a single
`set_var` of a value determined by the registers it reads (and, for a load,
the memory fields), so its evaluation equation transports across writes to
other registers and across agreeing states. Statements use the faithful wordSem
`evaluate` over `WordSemStateFiniteExact`, with the CSE `HolArith` instruction
embedded by the reviewed constructor codec `toWordLangArith` (the convention of
`semInv`) and `HolMemop` the reviewed alias of `WordMemOp`.
-/

namespace Flapjack

namespace WordCseEvaluateFactsSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordCseEvaluateFactsSupport

namespace Compiler.Backend.WordCse

open WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordInst

section Helpers

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- The value a CSE-storable arithmetic instruction writes to its first
    register (Flapjack infrastructure). -/
def arithValue : HolArith width → WordSemStateFiniteExact width C F → Option (WordLocW width)
  | .binop op _ r2 ri, s =>
      wordExp s (.op op [.var r2, match ri.toWordRegImm with | .reg r3 => .var r3 | .imm w => .const w])
  | .shift sh _ r2 ri, s =>
      wordExp s (.shift sh (.var r2) (match ri.toWordRegImm with | .reg r3 => .var r3 | .imm w => .const w))
  | .div _ r2 r3, s =>
      match WordSemStateFiniteExact.getVars [r3, r2] s with
      | some [.word q, .word w2] => if q ≠ 0 then some (.word (w2.sdiv q)) else none
      | _ => none
  | _, _ => none

/-- The value a load writes to its destination (Flapjack infrastructure). -/
def loadValue (op : HolMemop) (a : Nat) (ofs : BitVec width) (s : WordSemStateFiniteExact width C F) :
    Option (WordLocW width) :=
  match op with
  | .load =>
      match wordExp s (.op .add [.var a, .const ofs]) with
      | some (.word w) => memLoad w s
      | _ => none
  | .load8 =>
      match wordExp s (.op .add [.var a, .const ofs]) with
      | some (.word w) =>
          (memLoadByteAuxExact s.memory s.mdomain s.be w).map (fun b => .word (b.setWidth width))
      | _ => none
  | .load32 =>
      match wordExp s (.op .add [.var a, .const ofs]) with
      | some (.word w) =>
          (memLoad32Exact s.memory s.mdomain s.be w).map (fun b => .word (b.setWidth width))
      | _ => none
  | _ => none

theorem inst_arith_shape (a : HolArith width) (hc : canMemArith a = true)
    (s : WordSemStateFiniteExact width C F) :
    inst (.arith a.toWordLangArith) s = (arithValue a s).map (fun v => setVar (firstRegOfArith a) v s) := by
  cases a <;> simp only [canMemArith, Bool.false_eq_true] at hc
  all_goals
    simp only [inst, assign, HolArith.toWordLangArith, arithValue, firstRegOfArith]
    repeat' split
  all_goals first | rfl | simp_all

theorem inst_load_shape (op : HolMemop) (hs : isStore op = false) (r a : Nat) (ofs : BitVec width)
    (s : WordSemStateFiniteExact width C F) :
    inst (.mem op r (.addr a ofs)) s = (loadValue op a ofs s).map (fun v => setVar r v s) := by
  cases op <;> simp only [isStore, Bool.true_eq_false] at hs
  all_goals
    simp only [inst, loadValue]
    repeat' split
  all_goals first | rfl | simp_all

theorem getVars_two_congr (s t : WordSemStateFiniteExact width C F) (x y : Nat)
    (hx : getVar x t = getVar x s) (hy : getVar y t = getVar y s) :
    WordSemStateFiniteExact.getVars [x, y] t = WordSemStateFiniteExact.getVars [x, y] s := by
  simp only [WordSemStateFiniteExact.getVars, hx, hy]

theorem arithValue_congr (a : HolArith width) (hc : canMemArith a = true)
    (s t : WordSemStateFiniteExact width C F)
    (hr : ∀ x ∈ arithReads a, getVar x t = getVar x s) :
    arithValue a t = arithValue a s := by
  have hv : ∀ x ∈ arithReads a, wordExp t (.var x) = wordExp s (.var x) := fun x hx => by
    rw [wordExp, wordExp]; exact hr x hx
  have hk : ∀ w : BitVec width, wordExp t (.const w) = wordExp s (.const w) := fun w => by
    rw [wordExp, wordExp]
  cases a with
  | binop op d r2 ri =>
    cases ri with
    | reg r3 =>
      exact wordExp_op2_congr t s op _ _ _ _ (hv r2 (by simp [arithReads]))
        (hv r3 (by simp [arithReads]))
    | imm w => exact wordExp_op2_congr t s op _ _ _ _ (hv r2 (by simp [arithReads])) (hk w)
  | shift sh d r2 ri =>
    cases ri with
    | reg r3 => simp [canMemArith] at hc
    | imm w =>
      exact wordExp_shift_congr t s sh _ _ _ _ (hv r2 (by simp [arithReads])) (hk w)
  | div d r2 r3 =>
    simp only [arithValue, getVars_two_congr s t r3 r2 (hr r3 (by simp [arithReads]))
      (hr r2 (by simp [arithReads]))]
  | _ => simp [canMemArith] at hc

theorem loadValue_congr (op : HolMemop) (a : Nat) (ofs : BitVec width)
    (s t : WordSemStateFiniteExact width C F) (ha : getVar a t = getVar a s)
    (hm : t.memory = s.memory) (hd : t.mdomain = s.mdomain) (hb : t.be = s.be) :
    loadValue op a ofs t = loadValue op a ofs s := by
  have hv : wordExp t (.var a) = wordExp s (.var a) := by rw [wordExp, wordExp]; exact ha
  have hk : wordExp t (.const ofs) = wordExp s (.const ofs) := by rw [wordExp, wordExp]
  have he : wordExp t (.op .add [.var a, .const ofs]) = wordExp s (.op .add [.var a, .const ofs]) :=
    wordExp_op2_congr t s .add _ _ _ _ hv hk
  cases op <;> simp only [loadValue, he, memLoad, hm, hd, hb]

theorem setVar_inj (d : Nat) (v w : WordLocW width) (s : WordSemStateFiniteExact width C F) :
    setVar d v s = setVar d w s ↔ v = w := by
  constructor
  · intro h
    have := congrArg (fun t => sptLookup d t.locals) h
    simpa [setVar, sptLookup_sptInsert_same] using this
  · rintro rfl; rfl

theorem evaluate_arith_iff (a : HolArith width) (hc : canMemArith a = true) (w : WordLocW width)
    (s : WordSemStateFiniteExact width C F) :
    evaluate (.inst (.arith a.toWordLangArith)) s = (none, setVar (firstRegOfArith a) w s) ↔
      arithValue a s = some w := by
  rw [evaluate_inst_eq, inst_arith_shape a hc]
  cases arithValue a s with
  | none => simp
  | some v => simp [setVar_inj, eq_comm]

theorem evaluate_load_iff (op : HolMemop) (hs : isStore op = false) (r a : Nat) (ofs : BitVec width)
    (w : WordLocW width) (s : WordSemStateFiniteExact width C F) :
    evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s) ↔
      loadValue op a ofs s = some w := by
  rw [evaluate_inst_eq, inst_load_shape op hs]
  cases loadValue op a ofs s with
  | none => simp
  | some v => simp [setVar_inj, eq_comm]

theorem getVar_setVar_ne (s : WordSemStateFiniteExact width C F) (r x : Nat) (u : WordLocW width)
    (h : x ≠ r) : getVar x (setVar r u s) = getVar x s := by
  simp only [getVar, setVar, sptLookup_sptInsert_ne _ _ _ _ h]

theorem getVar_unsetVar_ne (s : WordSemStateFiniteExact width C F) (r x : Nat)
    (h : x ≠ r) : getVar x (unsetVar r s) = getVar x s := by
  simp only [getVar, unsetVar, sptLookup_sptDelete, h, if_false]

end Helpers

/-- Exact HOL `insert_eq` (`word_cseProof:167-171`); the unused `n2` binder of
    HOL's statement is retained. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "insert_eq"]
theorem insert_eq {α : Type} (n1 _n2 : Nat) (v1 v2 : α) (l : Spt α) :
    sptInsert n1 v1 l = sptInsert n1 v2 l ↔ v1 = v2 := by
  constructor
  · intro h
    have := congrArg (sptLookup n1) h
    simpa [sptLookup_sptInsert_same] using this
  · rintro rfl; rfl

/-- Exact HOL `evaluate_arith_set_var` (`word_cseProof:179-215`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_arith_set_var {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (r : Nat) (u w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : canMemArith a = true ∧ r ∉ arithReads a) :
    (evaluate (.inst (.arith a.toWordLangArith)) (setVar r u s) =
        (none, setVar (firstRegOfArith a) w (setVar r u s)) ↔
      evaluate (.inst (.arith a.toWordLangArith)) s = (none, setVar (firstRegOfArith a) w s)) := by
  rw [evaluate_arith_iff a h.1, evaluate_arith_iff a h.1,
    arithValue_congr a h.1 s (setVar r u s)
      (fun x hx => getVar_setVar_ne s r x u (fun e => h.2 (e ▸ hx)))]

/-- Exact HOL `evaluate_load_any_dest` (`word_cseProof:221-233`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_any_dest"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_load_any_dest {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r0 a : Nat) (ofs : BitVec width) (w : WordLocW width) (s : WordSemStateFiniteExact width C F) (r : Nat)
    (h : ¬isStore op ∧ evaluate (.inst (.mem op r0 (.addr a ofs))) s = (none, setVar r0 w s)) :
    evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s) := by
  have hs : isStore op = false := by simpa using h.1
  exact (evaluate_load_iff op hs r a ofs w s).mpr ((evaluate_load_iff op hs r0 a ofs w s).mp h.2)

/-- Exact HOL `evaluate_load_set_var` (`word_cseProof:235-256`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_set_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_load_set_var {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r a : Nat) (ofs : BitVec width) (n : Nat) (u w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : ¬isStore op ∧ a ≠ n) :
    (evaluate (.inst (.mem op r (.addr a ofs))) (setVar n u s) = (none, setVar r w (setVar n u s)) ↔
      evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s)) := by
  have hs : isStore op = false := by simpa using h.1
  rw [evaluate_load_iff op hs, evaluate_load_iff op hs,
    loadValue_congr op a ofs s (setVar n u s) (getVar_setVar_ne s n a u h.2) rfl rfl rfl]

/-- Exact HOL local `evaluate_load_change_addr` (`word_cseProof:258-270`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_change_addr"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_load_change_addr {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r a a' : Nat) (ofs : BitVec width) (w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : ¬isStore op ∧ sptLookup a' s.locals = sptLookup a s.locals ∧
      evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s)) :
    evaluate (.inst (.mem op r (.addr a' ofs))) s = (none, setVar r w s) := by
  have hs : isStore op = false := by simpa using h.1
  have hv : loadValue op a ofs s = loadValue op a' ofs s := by
    unfold loadValue
    have hv : wordExp s (.var a) = wordExp s (.var a') := by rw [wordExp, wordExp]; exact h.2.1.symm
    have hk : wordExp s (.const ofs) = wordExp s (.const ofs) := rfl
    rw [wordExp_op2_congr s s .add _ _ _ _ hv hk]
  rw [evaluate_load_iff op hs, ← hv]
  exact (evaluate_load_iff op hs r a ofs w s).mp h.2.2

/-- Exact HOL local `evaluate_arith_memory` (`word_cseProof:272-287`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_memory"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_arith_memory {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (w : WordLocW width) (s : WordSemStateFiniteExact width C F) (m : BitVec width → WordLocW width)
    (h : canMemArith a = true) :
    (evaluate (.inst (.arith a.toWordLangArith)) { s with memory := m } =
        (none, { setVar (firstRegOfArith a) w s with memory := m }) ↔
      evaluate (.inst (.arith a.toWordLangArith)) s = (none, setVar (firstRegOfArith a) w s)) := by
  rw [show ({ setVar (firstRegOfArith a) w s with memory := m } : WordSemStateFiniteExact width C F) =
      setVar (firstRegOfArith a) w { s with memory := m } from rfl,
    evaluate_arith_iff a h, evaluate_arith_iff a h,
    arithValue_congr a h s { s with memory := m } (fun _ _ => rfl)]

/-- Exact HOL local `evaluate_arith_unset_var` (`word_cseProof:341-380`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_unset_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_arith_unset_var {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (r : Nat) (w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : canMemArith a = true ∧ r ∉ arithReads a) :
    (evaluate (.inst (.arith a.toWordLangArith)) (unsetVar r s) =
        (none, setVar (firstRegOfArith a) w (unsetVar r s)) ↔
      evaluate (.inst (.arith a.toWordLangArith)) s = (none, setVar (firstRegOfArith a) w s)) := by
  rw [evaluate_arith_iff a h.1, evaluate_arith_iff a h.1,
    arithValue_congr a h.1 s (unsetVar r s)
      (fun x hx => getVar_unsetVar_ne s r x (fun e => h.2 (e ▸ hx)))]

/-- Exact HOL local `evaluate_load_unset_var` (`word_cseProof:382-400`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_unset_var"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_load_unset_var {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r a : Nat) (ofs : BitVec width) (n : Nat) (w : WordLocW width) (s : WordSemStateFiniteExact width C F)
    (h : ¬isStore op ∧ a ≠ n) :
    (evaluate (.inst (.mem op r (.addr a ofs))) (unsetVar n s) = (none, setVar r w (unsetVar n s)) ↔
      evaluate (.inst (.mem op r (.addr a ofs))) s = (none, setVar r w s)) := by
  have hs : isStore op = false := by simpa using h.1
  rw [evaluate_load_iff op hs, evaluate_load_iff op hs,
    loadValue_congr op a ofs s (unsetVar n s) (getVar_unsetVar_ne s n a h.2) rfl rfl rfl]

/-- Exact HOL local `evaluate_arith_agree` (`word_cseProof:521-537`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_arith_agree"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_arith_agree {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : HolArith width) (w : WordLocW width) (s1 s2 : WordSemStateFiniteExact width C F)
    (h : evaluate (.inst (.arith a.toWordLangArith)) s1 = (none, setVar (firstRegOfArith a) w s1) ∧
      canMemArith a = true ∧ s2.locals = s1.locals) :
    evaluate (.inst (.arith a.toWordLangArith)) s2 = (none, setVar (firstRegOfArith a) w s2) := by
  obtain ⟨he, hc, hl⟩ := h
  rw [evaluate_arith_iff a hc] at he ⊢
  rw [arithValue_congr a hc s1 s2 (fun x _ => by simp only [getVar, hl])]
  exact he

/-- Exact HOL local `evaluate_load_agree` (`word_cseProof:539-553`). -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "evaluate_load_agree"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluate_load_agree {width : Nat} [NeZero width] {C : Type} {F : Type}
    (op : HolMemop) (r a : Nat) (ofs : BitVec width) (w : WordLocW width) (s1 s2 : WordSemStateFiniteExact width C F)
    (h : evaluate (.inst (.mem op r (.addr a ofs))) s1 = (none, setVar r w s1) ∧ ¬isStore op ∧
      s2.locals = s1.locals ∧ s2.memory = s1.memory ∧ s2.mdomain = s1.mdomain ∧ s2.be = s1.be) :
    evaluate (.inst (.mem op r (.addr a ofs))) s2 = (none, setVar r w s2) := by
  obtain ⟨he, hs, hl, hm, hd, hb⟩ := h
  have hs : isStore op = false := by simpa using hs
  rw [evaluate_load_iff op hs] at he ⊢
  rw [loadValue_congr op a ofs s1 s2 (by simp only [getVar, hl]) hm hd hb]
  exact he

end Compiler.Backend.WordCse

end Flapjack
