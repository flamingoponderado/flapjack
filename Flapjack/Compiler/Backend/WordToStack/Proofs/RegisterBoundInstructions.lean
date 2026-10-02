import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.StackProps.RegisterBounds
import Flapjack.Pancake.WordConvs
import Mathlib.Tactic.SplitIfs

namespace Flapjack.WordToStackProofs.RegisterBoundInstructions
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStackRegFormat

/- Internal register calculations from the original Inst/ShareInst case proof.
These are Flapjack infrastructure, with no separately named HOL original. -/
theorem loadBound {width : Nat} [NeZero width] (loads : List (Nat × Nat))
    (p : HolProg width) (bound : Nat) :
    regBound (wStackLoadNative loads p) bound ↔
      (∀ x ∈ loads, x.1 < bound) ∧ regBound p bound := by
  induction loads with
  | nil => simp [wStackLoadNative]
  | cons x xs ih => cases x; simp [wStackLoadNative, regBound, ih, and_assoc]

theorem reg1Bounds (r : Nat) (frame : Nat × Nat × Nat) :
    (∀ x ∈ (wReg1 r frame).1, x.1 < frame.1 + 2) ∧
      (wReg1 r frame).2 < frame.1 + 2 := by
  simp only [wReg1]
  split <;> simp_all <;> omega

theorem reg2Bounds (r : Nat) (frame : Nat × Nat × Nat) :
    (∀ x ∈ (wReg2 r frame).1, x.1 < frame.1 + 2) ∧
      (wReg2 r frame).2 < frame.1 + 2 := by
  simp only [wReg2]
  split <;> simp_all <;> omega

theorem writeBound {width : Nat} [NeZero width] (g : Nat → HolProg width)
    (r : Nat) (frame : Nat × Nat × Nat)
    (h : ∀ n, n < frame.1 + 2 → regBound (g n) (frame.1 + 2)) :
    regBound (wRegWrite1Native g r frame) (frame.1 + 2) := by
  simp only [wRegWrite1Native]
  split
  · exact h _ (by omega)
  · exact ⟨h _ (by omega), by simp only [regBound]; omega⟩

theorem write2Bound {width : Nat} [NeZero width] (g : Nat → HolProg width)
    (r : Nat) (frame : Nat × Nat × Nat)
    (h : ∀ n, n < frame.1 + 2 → regBound (g n) (frame.1 + 2)) :
    regBound (wRegWrite2Native g r frame) (frame.1 + 2) := by
  simp only [wRegWrite2Native]
  split
  · exact h _ (by omega)
  · exact ⟨h _ (by omega), by simp only [regBound]; omega⟩

private theorem instBound {width : Nat} [NeZero width] (i : HolInst width)
    (frame : Nat × Nat × Nat) (room : 4 ≤ frame.1)
    (convention : instArgConventionExact i = true) :
    regBound (wInstNative i frame) (frame.1 + 2) := by
  cases i with
  | const n c =>
      simp only [wInstNative]
      apply writeBound
      intro n hn
      exact hn
  | arith a =>
      cases a <;> try (rename_i op d src ri; cases ri)
      all_goals try simp only [instArgConventionExact, Bool.and_eq_true, beq_iff_eq] at convention
      all_goals simp only [wInstNative, wRegWrite1Native,
        wReg1, wReg2, regBound, regBoundInst]
      all_goals try split_ifs
      all_goals try simp only [regBound, regBoundInst, List.append_nil,
        List.nil_append, List.cons_append, wStackLoadNative]
      all_goals repeat' apply And.intro
      all_goals first | trivial | omega
  | mem op d addr =>
      cases addr
      cases op
      all_goals simp only [wInstNative, wRegWrite1Native,
        wReg1, wReg2, regBound, regBoundInst]
      all_goals try split_ifs
      all_goals try simp only [regBound, regBoundInst, List.append_nil,
        List.nil_append, List.cons_append, wStackLoadNative]
      all_goals repeat' apply And.intro
      all_goals first | trivial | omega
  | fp f =>
      cases f
      all_goals by_cases hw : width = 64
      all_goals simp only [wInstNative, hw, if_true, if_false,
        wRegWrite1Native, wRegWrite2Native, wReg1, wReg2, regBound, regBoundInst]
      all_goals try split_ifs
      all_goals try simp only [regBound, regBoundInst, List.append_nil,
        List.nil_append, List.cons_append, wStackLoadNative]
      all_goals repeat' apply And.intro
      all_goals first | trivial | omega
  | skip => trivial

/-- Full original Inst case: all source quantified inputs and all three
original premises are retained, on the actual native compiler output. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_reg_bound" (words_as_type_indexed_bitvec)]
theorem wordToStackRegBoundInst {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (i : WordLangInst (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (conventions : postAllocConventionsHOL frame.1 (.inst i) = true)
    (room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.inst i) bs frame).1 (frame.1 + 2) := by
  subst perf
  simp only [compNative]
  apply instBound _ _ room
  simp only [postAllocConventionsHOL, Bool.and_eq_true] at conventions
  have convention : instArgConvention i = true := conventions.2.2
  cases i with
  | arith a =>
      cases a <;> try (rename_i op d src ri; cases ri)
      all_goals simp_all only [HolInst.ofWordLangInst, HolArith.ofWordLangArith, HolRegImm.ofWordRegImm, instArgConvention, instArgConventionExact]
  | mem op d addr => cases addr; trivial
  | fp f => cases f <;> trivial
  | skip => trivial
  | const _ _ => trivial

/-- Internal source-case calculation for all eight shared-memory operations;
there is no separately named HOL declaration for this intermediate. -/
theorem shareBound {width : Nat} [NeZero width] (op : HolMemop) (v : Nat)
    (addr : HolAddr width) (frame : Nat × Nat × Nat) :
    regBound (wShareInstNative op v addr frame) (frame.1 + 2) := by
  cases addr
  cases op
  all_goals simp only [wShareInstNative, wRegWrite1Native, wReg1, wReg2]
  all_goals try split_ifs
  all_goals simp only [regBound, List.append_nil, List.nil_append,
    List.cons_append, wStackLoadNative]
  all_goals repeat' apply And.intro
  all_goals omega

/-- Entire original ShareInst case, including failed address extraction.
All original guards and every expression are retained. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_reg_bound" (words_as_type_indexed_bitvec)]
theorem wordToStackRegBoundShareInst {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (op : HolMemop) (v : Nat)
    (exp : WordLangExpHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat)
    (_conventions : postAllocConventionsHOL frame.1 (.shareInst op v exp) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.shareInst op v exp) bs frame).1 (frame.1 + 2) := by
  subst perf
  cases h : expToAddrHOL exp <;> simp only [compNative, h]
  · trivial
  · exact shareBound _ _ _ frame

end Flapjack.WordToStackProofs.RegisterBoundInstructions
