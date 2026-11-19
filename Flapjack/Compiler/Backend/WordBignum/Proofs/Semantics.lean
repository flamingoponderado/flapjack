module

public import Flapjack.Compiler.Backend.WordBignum.Helpers
public import Flapjack.Compiler.Backend.WordBignum.Mini
public import Flapjack.Misc.Multiword.SingleWord
public import Flapjack.FiniteMap.Exact
public import Flapjack.FiniteMap.DomExact
public import Flapjack.Misc.ListEl
public import Flapjack.HolArb
public import Flapjack.Misc.FiniteMapApply
public import Flapjack.Compiler.Encoders.Asm
public import Mathlib.Logic.Function.Basic

@[expose] public section

/-! The bignum generator's mini-language state and evaluator, ported from
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. -/
namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack
open Flapjack.Misc.Multiword
open Flapjack.Compiler.Encoders.Asm

/-- Every word carrier has an inhabitant. This Flapjack-only instance exists so
the reviewed `holFapply` rendering of HOL's total `FAPPLY` can be used at word
types; it adds no hypothesis to any tagged statement. -/
instance bitVecNonempty {width : Nat} : Nonempty (BitVec width) := ⟨0⟩

/-- The mini-language state: the register finite map, the three array contents
and the clock. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "state"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
structure MiniState (width : Nat) [NeZero width] where
  regs : HolFiniteMapExact Nat (BitVec width)
  arrays : Address → List (BitVec width)
  clock : Nat

/-- Explicit lookup-and-support view of the mini-language state. -/
structure MiniStateBroad (width : Nat) [NeZero width] where
  regs : Nat → Option (BitVec width)
  regsFiniteSupport : ∃ keys : List Nat, ∀ key, regs key ≠ none → key ∈ keys
  arrays : Address → List (BitVec width)
  clock : Nat

/-- Expose the register map as lookup and finite support. -/
def MiniState.toBroad {width : Nat} [NeZero width] (s : MiniState width) :
    MiniStateBroad width :=
  ⟨s.regs.lookup, s.regs.finiteSupport, s.arrays, s.clock⟩

/-- Reconstruct a canonical mini-language state from its explicit map view. -/
def MiniState.ofBroad {width : Nat} [NeZero width] (s : MiniStateBroad width) :
    MiniState width :=
  ⟨⟨s.regs, s.regsFiniteSupport⟩, s.arrays, s.clock⟩

/-- The mini-language state and its explicit finite-support view roundtrip. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] :
    (∀ s : MiniStateBroad width, (MiniState.ofBroad s).toBroad = s) ∧
      (∀ s : MiniState width, MiniState.ofBroad s.toBroad = s) := by
  constructor
  · intro s
    cases s
    rfl
  · intro s
    cases s with
    | mk regs arrays clock =>
      cases regs
      rfl

/-- Evaluate a mini-language expression. Undefined registers read as the
arbitrary word and the unlisted expression shapes evaluate to an arbitrary
word, as in HOL's total definition. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "eval_exp_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
noncomputable def evalExp {width : Nat} [NeZero width] (s : MiniState width) :
    WordLangExpHOL (BitVec width) → BitVec width
  | .const w => w
  | .var v => holFapply s.regs v
  | .op .add [x1, x2] => evalExp s x1 + evalExp s x2
  | .op .sub [x1, x2] => evalExp s x1 - evalExp s x2
  | .op .and [x1, x2] => evalExp s x1 &&& evalExp s x2
  | .op .or [x1, x2] => evalExp s x1 ||| evalExp s x2
  | .op .xor [x1, x2] => evalExp s x1 ^^^ evalExp s x2
  | .shift .lsl x1 x2 => evalExp s x1 <<< (evalExp s x2).toNat
  | .shift .asr x1 x2 => BitVec.sshiftRight (evalExp s x1) (evalExp s x2).toNat
  | .shift .lsr x1 x2 => evalExp s x1 >>> (evalExp s x2).toNat
  | .shift .ror x1 x2 => BitVec.rotateRight (evalExp s x1) (evalExp s x2).toNat
  | _ => holArb (BitVec width)

/-- The expression well-formedness precondition of the evaluator. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "eval_exp_pre_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
noncomputable def evalExpPre {width : Nat} [NeZero width] (s : MiniState width) :
    WordLangExpHOL (BitVec width) → Prop
  | .const _ => True
  | .var v => v ∈ s.regs.dom
  | .op _ [x, y] => evalExpPre s x ∧ evalExpPre s y
  | .shift _ x1 x2 => evalExpPre s x1 ∧ evalExpPre s x2 ∧ (evalExp s x2).toNat < 32
  | _ => False

/-- The register-or-immediate well-formedness precondition. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "eval_ri_pre_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
noncomputable def evalRiPre {width : Nat} [NeZero width] (s : MiniState width) :
    WordRegImm (BitVec width) → Prop
  | .reg r => evalExpPre s (.var r)
  | .imm _ => True

/-- Evaluate a register or an immediate. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "eval_ri_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
noncomputable def evalRi {width : Nat} [NeZero width] (s : MiniState width) :
    WordRegImm (BitVec width) → BitVec width
  | .reg r => evalExp s (.var r)
  | .imm w => w

/-- Decrement the clock by one. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "dec_clock_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def decClock {width : Nat} [NeZero width] (s : MiniState width) : MiniState width :=
  { s with clock := s.clock - 1 }

/-- Write a register: no value deletes it, a value updates it. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "reg_write_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def regWrite {width : Nat} [NeZero width] (v : Nat) (value : Option (BitVec width))
    (s : MiniState width) : MiniState width :=
  match value with
  | none => { s with regs := s.regs.eraseEq v }
  | some w => { s with regs := s.regs.updateEq (v, w) }

/-- Delete a list of registers from a state. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "delete_vars_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def deleteVars {width : Nat} [NeZero width] : List Nat → MiniState width → MiniState width
  | [], s => s
  | v :: vs, s => regWrite v none (deleteVars vs s)

/-- Replace one array's contents. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "array_write_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def arrayWrite {width : Nat} [NeZero width] (n : Address) (v : List (BitVec width))
    (s : MiniState width) : MiniState width :=
  { s with arrays := Function.update s.arrays n v }

/-- Overwrite the clock with a given value. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "clock_write_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def clockWrite {width : Nat} [NeZero width] (l : Nat) (s : MiniState width) : MiniState width :=
  { s with clock := l }

/-- Copy the named registers from a source register map into a target state,
failing when any name is missing. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "copy_vars_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def copyVars {width : Nat} [NeZero width] : List Nat →
    HolFiniteMapExact Nat (BitVec width) → MiniState width → Option (MiniState width)
  | [], _, t => some t
  | n :: ns, source, t =>
    match source.lookup n with
    | none => none
    | some x => copyVars ns source (regWrite n (some x) t)

/-- The source's small-step relation over mini-programs: the recursion target
(`none` for a top-level program, `some p` while executing `p`), the state, the
program, and the result (`inl` for `Continue`, `inr` for a final state). -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "eval"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
inductive Eval {width : Nat} [NeZero width] :
    Option (Mini (BitVec width)) → MiniState width → Mini (BitVec width) →
    Sum (MiniState width) (MiniState width) → Prop
  | skip (r : Option (Mini (BitVec width))) (s : MiniState width) :
      Eval r s .skip (.inr s)
  | continue (r : Option (Mini (BitVec width))) (s : MiniState width) :
      Eval r s .continue (.inl s)
  | delete (r : Option (Mini (BitVec width))) (vs : List Nat) (s : MiniState width) :
      Eval r s (.delete vs) (.inr (deleteVars vs s))
  | assign (r : Option (Mini (BitVec width))) (s : MiniState width)
      (x : WordLangExpHOL (BitVec width)) (n : Nat) (h : evalExpPre s x) :
      Eval r s (.assign n x) (.inr (regWrite n (some (evalExp s x)) s))
  | seq (r : Option (Mini (BitVec width))) (s1 s2 : MiniState width)
      (s3 : Sum (MiniState width) (MiniState width))
      (p1 p2 : Mini (BitVec width))
      (h1 : Eval r s1 p1 (.inr s2)) (h2 : Eval r s2 p2 s3) :
      Eval r s1 (.seq p1 p2) s3
  | ite (rec : Option (Mini (BitVec width))) (s1 : MiniState width)
      (c : Cmp) (r : Nat) (ri : WordRegImm (BitVec width))
      (p1 p2 : Mini (BitVec width)) (s2 : Sum (MiniState width) (MiniState width))
      (hreg : r ∈ s1.regs.dom) (hri : evalRiPre s1 ri)
      (h : Eval rec s1
        (if wordCmpHOL c (evalExp s1 (.var r)) (evalRi s1 ri) then p1 else p2) s2) :
      Eval rec s1 (.ite c r ri p1 p2) s2
  | load (rec : Option (Mini (BitVec width))) (s : MiniState width)
      (r i : Nat) (a : Address) (w : BitVec width)
      (hlookup : s.regs.lookup i = some w) (hbound : w.toNat < (s.arrays a).length) :
      Eval rec s (.load r i a) (.inr (regWrite r (some (holEl w.toNat (s.arrays a))) s))
  | store (rec : Option (Mini (BitVec width))) (s : MiniState width)
      (r i : Nat) (w wr : BitVec width)
      (hlookup : s.regs.lookup i = some w) (hvalue : s.regs.lookup r = some wr)
      (hbound : w.toNat < (s.arrays .out).length) :
      Eval rec s (.store r i) (.inr (arrayWrite .out ((s.arrays .out).set w.toNat wr) s))
  | swap (r : Option (Mini (BitVec width))) (s : MiniState width) :
      Eval r s .swap (.inr (arrayWrite .in1 (s.arrays .in2) (arrayWrite .in2 (s.arrays .in1) s)))
  | add (n1 n2 n3 : Nat) (n4 n5 : WordRegImm (BitVec width))
      (r : Option (Mini (BitVec width))) (s : MiniState width) (r1 r2 : BitVec width)
      (hreg : n3 ∈ s.regs.dom) (h4 : evalRiPre s n4) (h5 : evalRiPre s n5)
      (hcarry : evalRi s n5 ≠ 0 → evalRi s n5 = 1)
      (hdistinct : n1 ≠ n2)
      (hadd : singleAddWord (holFapply s.regs n3)
        (evalRi s n4) (evalRi s n5) = (r1, r2)) :
      Eval r s (.add n1 n2 n3 n4 n5) (.inr (regWrite n1 (some r1) (regWrite n2 (some r2) s)))
  | sub (r : Option (Mini (BitVec width))) (s : MiniState width)
      (n1 n2 n3 : Nat) (n4 n5 : WordRegImm (BitVec width)) (r1 r2 : BitVec width)
      (hreg : n3 ∈ s.regs.dom) (h4 : evalRiPre s n4) (h5 : evalRiPre s n5)
      (hcarry : evalRi s n5 ≠ 0 → evalRi s n5 = 1)
      (hdistinct : n1 ≠ n2)
      (hsub : singleSubWord (holFapply s.regs n3)
        (evalRi s n4) (evalRi s n5) = (r1, r2)) :
      Eval r s (.sub n1 n2 n3 n4 n5) (.inr (regWrite n1 (some r1) (regWrite n2 (some r2) s)))
  | mul (r : Option (Mini (BitVec width))) (s : MiniState width) (n1 n2 n3 n4 : Nat)
      (h3 : n3 ∈ s.regs.dom) (h4 : n4 ∈ s.regs.dom) (hdistinct : n1 ≠ n2) :
      Eval r s (.mul n1 n2 n3 n4)
        (.inr (regWrite n1
          (some (singleMul (holFapply s.regs n3)
            (holFapply s.regs n4) 0).1)
          (regWrite n2
            (some (singleMul (holFapply s.regs n3)
              (holFapply s.regs n4) 0).2) s)))
  | div (r : Option (Mini (BitVec width))) (s : MiniState width) (n1 n2 n3 n4 n5 : Nat)
      (h3 : n3 ∈ s.regs.dom) (h4 : n4 ∈ s.regs.dom)
      (h5 : n5 ∈ s.regs.dom) (hdistinct : n1 ≠ n2)
      (hpre : singleDivPre (holFapply s.regs n3)
        (holFapply s.regs n4)
        (holFapply s.regs n5)) :
      Eval r s (.div n1 n2 n3 n4 n5)
        (.inr (regWrite n1
          (some (singleDiv (holFapply s.regs n3)
            (holFapply s.regs n4)
            (holFapply s.regs n5)).1)
          (regWrite n2
            (some (singleDiv (holFapply s.regs n3)
              (holFapply s.regs n4)
              (holFapply s.regs n5)).2) s)))
  | loop (r : Option (Mini (BitVec width))) (s1 : MiniState width) (p : Mini (BitVec width))
      (vs : List Nat) (s2 : MiniState width) (rec : Bool)
      (h : Eval (if rec then some p else none) (deleteVars vs (decClock s1))
        (.loopBody p) (.inr s2))
      (hclock : s1.clock ≠ 0) :
      Eval r s1 (.loop rec vs p) (.inr s2)
  | recurse (s1 : MiniState width) (saveRegs vs : List Nat) (p : Mini (BitVec width))
      (s2 s3 : MiniState width)
      (h : Eval (some p) (deleteVars vs (decClock s1)) (.loopBody p) (.inr s2))
      (hcopy : copyVars saveRegs s1.regs s2 = some s3)
      (hclock : s1.clock ≠ 0) :
      Eval (some p) s1 (.recurse saveRegs vs) (.inr s3)
  | loopBodyReturn (r : Option (Mini (BitVec width))) (s1 : MiniState width)
      (p : Mini (BitVec width)) (s2 : MiniState width)
      (h : Eval r s1 p (.inr s2)) :
      Eval r s1 (.loopBody p) (.inr s2)
  | loopBodyContinue (r : Option (Mini (BitVec width))) (s1 s2 s3 : MiniState width)
      (p : Mini (BitVec width))
      (h1 : Eval r s1 p (.inl s2)) (hclock : s2.clock ≠ 0)
      (h2 : Eval r (decClock s2) (.loopBody p) (.inr s3)) :
      Eval r s1 (.loopBody p) (.inr s3)

/-- A top-level evaluation is also an evaluation with any recursion target: the
recursion target only reaches the `Rec` and `Loop` rules, which ignore it. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Eval_NONE_IMP"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Eval_NONE_IMP {width : Nat} [NeZero width] :
    ∀ (s1 : MiniState width) (c : Mini (BitVec width))
      (s2 : Sum (MiniState width) (MiniState width)) (p : Mini (BitVec width)),
      Eval none s1 c s2 → Eval (some p) s1 c s2 := by
  intro s1 c s2 p h
  generalize hr : (none : Option (Mini (BitVec width))) = r at h
  induction h with
  | skip r s => exact Eval.skip (some p) s
  | «continue» r s => exact Eval.continue (some p) s
  | delete r vs s => exact Eval.delete (some p) vs s
  | assign r s x n hpre => exact Eval.assign (some p) s x n hpre
  | seq r s1 s2 s3 p1 p2 h1 h2 ih1 ih2 =>
    exact Eval.seq (some p) s1 s2 s3 p1 p2 (ih1 hr) (ih2 hr)
  | ite rec s1 cmp r ri p1 p2 s2 hreg hri h ih =>
    exact Eval.ite (some p) s1 cmp r ri p1 p2 s2 hreg hri (ih hr)
  | load rec s r i a w hlookup hbound =>
    exact Eval.load (some p) s r i a w hlookup hbound
  | store rec s r i w wr hlookup hvalue hbound =>
    exact Eval.store (some p) s r i w wr hlookup hvalue hbound
  | swap r s => exact Eval.swap (some p) s
  | add n1 n2 n3 n4 n5 r s r1 r2 hreg h4 h5 hcarry hdistinct hadd =>
    exact Eval.add n1 n2 n3 n4 n5 (some p) s r1 r2 hreg h4 h5 hcarry hdistinct hadd
  | sub r s n1 n2 n3 n4 n5 r1 r2 hreg h4 h5 hcarry hdistinct hsub =>
    exact Eval.sub (some p) s n1 n2 n3 n4 n5 r1 r2 hreg h4 h5 hcarry hdistinct hsub
  | mul r s n1 n2 n3 n4 h3 h4 hdistinct =>
    exact Eval.mul (some p) s n1 n2 n3 n4 h3 h4 hdistinct
  | div r s n1 n2 n3 n4 n5 h3 h4 h5 hdistinct hpre =>
    exact Eval.div (some p) s n1 n2 n3 n4 n5 h3 h4 h5 hdistinct hpre
  | loop r s1 body vs s2 rec h hclock =>
    exact Eval.loop (some p) s1 body vs s2 rec h hclock
  | recurse s1 saveRegs vs body s2 s3 h hcopy hclock =>
    exact absurd hr (by simp)
  | loopBodyReturn r s1 body s2 h ih =>
    exact Eval.loopBodyReturn (some p) s1 body s2 (ih hr)
  | loopBodyContinue r s1 s2 s3 body h1 hclock h2 ih1 ih2 =>
    exact Eval.loopBodyContinue (some p) s1 s2 s3 body (ih1 hr) hclock (ih2 hr)

end Flapjack.Compiler.Backend.WordBignum
