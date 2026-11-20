module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.CodeSubset
public import Flapjack.Compiler.Backend.WordBignum.Compile

@[expose] public section

/-! Loop-tick bookkeeping, the source's correctness predicate, and the
installed-code well-formedness predicate, ported from
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. -/
namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack
open Flapjack.Misc.Multiword
open Flapjack.Compiler.Encoders.Asm

namespace RelationsWitness

/-- The mini-language state and its explicit finite-support view roundtrip,
restated locally so the relations in this module carry the same canonical
finite-map witness as the `Semantics` module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] :
    (∀ s : MiniStateBroad width, (MiniState.ofBroad s).toBroad = s) ∧
      (∀ s : MiniState width, MiniState.ofBroad s.toBroad = s) :=
  Flapjack.Compiler.Backend.WordBignum.holFmapAsFiniteSupportWitness

end RelationsWitness

/-- One tick of a fuelled loop driver: a `Continue` result decrements the clock
and keeps the guard when the clock is non-zero; a final state passes through
with the guard unchanged. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "loop_app_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def loopApp {width : Nat} [NeZero width] {β γ : Type}
    (f : γ → Sum (MiniState width) β) (g : γ → Bool) (x : γ) :
    Sum (MiniState width) β × Bool :=
  match f x with
  | .inl s => (.inl (decClock s), g x && decide (s.clock ≠ 0))
  | .inr s' => (.inr s', g x)

/-- A clock-guarded body step: at clock zero the state and guard `F` are
returned unchanged, otherwise the body runs on the register-deleted,
clock-decremented state. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "tick_before_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def tickBefore {width : Nat} [NeZero width] (vs : List Nat)
    (f : MiniState width → MiniState width × Bool) (s : MiniState width) :
    MiniState width × Bool :=
  if s.clock = 0 then (s, false) else f (deleteVars vs (decClock s))

/-- The source's correctness predicate: when the guard holds, the program
evaluates at the top level to the given result. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def Corr {width : Nat} [NeZero width] (prog : Mini (BitVec width)) (s : MiniState width)
    (s1 : Sum (MiniState width) (MiniState width)) (p : Bool) : Prop :=
  p = true → Eval none s prog s1

/-- Every installed mini-program compiles to the word program recorded beside
it and extends the accumulator it was compiled from. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "good_code_def"
  (words_as_type_indexed_bitvec)]
def goodCode {α : Type} {width : Nat} [NeZero width]
    (cs3 : α × List (Mini (BitVec width) × Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ prog n p2, (prog, n, p2) ∈ cs3.2 →
    ∃ cs1 l2' i2 cs2, compile n 2 1 cs1 prog = (p2, l2', i2, cs2) ∧ codeSubset cs2 cs3

/-! ## The `Corr` group (`word_bignumProofScript.sml:1342-1872`)

Each lemma relates one mini-language program shape to its `Eval` rule; the
Boolean guard is HOL's `bool` argument of `Corr`, so HOL's `T` is `true` and
HOL's `q1 /\ q2` is `&&`. -/

/-- HOL `Corr_Skip`: the guard holds and `Skip` evaluates to itself. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Skip"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Skip {width : Nat} [NeZero width] (s : MiniState width) :
    Corr .skip s (.inr s) true := by
  intro _
  exact Eval.skip none s

/-- HOL `Corr_Continue`: `Continue` evaluates to the left injection. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Continue"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Continue {width : Nat} [NeZero width] (s : MiniState width) :
    Corr .continue s (.inl s) true := by
  intro _
  exact Eval.continue none s

/-- HOL `Corr_Delete`: deleting registers evaluates to the updated state. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Delete"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Delete {width : Nat} [NeZero width] (vs : List Nat) (s : MiniState width) :
    Corr (.delete vs) s (.inr (deleteVars vs s)) true := by
  intro _
  exact Eval.delete none vs s

/-- HOL `Corr_Swap`: swapping the two input arrays evaluates to the swapped
state. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Swap"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Swap {width : Nat} [NeZero width] (s : MiniState width) :
    Corr .swap s
      (.inr (arrayWrite .in1 (s.arrays .in2) (arrayWrite .in2 (s.arrays .in1) s))) true := by
  intro _
  exact Eval.swap none s

/-- HOL `Corr_Seq`: two guarded evaluations compose, with the conjunction of
their guards. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Seq"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Seq {width : Nat} [NeZero width]
    (p2 : Mini (BitVec width)) (s1 : MiniState width)
    (s2 : Sum (MiniState width) (MiniState width)) (q2 : Bool)
    (p1 : Mini (BitVec width)) (s : MiniState width) (q1 : Bool) :
    Corr p2 s1 s2 q2 → Corr p1 s (.inr s1) q1 → Corr (.seq p1 p2) s s2 (q1 && q2) := by
  intro h2 h1 h
  rw [Bool.and_eq_true] at h
  exact Eval.seq none s s1 s2 p1 p2 (h1 h.1) (h2 h.2)

/-- HOL `Corr_Seq_alt`: the same composition with an extra Boolean premise on
the continuation. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Seq_alt"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Seq_alt {width : Nat} [NeZero width]
    (b : Bool) (p2 : Mini (BitVec width)) (s1 : MiniState width)
    (s2 : Sum (MiniState width) (MiniState width)) (q2 : Bool)
    (p1 : Mini (BitVec width)) (s : MiniState width) (q1 : Bool) :
    (b = true → Corr p2 s1 s2 q2) → Corr p1 s (.inr s1) q1 →
      b = true → Corr (.seq p1 p2) s s2 (q1 && q2) := by
  intro hb h1 hq h
  rw [Bool.and_eq_true] at h
  exact Eval.seq none s s1 s2 p1 p2 (h1 h.1) (hb hq h.2)

/-- HOL `Corr_STRENGTHEN_TERM`: a guarded evaluation to a right injection can be
restated at that injection with a stronger guard. HOL binds `f'` and `q'` after
the first premise, so Lean quantifies them in the conclusion. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_STRENGTHEN_TERM"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_STRENGTHEN_TERM {width : Nat} [NeZero width]
    (p : Mini (BitVec width)) (s : MiniState width)
    (f : Sum (MiniState width) (MiniState width)) (q : Bool) :
    Corr p s f q → ∀ (f' : MiniState width) (q' : Bool),
      (q' = true → f = .inr f' ∧ q = true) → Corr p s (.inr f') q' := by
  intro h f' q' hf hq
  obtain ⟨hfinr, hqtrue⟩ := hf hq
  rw [hfinr] at h
  exact h hqtrue

/-- HOL `Corr_move_pre`: conjoining a Boolean premise with the guard is the
same as guarding the evaluation. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_move_pre"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_move_pre {width : Nat} [NeZero width]
    (b : Bool) (code : Mini (BitVec width)) (s : MiniState width)
    (f : Sum (MiniState width) (MiniState width)) (p : Bool) :
    (b = true → Corr code s f p) ↔ Corr code s f (b && p) := by
  cases b <;> simp [Corr]

/-! ### Boolean guards for the `Corr` rules

HOL's `Corr` guard is a `bool` built from the Boolean `eval_exp_pre`,
`eval_ri_pre` and `FDOM` tests. Lean's `evalExpPre`/`evalRiPre` are
propositions, so the guards are stated with `decide`; these Flapjack-only
instances make those propositions decidable. -/

/-- Flapjack-only decision procedure for the mini-language expression
precondition, mirroring the tagged `evalExpPre` clauses. -/
noncomputable instance evalExpPreDecidable {width : Nat} [NeZero width] (s : MiniState width) :
    ∀ x : WordLangExpHOL (BitVec width), Decidable (evalExpPre s x)
  | .const _ => isTrue trivial
  | .var v =>
      decidable_of_iff (s.regs.lookup v ≠ none)
        (by simp [evalExpPre, HolFiniteMapExact.dom])
  | .op _ [x, y] => by
      haveI := evalExpPreDecidable s x
      haveI := evalExpPreDecidable s y
      exact decidable_of_iff (evalExpPre s x ∧ evalExpPre s y) (by simp [evalExpPre])
  | .shift _ x1 x2 => by
      haveI := evalExpPreDecidable s x1
      haveI := evalExpPreDecidable s x2
      exact decidable_of_iff
        (evalExpPre s x1 ∧ evalExpPre s x2 ∧ (evalExp s x2).toNat < 32)
        (by simp [evalExpPre])
  | .lookup _ => isFalse (by simp [evalExpPre])
  | .load _ => isFalse (by simp [evalExpPre])
  | .op _ [] => isFalse (by simp [evalExpPre])
  | .op _ [_] => isFalse (by simp [evalExpPre])
  | .op _ (_ :: _ :: _ :: _) => isFalse (by simp [evalExpPre])

/-- Flapjack-only decision procedure for the mini-language register-or-immediate
precondition, mirroring the tagged `evalRiPre` clauses. -/
noncomputable instance evalRiPreDecidable {width : Nat} [NeZero width] (s : MiniState width) :
    ∀ ri : WordRegImm (BitVec width), Decidable (evalRiPre s ri)
  | .reg r => evalExpPreDecidable s (.var r)
  | .imm _ => isTrue trivial

/-- HOL `Corr_Assign`: an assignment evaluates to the written state when its
expression precondition holds. HOL's Boolean guard is the decided proposition. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Assign"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Assign {width : Nat} [NeZero width] (n : Nat)
    (x : WordLangExpHOL (BitVec width)) (s : MiniState width) :
    Corr (.assign n x) s (.inr (regWrite n (some (evalExp s x)) s))
      (decide (evalExpPre s x)) := by
  intro h
  exact Eval.assign none s x n (of_decide_eq_true h)

/-- HOL `Corr_Load`: loading a register from an array evaluates to the written
state when the index register is live and the index is in bounds. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Load"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Load {width : Nat} [NeZero width] (r i : Nat) (a : Address)
    (s : MiniState width) :
    Corr (.load r i a) s
      (.inr (regWrite r (some (holEl (holFapply s.regs i).toNat (s.arrays a))) s))
      (decide (i ∈ s.regs.dom ∧ (holFapply s.regs i).toNat < (s.arrays a).length)) := by
  intro h
  rw [decide_eq_true_eq] at h
  obtain ⟨hdom, hbound⟩ := h
  cases hl : s.regs.lookup i with
  | none => exact absurd hl hdom
  | some w =>
    rw [holFapply_of_lookup hl] at hbound ⊢
    exact Eval.load none s r i a w ⟨hl, hbound⟩

/-- HOL `Corr_Store`: storing a register into the out array evaluates to the
written state when both registers are live and the index is in bounds. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Store"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Store {width : Nat} [NeZero width] (r i : Nat) (s : MiniState width) :
    Corr (.store r i) s
      (.inr (arrayWrite .out
        ((s.arrays .out).set (holFapply s.regs i).toNat (holFapply s.regs r)) s))
      (decide (r ∈ s.regs.dom ∧ i ∈ s.regs.dom ∧
        (holFapply s.regs i).toNat < (s.arrays .out).length)) := by
  intro h
  rw [decide_eq_true_eq] at h
  obtain ⟨hdomR, hdomI, hbound⟩ := h
  cases hl : s.regs.lookup i with
  | none => exact absurd hl hdomI
  | some w =>
    cases hr : s.regs.lookup r with
    | none => exact absurd hr hdomR
    | some wr =>
      rw [holFapply_of_lookup hl] at hbound ⊢
      rw [holFapply_of_lookup hr]
      exact Eval.store none s r i w wr ⟨hl, hr, hbound⟩

/-- HOL `loop_app_EQ` (`word_bignumProofScript.sml:1864`): the two shapes in
which `loop_app` returns a state with a true guard, one for each side of the
body result. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "loop_app_EQ"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem loopApp_EQ {width : Nat} [NeZero width] {γ : Type}
    (f : γ → Sum (MiniState width) (MiniState width)) (g : γ → Bool) (x : γ)
    (t : MiniState width) :
    (loopApp f g x = (.inr t, true) ↔ f x = .inr t ∧ g x = true) ∧
      (loopApp f g x = (.inl t, true) ↔
        ∃ x' : MiniState width,
          f x = .inl x' ∧ decClock x' = t ∧ g x = true ∧ x'.clock ≠ 0) := by
  cases hf : f x with
  | inl s =>
    simp only [loopApp, hf]
    constructor
    · simp
    · simp
  | inr s' =>
    simp only [loopApp, hf]
    constructor
    · simp
    · simp

/-- Flapjack-only decision procedure for the tagged single-word division
precondition, so HOL's Boolean `single_div_pre` guard can be written with
`decide`. -/
instance singleDivPreDecidable {w2 w0 w9 : Nat} [NeZero w2] [NeZero w0] [NeZero w9]
    (r2 : BitVec w2) (r0 : BitVec w0) (r9 : BitVec w9) : Decidable (singleDivPre r2 r0 r9) :=
  decidable_of_iff (r9 ≠ 0 ∧ (r2.toNat * 2 ^ w9 + r0.toNat) / r9.toNat < 2 ^ w9) Iff.rfl

/-- HOL `Corr_Add`: the carry-word addition evaluates to the two written
registers when the third register is live, both operands are well formed, the
carry operand is zero or one, and the destinations differ. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Add"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Add {width : Nat} [NeZero width]
    (n1 n2 n3 : Nat) (ri1 ri2 : WordRegImm (BitVec width)) (s : MiniState width) :
    Corr (.add n1 n2 n3 ri1 ri2) s
      (.inr (regWrite n1
        (some (singleAddWord (holFapply s.regs n3) (evalRi s ri1) (evalRi s ri2)).1)
        (regWrite n2
          (some (singleAddWord (holFapply s.regs n3) (evalRi s ri1) (evalRi s ri2)).2) s)))
      (decide (n3 ∈ s.regs.dom ∧ evalRiPre s ri1 ∧ evalRiPre s ri2 ∧
        (evalRi s ri2 ≠ 0 → evalRi s ri2 = 1) ∧ n1 ≠ n2)) := by
  intro h
  rw [decide_eq_true_eq] at h
  obtain ⟨hreg, h4, h5, hcarry, hdistinct⟩ := h
  cases hadd : singleAddWord (holFapply s.regs n3) (evalRi s ri1) (evalRi s ri2) with
  | mk r1 r2 =>
    exact Eval.add n1 n2 n3 ri1 ri2 none s r1 r2 ⟨hreg, h4, h5, hcarry, hdistinct, hadd⟩

/-- HOL `Corr_Sub`: the carry-word subtraction evaluates to the two written
registers under the same side conditions as the addition. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Sub"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Sub {width : Nat} [NeZero width]
    (n1 n2 n3 : Nat) (ri1 ri2 : WordRegImm (BitVec width)) (s : MiniState width) :
    Corr (.sub n1 n2 n3 ri1 ri2) s
      (.inr (regWrite n1
        (some (singleSubWord (holFapply s.regs n3) (evalRi s ri1) (evalRi s ri2)).1)
        (regWrite n2
          (some (singleSubWord (holFapply s.regs n3) (evalRi s ri1) (evalRi s ri2)).2) s)))
      (decide (n3 ∈ s.regs.dom ∧ evalRiPre s ri1 ∧ evalRiPre s ri2 ∧
        (evalRi s ri2 ≠ 0 → evalRi s ri2 = 1) ∧ n1 ≠ n2)) := by
  intro h
  rw [decide_eq_true_eq] at h
  obtain ⟨hreg, h4, h5, hcarry, hdistinct⟩ := h
  cases hsub : singleSubWord (holFapply s.regs n3) (evalRi s ri1) (evalRi s ri2) with
  | mk r1 r2 =>
    exact Eval.sub none s n1 n2 n3 ri1 ri2 r1 r2 ⟨hreg, h4, h5, hcarry, hdistinct, hsub⟩

/-- HOL `Corr_Mul`: the long multiplication evaluates to the two written
registers when both source registers are live and the destinations differ. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Mul"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Mul {width : Nat} [NeZero width]
    (n1 n2 n3 n4 : Nat) (s : MiniState width) :
    Corr (.mul n1 n2 n3 n4) s
      (.inr (regWrite n1
        (some (singleMul (holFapply s.regs n3) (holFapply s.regs n4) 0).1)
        (regWrite n2
          (some (singleMul (holFapply s.regs n3) (holFapply s.regs n4) 0).2) s)))
      (decide (n3 ∈ s.regs.dom ∧ n4 ∈ s.regs.dom ∧ n1 ≠ n2)) := by
  intro h
  rw [decide_eq_true_eq] at h
  obtain ⟨h3, h4, hdistinct⟩ := h
  exact Eval.mul none s n1 n2 n3 n4 ⟨h3, h4, hdistinct⟩

/-- HOL `Corr_Div`: the long division evaluates to the two written registers
when the three source registers are live, the destinations differ and the
single-word division precondition holds. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Div"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Div {width : Nat} [NeZero width]
    (n1 n2 n3 n4 n5 : Nat) (s : MiniState width) :
    Corr (.div n1 n2 n3 n4 n5) s
      (.inr (regWrite n1
        (some (singleDiv (holFapply s.regs n3) (holFapply s.regs n4) (holFapply s.regs n5)).1)
        (regWrite n2
          (some (singleDiv (holFapply s.regs n3) (holFapply s.regs n4) (holFapply s.regs n5)).2)
          s)))
      (decide (n3 ∈ s.regs.dom ∧ n4 ∈ s.regs.dom ∧ n5 ∈ s.regs.dom ∧ n1 ≠ n2 ∧
        singleDivPre (holFapply s.regs n3) (holFapply s.regs n4) (holFapply s.regs n5))) := by
  intro h
  rw [decide_eq_true_eq] at h
  obtain ⟨h3, h4, h5, hdistinct, hpre⟩ := h
  exact Eval.div none s n1 n2 n3 n4 n5 ⟨h3, h4, h5, hdistinct, hpre⟩

/-- HOL `Corr_If`: a conditional evaluates the branch chosen by the word
comparison, with the matching branch's guard conjoined to the comparison
side conditions. HOL's premise is ONE conjunction of the two branch
correctness facts, and its guard is right-associated; HOL's Boolean guard is a
`&&` of the two decided propositions and the chosen branch's Boolean guard,
since that guard is itself a `Bool`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_If"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_If {width : Nat} [NeZero width]
    (p1 : Mini (BitVec width)) (s : MiniState width)
    (f1 : Sum (MiniState width) (MiniState width)) (q1 : Bool)
    (p2 : Mini (BitVec width)) (f2 : Sum (MiniState width) (MiniState width)) (q2 : Bool)
    (c : Cmp) (r : Nat) (ri : WordRegImm (BitVec width)) :
    (Corr p1 s f1 q1 ∧ Corr p2 s f2 q2) →
      Corr (.ite c r ri p1 p2) s
        (if wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) then f1 else f2)
        (decide (r ∈ s.regs.dom) && (decide (evalRiPre s ri) &&
          if wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) then q1 else q2)) := by
  intro hpq h
  obtain ⟨h1, h2⟩ := hpq
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hdom, hpre, hq⟩ := h
  have hreg : r ∈ s.regs.dom := of_decide_eq_true hdom
  have hri : evalRiPre s ri := of_decide_eq_true hpre
  cases hcmp : wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) with
  | true =>
    have hq' : q1 = true := by simpa [hcmp] using hq
    exact Eval.ite none s c r ri p1 p2 f1 hreg hri ((if_pos hcmp).symm ▸ (h1 hq'))
  | false =>
    have hq' : q2 = true := by simpa [hcmp] using hq
    have hne : ¬ (wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) = true) := by
      rw [hcmp]
      simp
    exact Eval.ite none s c r ri p1 p2 f2 hreg hri ((if_neg hne).symm ▸ (h2 hq'))

end Flapjack.Compiler.Backend.WordBignum
