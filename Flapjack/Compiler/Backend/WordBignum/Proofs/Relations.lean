module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.CodeSubset
public import Flapjack.Compiler.Backend.WordBignum.Compile
public import Flapjack.Misc.Tailrec

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
with the guard unchanged. HOL's `bool` guard is a `Prop`, as in the tagged
`SHORT_TAILREC` rendering `holShortTailrec` that iterates this step. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "loop_app_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def loopApp {width : Nat} [NeZero width] {β γ : Type}
    (f : γ → Sum (MiniState width) β) (g : γ → Prop) (x : γ) :
    Sum (MiniState width) β × Prop :=
  match f x with
  | .inl s => (.inl (decClock s), g x ∧ s.clock ≠ 0)
  | .inr s' => (.inr s', g x)

/-- A clock-guarded body step: at clock zero the state and guard `F` are
returned unchanged, otherwise the body runs on the register-deleted,
clock-decremented state. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "tick_before_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def tickBefore {width : Nat} [NeZero width] (vs : List Nat)
    (f : MiniState width → MiniState width × Prop) (s : MiniState width) :
    MiniState width × Prop :=
  if s.clock = 0 then (s, False) else f (deleteVars vs (decClock s))

/-- The source's correctness predicate: when the guard holds, the program
evaluates at the top level to the given result. HOL's `bool` guard is a
`Prop`, matching the `Prop`-valued preconditions of the tagged machine-code
functions and the `holShortTailrecPre` rendering of `SHORT_TAILREC_PRE`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_def"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
def Corr {width : Nat} [NeZero width] (prog : Mini (BitVec width)) (s : MiniState width)
    (s1 : Sum (MiniState width) (MiniState width)) (p : Prop) : Prop :=
  p → Eval none s prog s1

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
guard is HOL's `bool` argument of `Corr`, rendered as a `Prop`, so HOL's `T` is
`True` and HOL's `q1 /\ q2` is `∧`. -/

/-- HOL `Corr_Skip`: the guard holds and `Skip` evaluates to itself. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Skip"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Skip {width : Nat} [NeZero width] (s : MiniState width) :
    Corr .skip s (.inr s) True := by
  intro _
  exact Eval.skip none s

/-- HOL `Corr_Continue`: `Continue` evaluates to the left injection. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Continue"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Continue {width : Nat} [NeZero width] (s : MiniState width) :
    Corr .continue s (.inl s) True := by
  intro _
  exact Eval.continue none s

/-- HOL `Corr_Delete`: deleting registers evaluates to the updated state. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Delete"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Delete {width : Nat} [NeZero width] (vs : List Nat) (s : MiniState width) :
    Corr (.delete vs) s (.inr (deleteVars vs s)) True := by
  intro _
  exact Eval.delete none vs s

/-- HOL `Corr_Swap`: swapping the two input arrays evaluates to the swapped
state. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Swap"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Swap {width : Nat} [NeZero width] (s : MiniState width) :
    Corr .swap s
      (.inr (arrayWrite .in1 (s.arrays .in2) (arrayWrite .in2 (s.arrays .in1) s))) True := by
  intro _
  exact Eval.swap none s

/-- HOL `Corr_Seq`: two guarded evaluations compose, with the conjunction of
their guards. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Seq"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Seq {width : Nat} [NeZero width]
    (p2 : Mini (BitVec width)) (s1 : MiniState width)
    (s2 : Sum (MiniState width) (MiniState width)) (q2 : Prop)
    (p1 : Mini (BitVec width)) (s : MiniState width) (q1 : Prop) :
    Corr p2 s1 s2 q2 → Corr p1 s (.inr s1) q1 → Corr (.seq p1 p2) s s2 (q1 ∧ q2) := by
  intro h2 h1 h
  exact Eval.seq none s s1 s2 p1 p2 (h1 h.1) (h2 h.2)

/-- HOL `Corr_Seq_alt`: the same composition with an extra Boolean premise on
the continuation. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Seq_alt"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Seq_alt {width : Nat} [NeZero width]
    (b : Prop) (p2 : Mini (BitVec width)) (s1 : MiniState width)
    (s2 : Sum (MiniState width) (MiniState width)) (q2 : Prop)
    (p1 : Mini (BitVec width)) (s : MiniState width) (q1 : Prop) :
    (b → Corr p2 s1 s2 q2) → Corr p1 s (.inr s1) q1 →
      b → Corr (.seq p1 p2) s s2 (q1 ∧ q2) := by
  intro hb h1 hq h
  exact Eval.seq none s s1 s2 p1 p2 (h1 h.1) (hb hq h.2)

/-- HOL `Corr_STRENGTHEN_TERM`: a guarded evaluation to a right injection can be
restated at that injection with a stronger guard. HOL binds `f'` and `q'` after
the first premise, so Lean quantifies them in the conclusion. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_STRENGTHEN_TERM"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_STRENGTHEN_TERM {width : Nat} [NeZero width]
    (p : Mini (BitVec width)) (s : MiniState width)
    (f : Sum (MiniState width) (MiniState width)) (q : Prop) :
    Corr p s f q → ∀ (f' : MiniState width) (q' : Prop),
      (q' → f = .inr f' ∧ q) → Corr p s (.inr f') q' := by
  intro h f' q' hf hq
  obtain ⟨hfinr, hqtrue⟩ := hf hq
  rw [hfinr] at h
  exact h hqtrue

/-- HOL `Corr_move_pre`: conjoining a premise with the guard is the same as
guarding the evaluation. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_move_pre"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_move_pre {width : Nat} [NeZero width]
    (b : Prop) (code : Mini (BitVec width)) (s : MiniState width)
    (f : Sum (MiniState width) (MiniState width)) (p : Prop) :
    (b → Corr code s f p) ↔ Corr code s f (b ∧ p) := by
  simp only [Corr]
  exact ⟨fun h hbp => h hbp.1 hbp.2, fun h hb hp => h ⟨hb, hp⟩⟩

/-- HOL `Corr_Assign`: an assignment evaluates to the written state when its
expression precondition holds. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Assign"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Assign {width : Nat} [NeZero width] (n : Nat)
    (x : WordLangExpHOL (BitVec width)) (s : MiniState width) :
    Corr (.assign n x) s (.inr (regWrite n (some (evalExp s x)) s))
      (evalExpPre s x) := by
  intro h
  exact Eval.assign none s x n h

/-- HOL `Corr_Load`: loading a register from an array evaluates to the written
state when the index register is live and the index is in bounds. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Load"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Load {width : Nat} [NeZero width] (r i : Nat) (a : Address)
    (s : MiniState width) :
    Corr (.load r i a) s
      (.inr (regWrite r (some (holEl (holFapply s.regs i).toNat (s.arrays a))) s))
      (i ∈ s.regs.dom ∧ (holFapply s.regs i).toNat < (s.arrays a).length) := by
  intro h
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
      (r ∈ s.regs.dom ∧ i ∈ s.regs.dom ∧
        (holFapply s.regs i).toNat < (s.arrays .out).length) := by
  intro h
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
    (f : γ → Sum (MiniState width) (MiniState width)) (g : γ → Prop) (x : γ)
    (t : MiniState width) :
    (loopApp f g x = (.inr t, True) ↔ f x = .inr t ∧ g x) ∧
      (loopApp f g x = (.inl t, True) ↔
        ∃ x' : MiniState width,
          f x = .inl x' ∧ decClock x' = t ∧ g x ∧ x'.clock ≠ 0) := by
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
      (n3 ∈ s.regs.dom ∧ evalRiPre s ri1 ∧ evalRiPre s ri2 ∧
        (evalRi s ri2 ≠ 0 → evalRi s ri2 = 1) ∧ n1 ≠ n2) := by
  intro h
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
      (n3 ∈ s.regs.dom ∧ evalRiPre s ri1 ∧ evalRiPre s ri2 ∧
        (evalRi s ri2 ≠ 0 → evalRi s ri2 = 1) ∧ n1 ≠ n2) := by
  intro h
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
      (n3 ∈ s.regs.dom ∧ n4 ∈ s.regs.dom ∧ n1 ≠ n2) := by
  intro h
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
      (n3 ∈ s.regs.dom ∧ n4 ∈ s.regs.dom ∧ n5 ∈ s.regs.dom ∧ n1 ≠ n2 ∧
        singleDivPre (holFapply s.regs n3) (holFapply s.regs n4) (holFapply s.regs n5)) := by
  intro h
  obtain ⟨h3, h4, h5, hdistinct, hpre⟩ := h
  exact Eval.div none s n1 n2 n3 n4 n5 ⟨h3, h4, h5, hdistinct, hpre⟩

/-- HOL `Corr_If`: a conditional evaluates the branch chosen by the word
comparison, with the matching branch's guard conjoined to the comparison
side conditions. HOL's premise is ONE conjunction of the two branch
correctness facts, and its guard is right-associated. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_If"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_If {width : Nat} [NeZero width]
    (p1 : Mini (BitVec width)) (s : MiniState width)
    (f1 : Sum (MiniState width) (MiniState width)) (q1 : Prop)
    (p2 : Mini (BitVec width)) (f2 : Sum (MiniState width) (MiniState width)) (q2 : Prop)
    (c : Cmp) (r : Nat) (ri : WordRegImm (BitVec width)) :
    (Corr p1 s f1 q1 ∧ Corr p2 s f2 q2) →
      Corr (.ite c r ri p1 p2) s
        (if wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) then f1 else f2)
        (r ∈ s.regs.dom ∧ (evalRiPre s ri ∧
          if wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) then q1 else q2)) := by
  intro hpq h
  obtain ⟨h1, h2⟩ := hpq
  obtain ⟨hreg, hri, hq⟩ := h
  cases hcmp : wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) with
  | true =>
    have hq' : q1 := by simpa [hcmp] using hq
    exact Eval.ite none s c r ri p1 p2 f1 hreg hri ((if_pos hcmp).symm ▸ (h1 hq'))
  | false =>
    have hq' : q2 := by simpa [hcmp] using hq
    have hne : ¬ (wordCmpHOL c (evalExp s (.var r)) (evalRi s ri) = true) := by
      rw [hcmp]
      simp
    exact Eval.ite none s c r ri p1 p2 f2 hreg hri ((if_neg hne).symm ▸ (h2 hq'))

/-- Flapjack-only inhabitant of the mini-language state, so the reviewed
`holShortTailrec`/`holShortTailrecPre` renderings of HOL's `SHORT_TAILREC` and
`SHORT_TAILREC_PRE` (which need `Nonempty` carriers for HOL's `ARB`) can be used
at this state type; it adds no hypothesis to any tagged statement. -/
instance miniStateNonempty {width : Nat} [NeZero width] : Nonempty (MiniState width) :=
  ⟨⟨HolFiniteMapExact.empty, fun _ => [], 0⟩⟩

/-- HOL `Corr_LoopBody` (`word_bignumProofScript.sml:1483`): a loop body whose
one iteration is described by `f` under guard `q` evaluates to the
`SHORT_TAILREC` of the clock-ticking `loop_app f q`, under its
`SHORT_TAILREC_PRE`. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_LoopBody"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_LoopBody {width : Nat} [NeZero width] (p : Mini (BitVec width))
    (f : MiniState width → Sum (MiniState width) (MiniState width))
    (q : MiniState width → Prop) :
    (∀ s, Corr p s (f s) (q s)) →
      ∀ s, Corr (.loopBody p) s (.inr (holShortTailrec (loopApp f q) s))
        (holShortTailrecPre (loopApp f q) s) := by
  intro hbody s hpre
  refine holShortTailrecPre_induct (f := loopApp f q)
    (fun s => Eval none s (.loopBody p) (.inr (holShortTailrec (loopApp f q) s))) ?_ s hpre
  rintro s ⟨_, hguard, ih⟩
  cases hfs : f s with
  | inl s' =>
    have happ : loopApp f q s = (.inl (decClock s'), q s ∧ s'.clock ≠ 0) := by
      simp only [loopApp, hfs]
    rw [happ] at hguard ih
    have hev := hbody s hguard.1
    rw [hfs] at hev
    have hnext := ih (decClock s') rfl
    rw [holShortTailrec_inl happ]
    exact Eval.loopBodyContinue none s s' _ p hev hguard.2 hnext
  | inr s' =>
    have happ : loopApp f q s = (.inr s', q s) := by
      simp only [loopApp, hfs]
    rw [happ] at hguard
    have hev := hbody s hguard
    rw [hfs] at hev
    rw [holShortTailrec_inr happ]
    exact Eval.loopBodyReturn none s p s' hev

/-- HOL `Corr_Loop_lemma` (`word_bignumProofScript.sml:1504`): a non-recursive
loop runs its body once from the register-deleted, clock-decremented state,
guarded by a non-zero clock. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_Loop_lemma"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_Loop_lemma {width : Nat} [NeZero width] (p : Mini (BitVec width))
    (f : MiniState width → MiniState width) (q : MiniState width → Prop)
    (vs : List Nat) (s : MiniState width) :
    (∀ s, Corr (.loopBody p) s (.inr (f s)) (q s)) →
      Corr (.loop false vs p) s (.inr (f (deleteVars vs (decClock s))))
        (q (deleteVars vs (decClock s)) ∧ s.clock ≠ 0) := by
  intro hbody ⟨hq, hclock⟩
  exact Eval.loop none s p vs _ false (hbody _ hq) hclock

end Flapjack.Compiler.Backend.WordBignum
