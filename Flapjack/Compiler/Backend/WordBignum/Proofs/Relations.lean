module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.CodeSubset
public import Flapjack.Compiler.Backend.WordBignum.Compile

@[expose] public section

/-! Loop-tick bookkeeping, the source's correctness predicate, and the
installed-code well-formedness predicate, ported from
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. -/
namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack

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
restated at that injection with a stronger guard. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "Corr_STRENGTHEN_TERM"
  (fmap_as_finite_support := [regs]) (words_as_type_indexed_bitvec)]
theorem Corr_STRENGTHEN_TERM {width : Nat} [NeZero width]
    (p : Mini (BitVec width)) (s : MiniState width)
    (f : Sum (MiniState width) (MiniState width)) (q : Bool)
    (f' : MiniState width) (q' : Bool) :
    Corr p s f q → (q' = true → f = .inr f' ∧ q = true) → Corr p s (.inr f') q' := by
  intro h hf hq
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

end Flapjack.Compiler.Backend.WordBignum
