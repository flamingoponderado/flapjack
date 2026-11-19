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

end Flapjack.Compiler.Backend.WordBignum
