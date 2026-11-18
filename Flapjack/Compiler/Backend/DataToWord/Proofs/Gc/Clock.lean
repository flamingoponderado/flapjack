module

public import Flapjack.Compiler.Backend.Semantics.DataSem.State
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
public import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StateLaws

@[expose] public section

/-! Clock identities used in the data-to-word allocation proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

/-- Incrementing and then decrementing either evaluator's clock restores its state. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "dec_clock_inc_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem decClockIncClock {width : Nat} [NeZero width] {C F D G : Type}
    (source : DataSem.State C F) (target : WordSemStateFiniteExact width D G) :
    DataSem.decClock { source with clock := source.clock + 1 } = source ∧
    WordSemStateFiniteExact.decClock { target with clock := target.clock + 1 } = target := by
  simp [DataSem.decClock, WordSemStateFiniteExact.decClock]

/-- Increasing the clock does not change a local-variable lookup. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_var_inc_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarIncClock {width : Nat} [NeZero width] {C F : Type}
    (n k : Nat) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.getVar n (WordSemStateFiniteExact.incClock k s) =
      WordSemStateFiniteExact.getVar n s := rfl

/-- Increasing the clock does not change a list of local-variable lookups. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "get_vars_inc_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem getVarsIncClock {width : Nat} [NeZero width] {C F : Type}
    (ns : List Nat) (k : Nat) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.getVars ns (WordSemStateFiniteExact.incClock k s) =
      WordSemStateFiniteExact.getVars ns s := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [WordSemStateFiniteExact.getVars, getVarIncClock, ih]

/-- Local-variable updates commute with increasing the clock. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "set_var_inc_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem setVarIncClock {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (x : WordLocW width) (k : Nat) (s : WordSemStateFiniteExact width C F) :
    WordSemStateFiniteExact.setVar n x (WordSemStateFiniteExact.incClock k s) =
      WordSemStateFiniteExact.incClock k (WordSemStateFiniteExact.setVar n x s) := rfl

/-- The GC theory's clock increment shares the word-semantics implementation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "inc_clock_def"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
abbrev gcIncClock {width : Nat} [NeZero width] {C F : Type}
    (n : Nat) (state : WordSemStateFiniteExact width C F) : WordSemStateFiniteExact width C F :=
  WordSemStateFiniteExact.incClock n state

/-- Zero clock increment leaves the state unchanged. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "inc_clock_0"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gcIncClock_zero {width : Nat} [NeZero width] {C F : Type}
    (state : WordSemStateFiniteExact width C F) : gcIncClock 0 state = state :=
  WordSemStateFiniteExact.incClock_zero state

/-- Successive clock increments compose by addition. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "inc_clock_inc_clock"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem gcIncClock_incClock {width : Nat} [NeZero width] {C F : Type}
    (n m : Nat) (state : WordSemStateFiniteExact width C F) :
    gcIncClock n (gcIncClock m state) = gcIncClock (n + m) state :=
  WordSemStateFiniteExact.incClock_incClock n m state

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
