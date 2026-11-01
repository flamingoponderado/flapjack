import Flapjack.Compiler.Backend.Semantics.DataSem.State
import Flapjack.Compiler.Backend.Semantics.WordSem.State
import Flapjack.Compiler.Backend.DataToWord.Variables

/-! Stack-frame relations used by data-to-word garbage-collector correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- The common condition for an ordinary data frame and its word frame. This
is a factoring of the first case of `stack_rel_def`, not a HOL declaration. -/
def stackEnvRel {width : Nat} [NeZero width] (dataSize wordSize : Option Nat)
    (env : Spt DataSem.Value) (nonGc gc : List (Nat × WordLocW width)) : Prop :=
  (∀ pair ∈ gc, pair.1 ≠ 0 ∧ pair.1 % 2 = 0) ∧ dataSize = wordSize ∧
  (∀ pair ∈ nonGc, pair.1 = 0) ∧ (gc.map Prod.fst).Nodup ∧
  ∀ n, (sptLookup n env).isSome = true ↔ (sptLookup (DataToWord.adjustVar n) (sptFromAList gc)).isSome = true

/-- A data frame and word frame have corresponding sizes, handlers, live
names, and cutsets. Positive-width bit vectors represent HOL words. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "stack_rel_def"
  (words_as_type_indexed_bitvec)]
def stackRel {width : Nat} [NeZero width] : DataSem.Stack → WordSemStackFrame width → Prop
  | .env size env, .stackFrame wordSize nonGc gc none => stackEnvRel size wordSize env nonGc gc
  | .exc size env handler, .stackFrame wordSize nonGc gc (some (wordHandler, _, _)) =>
      stackEnvRel size wordSize env nonGc gc ∧ wordHandler = handler
  | _, _ => False

/-- The default data global value is numeric zero when no global pointer is
installed. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "the_global_def"]
def theGlobal (global : Option Nat) : DataSem.Value :=
  (global.map (DataSem.Value.refPtr true)).getD (.number 0)

/-- Check the return location stored under key zero in a word frame's
non-GC cutset, using HOL's first-match association lookup. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "contains_loc_def"
  (words_as_type_indexed_bitvec)]
def containsLoc {width : Nat} [NeZero width] : WordSemStackFrame width → Nat × Nat → Prop
  | .stackFrame _ nonGc _ _, (l1, l2) => sptAListLookup 0 nonGc = some (.loc l1 l2)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
