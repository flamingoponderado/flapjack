import Flapjack.Compiler.Backend.BvlInline.Proofs.StateRel
import Flapjack.Compiler.Backend.Semantics.BvlSem.Call

/-! Code lookup facts for the tick-removal simulation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem

/-- Lookup preserves the selected arguments and transforms only the body.
This Flapjack lemma factors the code lookup reasoning in evaluator simulation. -/
theorem findCode_removeTicks (dest : Option Nat) (args : List BvlSem.Value)
    (code : Spt (Nat × Bvl.Exp)) :
    findCode dest args (sptMap (fun (arity, body) => (arity, removeTicksSing body)) code) =
      (findCode dest args code).map (fun (values, body) => (values, removeTicksSing body)) := by
  unfold findCode
  simp only [sptLookup_sptMap]
  repeat' (split <;> try simp_all)
  all_goals aesop

/-- Related states resolve calls to the same arguments and transformed body. -/
theorem stateRel_findCode {C F : Type} (s t : State C F) (related : stateRel s t)
    (dest : Option Nat) (args : List BvlSem.Value) :
    findCode dest args t.code =
      (findCode dest args s.code).map (fun (values, body) => (values, removeTicksSing body)) := by
  have code := congrArg (fun state : State C F => state.code) related.1
  rw [code]
  exact findCode_removeTicks dest args s.code

/-- Decrementing the clocks of related states preserves the relation. -/
theorem stateRel_decClock {C F : Type} (s t : State C F) (related : stateRel s t) (amount : Nat) :
    stateRel (decClock amount s) (decClock amount t) := by
  obtain ⟨fields, compiler⟩ := related
  constructor
  · have clock := congrArg (fun state : State C F => state.clock) fields
    cases s
    cases t
    simp_all [decClock]
  · simpa [decClock] using compiler

end Flapjack.Compiler.Backend.BvlInline.Proofs
