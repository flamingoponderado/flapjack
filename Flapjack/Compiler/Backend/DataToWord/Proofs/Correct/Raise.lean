import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.JumpExcLocals
import Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

/-! The raise case of the production-backed 64-bit simulation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Gc

/-- A successful source raise and its compiled word raise produce corresponding
exception values and handler states. This uses the candidate state relation,
whose compiler and oracle components have not been shown equivalent to HOL's. -/
theorem raise64 {C F : Type} (conf : Config) (secn label l1 l2 : Nat)
    (source : DataSem.State C F) (target : WordSemStateFiniteExact 64 C F)
    (locs : List (Nat × Nat)) (related : stateRel64 conf l1 l2 source target none locs)
    (name : Nat) (value : DataSem.Value) (next : DataSem.State C F)
    (lookup : DataSem.getVar name source.locals = some value)
    (jump : DataSem.jumpExc source = some next) :
    ∃ word targetNext a b return1 return2 remaining,
      DataSem.evaluate (.raise name) source = (some (.err (.raise value)), next) ∧
      WordSemStateFiniteExact.evaluate (compileControl64 conf secn label (.raise name)).1 target =
        (some (.exception (.loc a b) word), targetNext) ∧
      targetNext.ffi = next.ffi ∧ BackendProps.optionLe targetNext.stackMax next.stackMax ∧
      wordSemLastN (next.stack.length + 1) locs = (return1, return2) :: remaining ∧
      ∀ dest, stateRel64 conf return1 return2 (DataSem.setVar dest value next)
        (WordSemStateFiniteExact.setVar (adjustVar dest) word targetNext) none remaining := by
  obtain ⟨word, wordLookup⟩ := stateRel64_getVar conf l1 l2 source target none locs related name value lookup
  obtain ⟨targetNext, a, b, r1, r2, remaining, targetJump, locations, after⟩ :=
    stateRel64_jumpExc_setVar conf l1 l2 source next target locs related name value word lookup wordLookup jump
  have afterZero := after 0
  refine ⟨word, targetNext, a, b, r1, r2, remaining, ?_, ?_, afterZero.1, ?_, locations, after⟩
  · simp [DataSem.evaluate, lookup, jump]
  · simp [compileControl64, compileControl?, WordSemStateFiniteExact.evaluate, wordLookup, targetJump]
  · exact afterZero.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
