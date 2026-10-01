import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoves.MoveHead

namespace Flapjack.Test.WordAllocMoveHeadParity

open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordAlloc

/-- Apply the actual full theorem at arbitrary width, host/configuration
carriers and states. This is not a simplified evaluator or an assumed target run. -/
example {width : Nat} [NeZero width] {C : Type} {F : Type}
    (priority : Nat) (moves : List (Nat × Nat))
    (state result : WordSemStateFiniteExact width C F) (x y : Nat)
    (evaluation : evaluate (.move priority moves) state = (none, result))
    (present : sptDomain state.locals y)
    (sourceNotWritten : y ∉ moves.map Prod.fst)
    (destinationNotWritten : x ∉ moves.map Prod.fst) :
    evaluate (.move priority ((x, y) :: moves)) state =
      (none, { result with locals := sptInsert x ((sptLookup y state.locals).getD (.word 0)) result.locals }) :=
  movEvalHead priority moves state result x y evaluation present sourceNotWritten destinationNotWritten

/-- Check the guarded fallback independence for arbitrary native Word/Loc payloads. -/
example {width : Nat} [NeZero width] (tree : Spt (WordLocW width))
    (key : Nat) (present : sptDomain tree key) (first second : WordLocW width) :
    (sptLookup key tree).getD first = (sptLookup key tree).getD second :=
  moveHeadValue_defaultIndependent tree key present first second

/-- Fresh original `mh_empty`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 1 C F) :
    let state := { base with locals := sptFromAList [(1, .word 1)], clock := 17 }
    let output := evaluate (.move 0 [(2, 1)]) state
    output.1 = none ∧ sptToAList output.2.locals = [(1, .word 1), (2, .word 1)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars]

/-- Fresh original `mh_single`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 32 C F) :
    let state := { base with locals := sptFromAList [(1, .word 9), (4, .word 7)], clock := 17 }
    let output := evaluate (.move 7 [(5, 1), (4, 1)]) state
    output.1 = none ∧ sptToAList output.2.locals = [(1, .word 9), (5, .word 9), (4, .word 9)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars]

/-- Fresh original `mh_parallel`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 64 C F) :
    let state := { base with locals := sptFromAList [(1, .word 9), (2, .loc 7 8), (4, .word 3), (5, .word 4)], clock := 17 }
    let output := evaluate (.move 9 [(6, 2), (4, 1), (5, 2)]) state
    output.1 = none ∧ sptToAList output.2.locals = [(1, .word 9), (5, .loc 7 8), (4, .word 9), (2, .loc 7 8), (6, .loc 7 8)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars]

/-- Fresh original `mh_overwrite`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 80 C F) :
    let state := { base with locals := sptFromAList [(1, .word 9), (5, .word 123)], clock := 17 }
    let output := evaluate (.move 99 [(5, 1), (4, 1)]) state
    output.1 = none ∧ sptToAList output.2.locals = [(1, .word 9), (5, .word 9), (4, .word 9)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars]

/-- Fresh original `mh_self`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 32 C F) :
    let state := { base with locals := sptFromAList [(1, .word 9), (5, .word 12)], clock := 17 }
    let output := evaluate (.move 4 [(5, 5), (4, 1)]) state
    output.1 = none ∧ sptToAList output.2.locals = [(1, .word 9), (5, .word 12), (4, .word 9)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars]

/-- Fresh original `mh_same_source`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 1 C F) :
    let state := { base with locals := sptFromAList [(1, .word 1)], clock := 17 }
    let output := evaluate (.move 3 [(6, 1), (4, 1), (5, 1)]) state
    output.1 = none ∧ sptToAList output.2.locals = [(1, .word 1), (5, .word 1), (4, .word 1), (6, .word 1)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars]

/-- Fresh original `mh_malformed`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 64 C F) :
    let state := { base with locals := .bs (.bn .ln .ln) (.word 7) (.ls (.loc 3 4)), clock := 17 }
    let output := evaluate (.move 8 [(5, 0), (4, 1)]) state
    output.1 = none ∧ sptToAList output.2.locals = [(1, .loc 3 4), (5, .word 7), (0, .word 7), (4, .loc 3 4)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars]

/-- Fresh original `mh_huge`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 80 C F) :
    let state := { base with locals := sptFromAList [(1, .word 9)], clock := 17 }
    let output := evaluate (.move 0 [(1208925819614629174706176, 1), (4, 1)]) state
    output.1 = none ∧ sptToAList output.2.locals = [(1, .word 9), (1208925819614629174706176, .word 9), (4, .word 9)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVars]

/-- Fresh original `mh_missing_source`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 32 C F) :
    let state := { base with locals := sptFromAList [(1, .word 9)], clock := 17 }
    let output := evaluate (.move 0 [(5, 2)]) state
    output.1 = some .error ∧ sptToAList output.2.locals = [(1, .word 9)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate, WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar]

/-- Fresh original `mh_duplicate_destination`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 32 C F) :
    let state := { base with locals := sptFromAList [(1, .word 9)], clock := 17 }
    let output := evaluate (.move 0 [(5, 1), (5, 1)]) state
    output.1 = some .error ∧ sptToAList output.2.locals = [(1, .word 9)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate]

/-- Fresh original `mh_bad_tail`: exact result, Spt traversal and unchanged clock.
All other fields of the native state remain arbitrary. -/
example {C F : Type} (base : WordSemStateFiniteExact 64 C F) :
    let state := { base with locals := sptFromAList [(1, .word 9)], clock := 17 }
    let output := evaluate (.move 0 [(5, 1), (4, 1), (4, 1)]) state
    output.1 = some .error ∧ sptToAList output.2.locals = [(1, .word 9)] ∧ output.2.clock = 17 := by
  simp (config := { ground := true, decide := true }) [evaluate]

end Flapjack.Test.WordAllocMoveHeadParity
