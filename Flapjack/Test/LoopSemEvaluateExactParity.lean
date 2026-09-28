import Flapjack.Pancake.Semantics.LoopSemStateExact.Evaluate

/-!
# Exact loopSem `evaluate` against HOL oracle rows

Each `#guard` replays a row of
`scripts/hol-probes/loop_sem_evaluate_control_probe.out` or
`scripts/hol-probes/loop_sem_evaluate_probe.out` (HOL `EVAL` of
`loopSem$evaluate` at `:8 word`), projecting only the fields the HOL input
state fixes.  Bead `flapjack-pxgp.5`.
-/

namespace Flapjack.Test.LoopSemEvaluateExactParity

open Flapjack
open Flapjack.LoopSemStateFiniteExact

private abbrev St := LoopSemStateFiniteExact 8 Unit
private abbrev Res := Option (LoopResultExact 8)

private def holTrivialFfi : HolFfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := (), ioEvents := [] }
private def base : St :=
  { locals := .ln, globals := HolFiniteMapExact.empty, memory := fun _ => .word 0,
    mdomain := fun _ => false, shMdomain := fun _ => false, clock := 5, code := .ln,
    be := false, ffi := holTrivialFfi, baseAddr := 0, topAddr := 0 }
private def w (n : Nat) : WordLocW 8 := .word (BitVec.ofNat 8 n)
private def l17 : Spt (WordLocW 8) := sptInsert 1 (w 7) .ln
private def s17 : St := { base with locals := l17 }
private def live (ks : List Nat) : NumSet := ks.foldr (fun k t => sptInsert k () t) .ln

private def showV : WordLocW 8 → String
  | .word x => s!"Word {x.toNat}w"
  | .loc a b => s!"Loc {a} {b}"
/-- HOL-style rendering of a word location. -/
private def showW : Option (WordLocW 8) → String
  | none => "NONE"
  | some v => s!"SOME ({showV v})"
private def showWs (ws : List (WordLocW 8)) : String :=
  "[" ++ ", ".intercalate (ws.map showV) ++ "]"
private def showRes : Res → String
  | none => "NONE"
  | some (.result vs) => s!"SOME (Result {showWs vs})"
  | some (.exception v) => s!"SOME (Exception ({showV v}))"
  | some (.break n) => s!"SOME (Break {n})"
  | some (.continue n) => s!"SOME (Continue {n})"
  | some .timeOut => "SOME TimeOut"
  | some (.finalFfi _) => "SOME (FinalFFI _)"
  | some .error => "SOME Error"

/-- `(res, lookup a s'.locals, lookup b s'.locals, s'.clock)` -/
private def obs2 (p : HolLoopProg 8) (s : St) (a b : Nat) : String :=
  let (r, s') := evaluate p s
  s!"({showRes r},{showW (sptLookup a s'.locals)},{showW (sptLookup b s'.locals)},{s'.clock})"
/-- `(res, lookup a s'.locals, s'.clock)` -/
private def obs1 (p : HolLoopProg 8) (s : St) (a : Nat) : String :=
  let (r, s') := evaluate p s
  s!"({showRes r},{showW (sptLookup a s'.locals)},{s'.clock})"

private def c (n : Nat) : HolLoopExp 8 := .const (BitVec.ofNat 8 n)
private def retCode : Spt (List Nat × HolLoopProg 8) := sptInsert 1 ([5], .return [5]) .ln
private def raiseCode : Spt (List Nat × HolLoopProg 8) := sptInsert 1 ([5], .raise 5) .ln

-- loop_sem_evaluate_control_probe.out
#guard obs2 (.ite .equal 1 (.imm 7) (.assign 2 (c 1)) (.assign 2 (c 2)) (live [2])) s17 2 1 ==
  "(NONE,SOME (Word 1w),NONE,4)"
#guard obs2 (.ite .equal 1 (.imm 8) (.assign 2 (c 1)) (.assign 2 (c 2)) (live [2])) s17 2 1 ==
  "(NONE,SOME (Word 2w),NONE,4)"
#guard obs1 (.ite .equal 1 (.imm 7) .skip .skip (live [9])) s17 1 ==
  "(SOME Error,SOME (Word 7w),5)"
#guard obs1 (.loop .ln (.break 0) .ln) s17 1 == "(NONE,NONE,3)"
#guard obs1 (.loop (live [1]) (.return [1]) .ln) s17 1 == "(SOME (Result [Word 7w]),NONE,4)"
#guard obs1 (.loop .ln .skip .ln) { s17 with clock := 2 } 1 == "(SOME TimeOut,NONE,0)"
#guard obs1 (.loop .ln (.continue 0) .ln) { s17 with clock := 1 } 1 == "(SOME TimeOut,NONE,0)"
#guard obs1 (.loop .ln (.break 2) .ln) s17 1 == "(SOME (Break 1),NONE,4)"
#guard obs2 (.call (some ([3], live [1])) (some 1) [1] none) { s17 with code := retCode } 3 1 ==
  "(NONE,SOME (Word 7w),SOME (Word 7w),4)"
#guard obs2 (.call (some ([3], live [1])) (some 1) [1]
    (some (4, .skip, .assign 6 (.var 3), live [6]))) { s17 with code := retCode } 6 1 ==
  "(NONE,SOME (Word 7w),NONE,3)"
#guard obs2 (.call (some ([3], live [1])) (some 1) [1]
    (some (4, .assign 6 (.var 4), .skip, live [6]))) { s17 with code := raiseCode } 6 1 ==
  "(NONE,SOME (Word 7w),NONE,3)"
#guard obs1 (.call (some ([3], live [1])) (some 1) [1] none) { s17 with code := raiseCode } 1 ==
  "(SOME (Exception (Word 7w)),NONE,4)"
#guard obs1 (.call (some ([3, 4], live [1])) (some 1) [1] none) { s17 with code := retCode } 1 ==
  "(SOME Error,NONE,4)"
#guard obs1 (.call none (some 1) [1] none) { s17 with code := retCode } 1 ==
  "(SOME (Result [Word 7w]),NONE,4)"
#guard obs1 (.raise 1) s17 1 == "(SOME (Exception (Word 7w)),NONE,5)"
#guard obs2 (.primitive [2, 3] .addCarry [1, 1, 1]) s17 2 3 ==
  "(NONE,SOME (Word 15w),SOME (Word 0w),5)"
#guard obs1 (.locValue 2 1) { s17 with code := sptInsert 1 ([], .skip) .ln } 2 ==
  "(NONE,SOME (Loc 1 0),5)"
#guard obs1 (.locValue 2 3) { s17 with code := sptInsert 1 ([], .skip) .ln } 2 ==
  "(SOME Error,NONE,5)"
#guard obs2 (.ffi (Flapjack.Basis.Pure.MlString.MlString.implode []) 2 2 2 2 (live [2]))
    { s17 with locals := sptInsert 2 (w 0) l17 } 2 1 ==
  "(NONE,SOME (Word 0w),NONE,5)"

-- loop_sem_evaluate_probe.out
#guard obs1 (.assign 1 (c 7)) base 1 == "(NONE,SOME (Word 7w),5)"
#guard obs1 (.seq (.assign 1 (c 7)) (.return [1])) base 1 == "(SOME (Result [Word 7w]),NONE,5)"
#guard obs1 (.break 3) s17 1 == "(SOME (Break 3),SOME (Word 7w),5)"
#guard obs1 (.continue 2) s17 1 == "(SOME (Continue 2),SOME (Word 7w),5)"
#guard obs1 (.call none (some 1) [] none) { base with code := sptInsert 1 ([], .skip) .ln } 1 ==
  "(SOME Error,NONE,4)"
#guard obs1 .tick { s17 with clock := 0 } 1 == "(SOME TimeOut,NONE,0)"

def runChecks : IO Bool := do
  IO.println "PASS exact loopSem evaluate HOL parity (loop_sem_evaluate{,_control}_probe)"
  pure true

end Flapjack.Test.LoopSemEvaluateExactParity
