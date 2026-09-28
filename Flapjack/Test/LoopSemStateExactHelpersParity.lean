import Flapjack.Pancake.Semantics.LoopSemStateExact

/-! Direct HOL parity for the exact loopSem state helpers of
    `Flapjack/Pancake/Semantics/LoopSemStateExact.lean`: `set_vars`
    (`sptree$alist_insert`), `call_env` (`sptree$fromList`) and `find_code`.
    Expected values are the checked-in HOL `EVAL` rows of
    `scripts/hol-probes/loop_sem_set_vars_probe.out`,
    `loop_sem_call_env_probe.out` and `loop_sem_find_code_probe.out`.  The state
    helpers only change `locals`, so the rows are checked on the `locals` value
    (`setVars` writes `sptAlistInsert`, `callEnv` writes `sptFromList`). -/

namespace Flapjack.Test.LoopSemStateExactHelpersParity

open Flapjack
open Flapjack.LoopSemStateFiniteExact

abbrev W := WordLocW 32

private def lookups (names : List Nat) (t : Spt W) : Option (List W) :=
  names.mapM fun name => sptLookup name t

def setVarsGuard : Bool :=
  -- set_vars_basic=SOME [Word 5w; Word 7w]
  lookups [1, 2] (sptAlistInsert [1, 2] [.word 5, .word 7] .ln) == some [.word 5, .word 7] &&
  -- set_vars_missing=NONE
  lookups [3] (sptAlistInsert [1, 2] [.word 5, .word 7] .ln) == none &&
  -- set_vars_duplicate=SOME [Word 5w]
  lookups [1] (sptAlistInsert [1, 1] [.word 5, .word 7] .ln) == some [.word 5] &&
  -- set_vars_short_values=NONE
  lookups [1, 2] (sptAlistInsert [1, 2] [.word 5] .ln) == none &&
  -- set_vars_overwrite=SOME [Word 9w]
  lookups [1] (sptAlistInsert [1] [.word 9] (sptInsert 1 (.word 1) .ln)) == some [.word 9] &&
  -- set_vars_empty=NONE
  lookups [1] (sptAlistInsert ([] : List Nat) ([] : List W) .ln) == none

def callEnvGuard : Bool :=
  -- arg_zero=SOME (Word 5w), arg_one=SOME (Word 7w), arg_missing=NONE
  sptLookup 0 (sptFromList ([.word 5, .word 7] : List W)) == some (.word 5) &&
  sptLookup 1 (sptFromList ([.word 5, .word 7] : List W)) == some (.word 7) &&
  sptLookup 2 (sptFromList ([.word 5, .word 7] : List W)) == none

private def code2 : Spt (List Nat × HolLoopProg 32) := sptInsert 5 ([1, 2], .skip) .ln
private def code1 : Spt (List Nat × HolLoopProg 32) := sptInsert 9 ([7], .skip) .ln
private def codeDup : Spt (List Nat × HolLoopProg 32) := sptInsert 5 ([1, 1], .skip) .ln

private def envLookup (key : Nat) :
    Option (Spt W × HolLoopProg 32) → Option W
  | some (env, _) => sptLookup key env
  | none => none

def findCodeGuard : Bool :=
  -- find_code_label_first=SOME (Word 3w), find_code_label_second=SOME (Word 4w)
  envLookup 1 (findCode (some 5) [.word 3, .word 4] code2) == some (.word 3) &&
  envLookup 2 (findCode (some 5) [.word 3, .word 4] code2) == some (.word 4) &&
  -- find_code_label_len_mismatch=NONE, find_code_label_missing=NONE
  (findCode (some 5) [.word 3] code2).isNone &&
  (findCode (some 6) [.word 3, .word 4] code2).isNone &&
  -- find_code_link_first=SOME (Word 3w), find_code_link_wrong_len=NONE
  envLookup 7 (findCode none [.word 3, .loc 9 0] code1) == some (.word 3) &&
  (findCode none [.loc 9 0] code1).isNone &&
  -- find_code_empty_args=NONE, find_code_bad_last=NONE
  (findCode none ([] : List W) code1).isNone &&
  (findCode none [.word 3, .word 4] code1).isNone &&
  -- find_code_dup_first=SOME (Word 5w)
  envLookup 1 (findCode (some 5) [.word 5, .word 7] codeDup) == some (.word 5)

#guard setVarsGuard
#guard callEnvGuard
#guard findCodeGuard

def runChecks : IO Bool := do
  let ok := setVarsGuard && callEnvGuard && findCodeGuard
  IO.println (if ok then "PASS exact loopSem state helpers HOL parity"
    else "FAIL exact loopSem state helpers HOL parity")
  pure ok

end Flapjack.Test.LoopSemStateExactHelpersParity
