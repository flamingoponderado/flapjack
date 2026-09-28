import Flapjack.Pancake.CrepToLoop.ContextExact

/-!
# Exact-carrier parity for `crep_to_loop$compile_prog_def`

Replays every direct HOL-EVAL row of
`scripts/hol-probes/crep_to_loop_compile_prog_probe.out` against the tagged
exact-carrier port `compileProgHOLExact` (`@[hol ... "compile_prog_def"
(words_as_type_indexed_bitvec)]`) over `CrepProgHOL 8` / `HolLoopProg 8`:

* `cp_fnums`, `cp_params`, `cp_body`, `cp_length` for a one-entry program
  whose body simplifies (`crep_arith$simp_prog`) and optimises
  (`loop_live$optimise`);
* `cp_call_fnums`, `cp_call_params`, `cp_call_body` for a one-entry program
  whose body calls `«f»`, exercising the `make_funcs` label (`first_name = 64`)
  through `comp_func`'s `find_lab`.

`compileProgHOLExact` is defined through well-founded/executable helpers
(`compFuncHOLExact`, `crepSimpProgHOL`, `optimiseHOL`), so the rows are
replayed through `#guard` on the executable definitions and the
`runChecks`-computed predicates, matching the `LoopCallCompHOLParity` /
`CrepArithExactParity` idiom; no proof term is produced and no trusted
evaluator axiom is attached.
-/

set_option linter.unusedSimpArgs false

namespace Flapjack.Test.CrepToLoopCompileProgParity

open Flapjack
open Flapjack.Basis.Pure.MlString

private abbrev P := CrepProgHOL 8
private abbrev L := HolLoopProg 8

private def prog : List (MlString × List Nat × P) :=
  [(ofString "f", [1, 2], .assign 1 (.crepOp .mul [.const 2, .const 3]))]

private def progCall : List (MlString × List Nat × P) :=
  [(ofString "f", [], .call none (ofString "f") [.const 7])]

private def isMarkSeqMarkSkip : L → Bool
  | .mark (.seq (.mark .skip) (.mark .skip)) => true
  | _ => false

private def isCallBody : L → Bool
  | .mark (.seq (.mark (.assign 1 (.const 7)))
      (.mark (.seq (.mark (.call none (some 64) [1] none)) (.mark .skip)))) => true
  | _ => false

/-- All direct `compile_prog` HOL rows over the exact carriers. -/
def compileProgHOLGuard : Bool :=
  -- cp_fnums=[64]
  (compileProgHOLExact (width := 8) .riscv prog).map Prod.fst == [64] &&
  -- cp_params=[[0; 1]]
  (compileProgHOLExact (width := 8) .riscv prog).map (fun e => e.2.1) == [[0, 1]] &&
  -- cp_length=1
  (compileProgHOLExact (width := 8) .riscv prog).length == 1 &&
  -- cp_body=[Mark (Seq (Mark Skip) (Mark Skip))]
  (match compileProgHOLExact (width := 8) .riscv prog with
   | [(64, [0, 1], body)] => isMarkSeqMarkSkip body
   | _ => false) &&
  -- cp_call_fnums=[64]
  (compileProgHOLExact (width := 8) .riscv progCall).map Prod.fst == [64] &&
  -- cp_call_params=[[]]
  (compileProgHOLExact (width := 8) .riscv progCall).map (fun e => e.2.1) == [[]] &&
  -- cp_call_body=[Mark (Seq (Mark (Assign 1 (Const 7w)))
  --   (Mark (Seq (Mark (Call NONE (SOME 64) [1] NONE)) (Mark Skip))))]
  (match compileProgHOLExact (width := 8) .riscv progCall with
   | [(64, [], body)] => isCallBody body
   | _ => false)

#guard compileProgHOLGuard

def runChecks : IO Bool := do
  if compileProgHOLGuard then
    IO.println "PASS exact compileProgHOLExact matches all 7 crep_to_loop compile_prog_def HOL rows"
  else
    IO.println "FAIL exact compileProgHOLExact matches all 7 crep_to_loop compile_prog_def HOL rows"
  pure compileProgHOLGuard

end Flapjack.Test.CrepToLoopCompileProgParity
