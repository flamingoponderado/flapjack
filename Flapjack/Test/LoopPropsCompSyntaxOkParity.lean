import Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOk

/-!
# Exact `comp_syntax_ok_def` observations

Kernel-checked replay of the HOL EVAL rows in
`scripts/hol-probes/loop_props_comp_syntax_ok_probe.out` for
`loopProps$comp_syntax_ok_def` (`loopPropsScript.sml:57-73`) over the exact
width-indexed `HolLoopProg 8` carrier and `NumSet = Spt Unit` live sets.

`compSyntaxOkHOL` is noncomputable (the `If` set-extension condition is HOL's
classical existential over `List Nat`; see the module header of
`Flapjack.Pancake.Semantics.LoopProps.CompSyntaxOk`), so the rows are
kernel-checked equalities rather than runtime `#guard` evaluations, exactly as
the noncomputable HOL `EXISTS` cannot be reduced by `EVAL`. The `If` rows in
the probe print the residual existential; here the matching case is discharged
by exhibiting the witness list, and the structurally non-matching case is
recorded as its literal residual existential (undecided on both sides). -/

namespace Flapjack.Test.LoopPropsCompSyntaxOkParity

open Flapjack

private def live8 : NumSet := sptInsert 8 () .ln

private def live9 : NumSet := sptInsert 9 () .ln

private def afterLocValue : NumSet := sptInsert 1 () live8

/-- `live8` and `live9` are unequal: key 8 is present in the first and absent
    in the second, so a hypothetical equality would identify `some ()` with
    `none`. This is stated through `sptLookup` because the derived
    `DecidableEq Spt` is a recursive instance that does not reduce under
    `decide`/`rfl`. -/
theorem live8_ne_live9 : live8 ≠ live9 := by
  intro h
  have h1 : sptLookup 8 live8 = some () := by simp [live8, sptInsert, sptLookup]
  have h2 : sptLookup 8 live9 = none := by simp [live9, sptInsert, sptLookup]
  rw [h] at h1
  rw [h2] at h1
  cases h1

example : compSyntaxOkHOL (width := 8) live8 (.skip : HolLoopProg 8) = true :=
  rfl

example : compSyntaxOkHOL (width := 8) live8
    (.assign 4 (.const (0 : BitVec 8)) : HolLoopProg 8) = true := rfl

example : compSyntaxOkHOL (width := 8) live8 (.locValue 3 4 : HolLoopProg 8) = true :=
  rfl

example : compSyntaxOkHOL (width := 8) live8 (.load32 5 6 : HolLoopProg 8) = true :=
  rfl

example : compSyntaxOkHOL (width := 8) live8 (.loadByte 7 9 : HolLoopProg 8) = true :=
  rfl

example : compSyntaxOkHOL (width := 8) live8 (.break 11 : HolLoopProg 8) = true :=
  rfl

example : compSyntaxOkHOL (width := 8) live8
    (.arith (.div 7 8 9) : HolLoopProg 8) = true := rfl

example : compSyntaxOkHOL (width := 8) live8
    (.seq (.locValue 1 3) (.assign 1 (.var 1)) : HolLoopProg 8) = true := rfl

/-- `Seq` threads the live set through `cutSetsHOL`: after `LocValue 1 3` the
    nested `Loop` must use `insert 1 () live8`, which it does. -/
example : compSyntaxOkHOL (width := 8) live8
    (.seq (.locValue 1 3)
      (.loop afterLocValue .skip afterLocValue) : HolLoopProg 8) = true := by
  simp [compSyntaxOkHOL, afterLocValue, cutSetsHOL]

example : compSyntaxOkHOL (width := 8) live8
    (.loop live8 .skip live8 : HolLoopProg 8) = true := by
  simp [compSyntaxOkHOL]

example : compSyntaxOkHOL (width := 8) live8
    (.loop live8 .skip live9 : HolLoopProg 8) = false := by
  simp [compSyntaxOkHOL, live8_ne_live9]

example : compSyntaxOkHOL (width := 8) live8
    (.store (.const (0 : BitVec 8)) 4 : HolLoopProg 8) = false := rfl

example : compSyntaxOkHOL (width := 8) live8 (.raise 0 : HolLoopProg 8) = false :=
  rfl

example : compSyntaxOkHOL (width := 8) live8 (.tick : HolLoopProg 8) = false := rfl

private def ifLiveOut : NumSet :=
  [1, 2].foldl (fun sp n => sptInsert n () sp) live8

/-- Matching `If` row: the stored live set is the `FOLDL insert` image of the
    explicit witness list `[1, 2]`, so the classical existential holds and the
    clause returns `true` (HOL probe row `comp_if_witness_ok=T`). -/
theorem if_matching :
    compSyntaxOkHOL (width := 8) live8
      (.ite .equal 1 (.imm 0) .skip .skip ifLiveOut : HolLoopProg 8) = true := by
  simp only [compSyntaxOkHOL, ifLiveOut]
  exact @decide_eq_true _ (Classical.propDecidable _) ⟨[1, 2], rfl⟩

/-- Structurally non-matching `If` row: the stored live set is not syntactically
    a `FOLDL insert` image, so HOL `EVAL` leaves the set-extension existential
    unreduced (`comp_if_nonmatching` in the probe prints
    `∃ns. ⦕5⦖ = FOLDL (λsp n. insert n () sp) ⦕8⦖ ns`). The Lean clause is the
    same classical existential, and this theorem records that literal
    unfolding; the truth value is not computed on either side. Deciding it
    would need a separate `sptInsert`-preserves-`sptLookup` induction,
    unrelated to the definition's statement. -/
theorem if_nonmatching_unfolds :
    compSyntaxOkHOL (width := 8) live8
      (.ite .equal 1 (.imm 0) .skip .skip (sptInsert 5 () .ln) : HolLoopProg 8) =
      @decide
        (∃ ns : List Nat,
          sptInsert 5 () .ln = ns.foldl (fun sp n => sptInsert n () sp) live8)
        (Classical.propDecidable _) := rfl

def runChecks : IO Bool := do
  IO.println "PASS loopProps comp_syntax_ok_def exact HOL cases"
  pure true

end Flapjack.Test.LoopPropsCompSyntaxOkParity