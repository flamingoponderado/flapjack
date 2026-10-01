import Flapjack.Pancake.Proofs.PanToWord
import Flapjack.Pancake.Proofs.PanToTarget
import Flapjack.Basis.Pure.MlString

/-!
Kernel replay for the exact `pan_to_word` good-code predicates
`Flapjack.goodPanopsHOL` / `Flapjack.pancakeGoodCodeHOL` (HOL
`good_panops_def`, `pan_to_wordProofScript.sml:1108`; `pancake_good_code_def`,
`:21`).

The exact Lean definitions are computable `Bool` functions, so these concrete
inputs decide to `true`/`false` in the kernel (`decide +kernel`).  The matching
direct original-HOL observations live in
`scripts/hol-probes/pan_to_word_good_code_probe.out`: for declarations without
`Panop` HOL `EVAL` reduces to the same Bool literals `T`; for the `Panop`
arity cases HOL leaves the arity predicate as its universally quantified normal
form (`Mul = op ∧ [args] = es ⇒ LENGTH es = 2`), which is exactly the case the
Lean `panopArityTwoHOL` decides.  Bead flapjack-cnum. -/

namespace Flapjack.Test.PanToWordGoodCodeParity

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

private abbrev D := DeclHOL 8

private def exn : D := .exnDecl (ofString "e") .one

private def nm : D := .name (ofString "s") []

private def goodDecl : D :=
  .decl .one (ofString "v") (.panop .mul [.const (1 : BitVec 8), .const (2 : BitVec 8)])

private def badDecl : D :=
  .decl .one (ofString "v") (.panop .mul [.const (1 : BitVec 8)])

private def plainDecl : D := .decl .one (ofString "v") (.const (1 : BitVec 8))

private def goodFun : D :=
  .function
    { name := ofString "f", inline := true, exported := true, params := [],
      body := .return (.panop .mul [.const (1 : BitVec 8), .const (2 : BitVec 8)]),
      returnShape := .one }

private def badFun : D :=
  .function
    { name := ofString "f", inline := true, exported := true, params := [],
      body := .return (.panop .mul [.const (1 : BitVec 8)]),
      returnShape := .one }

theorem goodPanops_exn : goodPanopsHOL exn = true := by decide +kernel

theorem goodPanops_name : goodPanopsHOL nm = true := by decide +kernel

theorem goodPanops_decl_good : goodPanopsHOL goodDecl = true := by decide +kernel

theorem goodPanops_decl_bad : goodPanopsHOL badDecl = false := by decide +kernel

theorem goodPanops_decl_plain : goodPanopsHOL plainDecl = true := by decide +kernel

theorem goodPanops_fun_good : goodPanopsHOL goodFun = true := by decide +kernel

theorem goodPanops_fun_bad : goodPanopsHOL badFun = false := by decide +kernel

theorem pancakeGoodCode_nil : pancakeGoodCodeHOL ([] : List D) = true := by decide +kernel

theorem pancakeGoodCode_exn : pancakeGoodCodeHOL [exn] = true := by decide +kernel

theorem pancakeGoodCode_name : pancakeGoodCodeHOL [nm] = true := by decide +kernel

theorem pancakeGoodCode_bad : pancakeGoodCodeHOL [goodDecl, badDecl] = false := by
  decide +kernel

theorem pancakeGoodCode_fun_bad : pancakeGoodCodeHOL [goodFun, badFun] = false := by
  decide +kernel

def runChecks : IO Bool := do
  IO.println
    "PASS pan_to_word goodPanopsHOL/pancakeGoodCodeHOL kernel replay (T/F + structural HOL rows)"
  return true

end Flapjack.Test.PanToWordGoodCodeParity
