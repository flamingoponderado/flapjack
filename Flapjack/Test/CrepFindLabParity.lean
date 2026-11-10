module

public import Flapjack.Pancake.CrepToLoop
public import Flapjack.Pancake.CrepToLoop.ContextExact
public import Flapjack.Basis.Pure.MlString

-- Checks below run compiled code from these modules.
public meta import Flapjack.Basis.Pure.MlString
public meta import Flapjack.Pancake.CrepToLoop
public meta import Flapjack.Pancake.CrepToLoop.ContextExact
@[expose] public section

/-! Direct parity for `crep_to_loop$find_lab` (`find_lab_def`, line 27). -/
namespace Flapjack.Test.CrepFindLabParity

def context : LoopContext Nat :=
  { vars := [], functions := [("f", (64, 2))], maxVar := 0, target := .rv64i }

def parityGuard : Bool :=
  crepFindLab context "f" == 64 && crepFindLab context "missing" == 0

open Flapjack.Basis.Pure.MlString

def exactFunctionName : MlString := ofString "f"

def exactFunctions : HolFiniteMapExact MlString (Nat × Nat) where
  lookup name := if name = exactFunctionName then some (64, 2) else none
  finiteSupport := by
    refine ⟨[exactFunctionName], ?_⟩
    intro name hlookup
    by_cases hname : name = exactFunctionName
    · simp [hname]
    · simp [hname] at hlookup

def exactContext :=
  mkCtxtExact .riscv HolFiniteMapExact.empty exactFunctions 17

def exactParityGuard : Bool :=
  decide (findLabExact exactContext exactFunctionName = 64) &&
    decide (findLabExact exactContext (ofString "missing") = 0) &&
    decide (exactContext.vars.lookup 3 = none) &&
    decide (exactContext.funcs.lookup exactFunctionName = some (64, 2)) &&
    decide (exactContext.vmax = 17) &&
    decide (exactContext.target = .riscv)

#eval parityGuard
#guard parityGuard
#eval exactParityGuard
#guard exactParityGuard

end Flapjack.Test.CrepFindLabParity
