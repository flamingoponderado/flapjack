import Flapjack.Compiler.Backend.ClosLang.Syntax

/-! Structural bounds for the smart-operation equality traversal. -/
namespace Flapjack.Compiler.Backend.ClosOp
open ClosLang

mutual
def eqNodeWeight : Exp → Nat
  | .op _ (.blockOp (.cons _)) xs => 1 + eqNodesWeight xs
  | _ => 0
termination_by e => sizeOf e
decreasing_by all_goals simp_wf <;> omega

def eqNodesWeight : List Exp → Nat
  | [] => 0
  | x :: xs => 1 + eqNodeWeight x + eqNodesWeight xs
termination_by xs => sizeOf xs
decreasing_by all_goals simp_wf <;> omega
end

def eqPairWeight (p : Exp × Exp) : Nat :=
  2 + 2 * (eqNodeWeight p.1 + eqNodeWeight p.2) +
    if eqNodeWeight p.1 < eqNodeWeight p.2 then 1 else 0

def eqPairsWeight : List (Exp × Exp) → Nat
  | [] => 0
  | p :: ps => eqPairWeight p + eqPairsWeight ps

end Flapjack.Compiler.Backend.ClosOp
