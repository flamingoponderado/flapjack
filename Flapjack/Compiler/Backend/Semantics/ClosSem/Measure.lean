import Flapjack.Compiler.Backend.Semantics.ClosSem.Apply
import Flapjack.Compiler.Backend.Semantics.ClosSem.Call
import Flapjack.Compiler.Backend.Semantics.ClosSem.Install
import Flapjack.Misc.ListEl
import Lean.Elab.Tactic.Omega

/-! Expression weights for well-founded closure evaluation. -/
namespace Flapjack.Compiler.Backend.ClosSem

mutual
/-- Expression weight, with extra room for the generated force-thunk call. -/
def expWeight : ClosLang.Exp → Nat
  | .var _ _ => 1
  | .ifThenElse _ a b c => 1 + expWeight a + expWeight b + expWeight c
  | .let _ xs body => 1 + expsWeight xs + expWeight body
  | .raise _ body | .tick _ body => 1 + expWeight body
  | .handle _ body handler => 1 + expWeight body + expWeight handler
  | .call _ _ _ xs => 1 + expsWeight xs
  | .app _ _ function xs => 1 + expWeight function + expsWeight xs
  | .fn _ _ _ _ body => 1 + expWeight body
  | .letrec _ _ _ functions body => 1 + funsWeight functions + expWeight body
  | .op _ (.thunkOp .forceThunk) xs => 101 + expsWeight xs
  | .op _ _ xs => 1 + expsWeight xs
termination_by exp => sizeOf exp

/-- Expression-list weight. -/
def expsWeight : List ClosLang.Exp → Nat
  | [] => 0
  | e :: rest => 1 + expWeight e + expsWeight rest
termination_by exps => sizeOf exps

/-- Recursive function bundle weight. -/
def funsWeight : List (Nat × ClosLang.Exp) → Nat
  | [] => 0
  | (_, body) :: rest => 1 + expWeight body + funsWeight rest
termination_by funs => sizeOf funs
end

/-- Every expression has positive weight. -/
theorem expWeight_pos (exp : ClosLang.Exp) : 0 < expWeight exp := by
  cases exp <;> try (simp [expWeight] <;> omega)
  case op trace op args =>
    cases op <;> try (simp [expWeight] <;> omega)
    case thunkOp operation => cases operation <;> simp [expWeight] <;> omega

/-- Apply an expression to unit when forcing a thunk. -/
def appUnit (expression : ClosLang.Exp) : ClosLang.Exp :=
  .app .none none expression [.op .none (.blockOp (.cons 0)) []]

/-- The force-thunk generated call has bounded weight. -/
theorem appUnit_var_weight : expsWeight [appUnit (.var .none 0)] <
    expsWeight [.op .none (.thunkOp .forceThunk) []] := by
  simp [appUnit, expsWeight, expWeight]

end Flapjack.Compiler.Backend.ClosSem
