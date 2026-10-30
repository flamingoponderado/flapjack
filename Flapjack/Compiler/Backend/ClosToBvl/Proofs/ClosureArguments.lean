import Flapjack.Compiler.Backend.Semantics.ClosSem
import Flapjack.Misc.ListEl

/-! Argument accumulation for the closure-to-BVL value relation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Add a prefix of arguments to a closure or recursive closure. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "add_args_def"]
def addArgs : ClosSem.Value → List ClosSem.Value → Option ClosSem.Value
  | .closure loc args env arity body, added => some (.closure loc (added ++ args) env arity body)
  | .recclosure loc args env funs index, added => some (.recclosure loc (added ++ args) env funs index)
  | _, _ => none

/-- Flapjack helper: successive argument prefixes associate. The source's
local theorem has not yet had its inferred HOL type captured. -/
theorem addArgs_append (cl : ClosSem.Value) (argEnv : List ClosSem.Value)
    (func : ClosSem.Value) (args : List ClosSem.Value)
    (h : addArgs cl argEnv = some func) : addArgs cl (args ++ argEnv) = addArgs func args := by
  cases cl <;> simp [addArgs] at h
  all_goals subst func
  all_goals simp [addArgs, List.append_assoc]

private instance : Nonempty (Nat × ClosLang.Exp) := ⟨(0, .var .none 0)⟩

/-- The arity of a closure, using HOL's total `EL` for recursive groups. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "get_num_args_def"]
noncomputable def getNumArgs : ClosSem.Value → Option Nat
  | .closure _ _ _ arity _ => some arity
  | .recclosure _ _ _ funs index => some (Flapjack.holEl index funs).1
  | _ => none

end Flapjack.Compiler.Backend.ClosToBvl
