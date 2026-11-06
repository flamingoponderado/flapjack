import Flapjack.AstHOL.Syntax

/-! Lift top-level source `Let` and `Letrec` expressions into declarations. -/
namespace Flapjack.Compiler.Backend.SourceLet
open Flapjack.Basis.Pure.MlString Flapjack.AstHOL

/-- Extract a source `Let` expression. -/
@[hol "cakeml/compiler/backend/source_letScript.sml" "dest_Let_def"]
def destLet : Exp → Option (Option VarN × Exp × Exp)
  | .let_ v x y => some (v, x, y)
  | _ => none

/-- Extract a source `Letrec` expression. -/
@[hol "cakeml/compiler/backend/source_letScript.sml" "dest_Letrec_def"]
def destLetrec : Exp → Option (List (VarN × VarN × Exp) × Exp)
  | .letrec fs x => some (fs, x)
  | _ => none

/-- Lift one top-level `Let` or `Letrec` out of a value declaration. -/
@[hol "cakeml/compiler/backend/source_letScript.sml" "lift_let_def"]
def liftLet : Dec → Option (Dec × Dec)
  | .dlet l p (.let_ none x y) => some (.dlet l .pany x, .dlet l p y)
  | .dlet l p (.let_ (some v) x y) => some (.dlet l (.pvar v) x, .dlet l p y)
  | .dlet l p (.letrec fs x) => some (.dletrec l fs, .dlet l p x)
  | _ => none

/-- Lift all successive outer `Let` and `Letrec` expressions in order. -/
@[hol "cakeml/compiler/backend/source_letScript.sml" "lift_lets_def"]
def liftLets (sofar : List Dec) (d : Dec) : Option (List Dec × Dec) :=
  match d with
  | .dlet l p (.let_ none x y) => liftLets (.dlet l .pany x :: sofar) (.dlet l p y)
  | .dlet l p (.let_ (some v) x y) => liftLets (.dlet l (.pvar v) x :: sofar) (.dlet l p y)
  | .dlet l p (.letrec fs x) => liftLets (.dletrec l fs :: sofar) (.dlet l p x)
  | _ => if sofar.isEmpty then none else some (sofar.reverse, d)
termination_by sizeOf d
decreasing_by all_goals simp_wf <;> omega

/-- Apply source let-lifting to declarations and recursively to modules and
local declarations when the declaration itself was not lifted. -/
@[hol "cakeml/compiler/backend/source_letScript.sml" "compile_decs_def"]
def compileDecs : List Dec → List Dec
  | [] => []
  | d :: ds =>
      match liftLets [] d with
      | some (pre, final) => .dlocal pre [final] :: compileDecs ds
      | none =>
          match d with
          | .dmod mn ds1 => .dmod mn (compileDecs ds1) :: compileDecs ds
          | .dlocal ds1 ds2 => .dlocal (compileDecs ds1) (compileDecs ds2) :: compileDecs ds
          | _ => d :: compileDecs ds
termination_by ds => sizeOf ds
decreasing_by all_goals simp_wf <;> omega

end Flapjack.Compiler.Backend.SourceLet
