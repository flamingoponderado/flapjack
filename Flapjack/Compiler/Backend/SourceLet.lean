module

public import Flapjack.AstHOL.Syntax

@[expose] public section

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

/-- Original `dest_Let_SOME`: a successful extraction is exactly a source `Let`. -/
@[hol "cakeml/compiler/backend/source_letScript.sml" "dest_Let_SOME"]
theorem destLet_some (z : Exp) (opt : Option VarN) (x y : Exp) :
    destLet z = some (opt, x, y) ↔ z = .let_ opt x y := by
  cases z
  all_goals simp [destLet]

/-- Original `dest_Let_NONE`: a failed extraction means the expression is not a `Let`. -/
@[hol "cakeml/compiler/backend/source_letScript.sml" "dest_Let_NONE"]
theorem destLet_none (z : Exp) :
    destLet z = none ↔ ∀ opt x y, z ≠ .let_ opt x y := by
  cases z
  all_goals simp [destLet]

/-- Original `dest_Letrec_SOME`: a successful extraction is exactly a source `Letrec`. -/
@[hol "cakeml/compiler/backend/source_letScript.sml" "dest_Letrec_SOME"]
theorem destLetrec_some (z : Exp) (funs : List (VarN × VarN × Exp)) (x : Exp) :
    destLetrec z = some (funs, x) ↔ z = .letrec funs x := by
  cases z
  all_goals simp [destLetrec]

/-- Original `dest_Letrec_NONE`: a failed extraction means the expression is not a `Letrec`. -/
@[hol "cakeml/compiler/backend/source_letScript.sml" "dest_Letrec_NONE"]
theorem destLetrec_none (z : Exp) :
    destLetrec z = none ↔ ∀ funs x, z ≠ .letrec funs x := by
  cases z
  all_goals simp [destLetrec]

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
  match _h : liftLet d with
  | some (d1, d2) => liftLets (d1 :: sofar) d2
  | none => if sofar.isEmpty then none else some (sofar.reverse, d)
termination_by sizeOf d
decreasing_by
  cases d with
  | dlet loc pat expr =>
    cases expr with
    | let_ name first body =>
      cases name <;> simp only [liftLet, Option.some.injEq, Prod.mk.injEq] at _h <;>
        obtain ⟨_, rfl⟩ := _h <;> simp_wf <;> omega
    | letrec funs body =>
      simp only [liftLet, Option.some.injEq, Prod.mk.injEq] at _h
      obtain ⟨_, rfl⟩ := _h
      simp_wf
      omega
    | _ => simp [liftLet] at _h
  | _ => simp [liftLet] at _h

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
