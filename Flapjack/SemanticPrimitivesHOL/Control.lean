import Flapjack.SemanticPrimitivesHOL.Thunk

/-! Source control and declaration helpers. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString

private def valueAsBool : Value → Option Bool
  | .conv (some stamp) [] =>
    if stamp = .typeStamp (ofString "True") boolTypeNum then some true
    else if stamp = .typeStamp (ofString "False") boolTypeNum then some false else none
  | _ => none

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_log_def"]
def doLog (op : Lop) (value : Value) (expr : AstHOL.Exp) : Option ExpOrVal :=
  match op, valueAsBool value with
  | .andalso, some true | .orelse, some false => some (.exp expr)
  | .andalso, some false | .orelse, some true => some (.val value)
  | _, none => none

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "do_if_def"]
def doIf {α : Type} (value : Value) (yes no : α) : Option α :=
  match valueAsBool value with
  | some true => some yes
  | some false => some no
  | none => none

/-- A source Boolean chooses its corresponding branch. This is Flapjack
infrastructure for source-to-flat simulation. -/
theorem doIf_boolValue {α : Type} (b : Bool) (yes no : α) :
    doIf (boolValue b) yes no = some (if b then yes else no) := by
  cases b <;> rfl

/-- Flapjack infrastructure: successful source conditionals expose the Boolean
constructor and selected branch. -/
theorem doIf_success_boolean {α : Type} (value : Value) (yes no result : α)
    (evaluated : doIf value yes no = some result) :
    ∃ b, value = boolValue b ∧ result = if b then yes else no := by
  cases value <;> simp [doIf, valueAsBool] at evaluated
  case conv stamp values =>
    cases stamp with
    | none => simp at evaluated
    | some stamp =>
      cases values with
      | cons => simp at evaluated
      | nil =>
        by_cases htrue : stamp = .typeStamp (ofString "True") boolTypeNum
        · subst stamp
          simp at evaluated
          exact ⟨true, rfl, evaluated.symm⟩
        · by_cases hfalse : stamp = .typeStamp (ofString "False") boolTypeNum
          · subst stamp
            have different : ofString "False" ≠ ofString "True" := by decide
            simp [different] at evaluated
            exact ⟨false, rfl, evaluated.symm⟩
          · simp [htrue, hfalse] at evaluated

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "build_constrs_def"]
def buildConstrs (stamp : Nat) (constructors : List (ConN × List AstT)) : List (ConN × Nat × Stamp) :=
  constructors.map fun (name, args) => (name, args.length, .typeStamp name stamp)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "build_tdefs_def"]
def buildTdefs : Nat → TypeDef → Namespace ModN ConN (Nat × Stamp)
  | _, [] => nsEmpty
  | stamp, (_, _, constructors) :: rest =>
    nsAppend (buildTdefs (stamp + 1) rest) (alistToNs (buildConstrs stamp constructors).reverse)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "check_dup_ctors_def"]
def checkDupCtors (definition : List TvarN × TypeN × List (ConN × List AstT)) : Bool :=
  let (_, _, constructors) := definition
  decide (constructors.map Prod.fst).Nodup

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "combine_dec_result_def"]
def combineDecResult {α : Type} (env : SemEnv Value) : Result (SemEnv Value) α → Result (SemEnv Value) α
  | .val newEnv => .val { v := nsAppend newEnv.v env.v, c := nsAppend newEnv.c env.c }
  | .err error => .err error

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "extend_dec_env_def"]
def extendDecEnv (newEnv env : SemEnv Value) : SemEnv Value :=
  { v := nsAppend newEnv.v env.v, c := nsAppend newEnv.c env.c }

end Flapjack.SemanticPrimitivesHOL
