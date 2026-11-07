import Flapjack.Compiler.Backend.FlatLang
import Flapjack.SemanticPrimitivesHOL

/-! Value and state carriers for the original flat-language semantics.
The evaluator and source-to-flat simulation are not yet ported here. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendCommon

/-- Flat closures retain an ordered local value environment. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "environment"]
structure Environment (α : Type) where
  v : List (VarN × α)

/-- Values of the flat-language semantics, including local closures. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "v"]
inductive Value where
  | litv : Lit → Value
  | conv : Option (FlatLang.CtorId × FlatLang.TypeId) → List Value → Value
  | closure : Environment Value → VarN → FlatLang.Exp → Value
  | recclosure : Environment Value → List (VarN × VarN × FlatLang.Exp) → VarN → Value
  | loc : Bool → Nat → Value
  | vectorv : List Value → Value

/-- Compiler callbacks used by the original flat-language Eval operation. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "install_config"]
structure InstallConfig (C : Type) where
  compile : C → List FlatLang.Exp → Option (List (BitVec 8) × List (BitVec 64) × C)
  compileOracle : Nat → C × List FlatLang.Exp

/-- Full flat-language evaluator state with independent compiler and FFI types. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "state"]
structure State (C F : Type) where
  clock : Nat
  refs : Store Value
  ffi : HolFfiState F
  globals : List (Option Value)
  evalConfig : InstallConfig C

/-- Original flat-language type identifier for lists. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "list_id_def"]
def listId : Nat := 1

/-- A flat-language Boolean constructor value. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "Boolv_def"]
def boolValue (b : Bool) : Value :=
  .conv (some (boolToTag b, some FlatLang.boolId)) []

/-- A flat-language unit constructor value. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "Unitv_def"]
def unitValue : Value := .conv none []

/-- Install recursive closures into an ordered local association list. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "build_rec_env_def"]
def buildRecEnv (funs : List (VarN × VarN × FlatLang.Exp)) (closureEnv : Environment Value)
    (initial : List (VarN × Value)) : List (VarN × Value) :=
  funs.foldr (fun (f, _, _) env => (f, .recclosure closureEnv funs f) :: env) initial

/-- Constructor types agree when their optional type identifiers agree; the
two constructor identifiers may have independent types. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "ctor_same_type_def"]
def ctorSameType {α β γ : Type} (left : Option (α × β)) (right : Option (γ × β)) : Prop :=
  match left, right with
  | some (_, t), some (_, t') => t = t'
  | none, none => True
  | _, _ => False

/-- Decidable comparison when the shared type identifier has decidable equality. -/
instance {α β γ : Type} [DecidableEq β] (left : Option (α × β)) (right : Option (γ × β)) :
    Decidable (ctorSameType left right) := by
  cases left <;> cases right <;> simp only [ctorSameType] <;> infer_instance

end Flapjack.Compiler.Backend.FlatSem
