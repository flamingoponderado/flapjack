module

public import Flapjack.TypeSoundInvariants
public import Flapjack.PrimTypesHOL.Types
public import Flapjack.Compiler.Inference.EnvRel

@[expose] public section

/-! Primitive type-environment facts used by the compiler and REPL proofs. -/
namespace Flapjack.Compiler.Repl.ReplTypes
open Flapjack.NamespaceHOL Flapjack.PrimTypesHOL Flapjack.TypeSystemHOL Flapjack.TypeSoundInvariants

/-- HOL's `simple_type`: the three reference types the REPL tracks. -/
@[hol "cakeml/compiler/repl/repl_typesScript.sml" "simple_type"]
inductive SimpleType where
  | bool | str | exn
  deriving DecidableEq, Repr

/-- Original `to_type_def`: the inference-type rendering of a reference type. -/
@[hol "cakeml/compiler/repl/repl_typesScript.sml" "to_type_def"]
def toType : SimpleType → Flapjack.Compiler.Inference.InferT
  | .bool => .app [] TboolNum
  | .str => .app [] TstringNum
  | .exn => .app [] TexnNum

/-- Original `to_type_TS_def`: the declarative-type rendering. -/
@[hol "cakeml/compiler/repl/repl_typesScript.sml" "to_type_TS_def"]
def toTypeTS : SimpleType → SemanticT
  | .bool => .app [] TboolNum
  | .str => .app [] TstringNum
  | .exn => .app [] TexnNum

/-- Original `roll_back_def`: keep the old environment and the new identifier. -/
@[hol "cakeml/compiler/repl/repl_typesScript.sml" "roll_back_def"]
def rollBack : Flapjack.Compiler.Inference.Infer.Env × Nat →
    Flapjack.Compiler.Inference.Infer.Env × Nat →
      Flapjack.Compiler.Inference.Infer.Env × Nat
  | (oldIenv, _), (_, newNextId) => (oldIenv, newNextId)

/-- Original `FST_roll_back`. -/
@[hol "cakeml/compiler/repl/repl_typesScript.sml" "FST_roll_back"]
theorem fst_rollBack (x y : Flapjack.Compiler.Inference.Infer.Env × Nat) :
    (rollBack x y).1 = x.1 := by
  obtain ⟨oldIenv, oldNextId⟩ := x
  obtain ⟨newIenv, newNextId⟩ := y
  rfl

/-- Original `SND_roll_back`. -/
@[hol "cakeml/compiler/repl/repl_typesScript.sml" "SND_roll_back"]
theorem snd_rollBack (x y : Flapjack.Compiler.Inference.Infer.Env × Nat) :
    (rollBack x y).2 = y.2 := by
  obtain ⟨oldIenv, oldNextId⟩ := x
  obtain ⟨newIenv, newNextId⟩ := y
  rfl

/-- Original `convert_t_to_type`: both renderings agree through `convert_t`. -/
@[hol "cakeml/compiler/repl/repl_typesScript.sml" "convert_t_to_type"]
theorem convertT_toType (t : SimpleType) :
    Flapjack.Compiler.Inference.EnvRel.convertT (toType t) = toTypeTS t := by
  cases t
  · simp [toType, toTypeTS, Flapjack.Compiler.Inference.EnvRel.convertTEqn]
  · simp [toType, toTypeTS, Flapjack.Compiler.Inference.EnvRel.convertTEqn]
  · simp [toType, toTypeTS, Flapjack.Compiler.Inference.EnvRel.convertTEqn]

@[hol "cakeml/compiler/repl/repl_typesScript.sml" "init_config_tenv_to_ienv"]
theorem initConfig_eq_tenvToIenv :
    Flapjack.Compiler.Inference.Infer.initConfig =
      Flapjack.Compiler.Inference.EnvRel.tenvToIenv primTenv := by
  simp [Flapjack.Compiler.Inference.Infer.initConfig,
    Flapjack.Compiler.Inference.EnvRel.tenvToIenv, primTenv, nsEmpty, nsMap]

@[hol "cakeml/compiler/repl/repl_typesScript.sml" "tenv_ok_prim_tenv"]
theorem tenvOkPrimTenv : tenvOk primTenv := by
  unfold tenvOk tenvValOk tenvCtorOk tenvAbbrevOk
  simp only [nsAll, primTenv, alistToNs, nsEmpty]
  constructor
  · intro id v h
    cases id <;> simp [nsLookup] at h
  · constructor
    · intro id v h
      cases id with
      | long m id => simp [nsLookup] at h
      | short name =>
        simp only [nsLookup, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h
        simp only [List.lookup] at h
        repeat' (split at h <;> simp_all)
        all_goals subst v
        all_goals simp_all [checkFreevars, checkFreevarsList]
    · intro id v h
      cases id with
      | long m id => simp [nsLookup] at h
      | short name =>
        simp only [nsLookup, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at h
        simp only [List.lookup] at h
        repeat' (split at h <;> simp_all)
        all_goals subst v
        all_goals simp_all [checkFreevars, checkFreevarsList]

/-- Original `check_ref_types_def`: the REPL accepts a reference type when the
    inference environment binds the name to `ref ty` and the value environment
    binds it to a location. -/
@[hol "cakeml/compiler/repl/repl_typesScript.sml" "check_ref_types_def"]
def checkRefTypes (types : Flapjack.Compiler.Inference.Infer.Env)
    (env : Flapjack.SemanticPrimitivesHOL.SemEnv Flapjack.SemanticPrimitivesHOL.Value)
    (entry : Ident Flapjack.Basis.Pure.MlString.MlString
        Flapjack.Basis.Pure.MlString.MlString × SimpleType × Nat) : Prop :=
  nsLookup types.infV entry.1 = some (0, .app [toType entry.2.1] TrefNum) ∧
    nsLookup env.v entry.1 = some (.loc true entry.2.2)

/-- Original `check_ref_types_TS_def`: the declarative-environment analogue. -/
@[hol "cakeml/compiler/repl/repl_typesScript.sml" "check_ref_types_TS_def"]
def checkRefTypesTS (types : TypeEnv)
    (env : Flapjack.SemanticPrimitivesHOL.SemEnv Flapjack.SemanticPrimitivesHOL.Value)
    (entry : Ident Flapjack.Basis.Pure.MlString.MlString
        Flapjack.Basis.Pure.MlString.MlString × SimpleType × Nat) : Prop :=
  nsLookup types.v entry.1 = some (0, .app [toTypeTS entry.2.1] TrefNum) ∧
    nsLookup env.v entry.1 = some (.loc true entry.2.2)

end Flapjack.Compiler.Repl.ReplTypes
