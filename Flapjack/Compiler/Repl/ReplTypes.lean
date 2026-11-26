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

end Flapjack.Compiler.Repl.ReplTypes
