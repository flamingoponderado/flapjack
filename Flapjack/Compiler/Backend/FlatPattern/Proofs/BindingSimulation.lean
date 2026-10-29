import Flapjack.Compiler.Backend.FlatPattern.Proofs.BindingFold
import Flapjack.Compiler.Backend.FlatPattern.Proofs.PatternList
import Flapjack.Compiler.Backend.FlatPattern.BindingsTotal

/-! Evaluation steps for compiled pattern bindings. These proofs use the
unreviewed clocked evaluator and are not tagged as HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack.AstHOL Flapjack.Compiler.Backend

/-- The generated binding for a variable evaluates its source expression
and then continues with that value at the head of the environment. -/
theorem compilePatBindings_var_evaluate {C F : Type} (trace : BackendCommon.Tra) (i key : Nat)
    (name : VarN) (expression body : FlatLang.Exp)
    (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pvar name, key, expression) :: rest) body).2] =
      FlatSem.evaluate { env with v := (name, value) :: env.v } state
        [(compilePatBindings trace i rest body).2] := by
  cases compiled : compilePatBindings trace i rest body with
  | mk used result =>
    simp [compilePatBindings, compiled, FlatSem.evaluate, pure, FlatSem.fixClock]

/-- The variable step also preserves the observed lookup relation with the
matcher bindings extended by the same value. -/
theorem compilePatBindings_var_step {C F : Type} (trace : BackendCommon.Tra) (i key bound : Nat)
    (name : VarN) (expression body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pre base : List (VarN × FlatSem.Value))
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value]))
    (related : aLookupRel (fun n => decNameToNum n < bound) Eq env.v (pre ++ base)) :
    let next := { env with v := (name, value) :: env.v }
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pvar name, key, expression) :: rest) body).2] =
      FlatSem.evaluate next state [(compilePatBindings trace i rest body).2] ∧
    aLookupRel (fun n => decNameToNum n < bound) Eq next.v (((name, value) :: pre) ++ base) := by
  constructor
  · exact compilePatBindings_var_evaluate trace i key name expression body rest env state value pure
  · exact aLookupRel_cons _ _ name value value env.v (pre ++ base) (fun _ => rfl) related

/-- Wildcard bindings introduce no code and leave the continuation untouched. -/
theorem compilePatBindings_any_evaluate {C F : Type} (trace : BackendCommon.Tra) (i key : Nat)
    (expression body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) :
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pany, key, expression) :: rest) body).2] =
      FlatSem.evaluate env state [(compilePatBindings trace i rest body).2] := by
  simp [compilePatBindings]

/-- Literal bindings introduce no code and leave the continuation untouched. -/
theorem compilePatBindings_lit_evaluate {C F : Type} (trace : BackendCommon.Tra) (i key : Nat)
    (lit : Lit) (expression body : FlatLang.Exp) (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) :
    FlatSem.evaluate env state [(compilePatBindings trace i ((.plit lit, key, expression) :: rest) body).2] =
      FlatSem.evaluate env state [(compilePatBindings trace i rest body).2] := by
  simp [compilePatBindings]

/-- An as-pattern binds the original value and copies it into the generated
name used by the nested pattern's continuation. -/
theorem compilePatBindings_as_evaluate {C F : Type} (trace : BackendCommon.Tra) (i key : Nat)
    (pattern : FlatLang.Pat) (name : VarN) (expression body : FlatLang.Exp)
    (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value])) :
    let generated := encNumToName (i + 1)
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pas pattern name, key, expression) :: rest) body).2] =
      FlatSem.evaluate { env with v := (generated, value) :: (name, value) :: env.v } state
        [(compilePatBindings trace (i + 2) ((pattern, i + 1, .varLocal trace generated) :: rest) body).2] := by
  cases compiled : compilePatBindings trace (i + 2)
      ((pattern, i + 1, .varLocal trace (encNumToName (i + 1))) :: rest) body with
  | mk used result =>
    simp [compilePatBindings, compiled, FlatSem.evaluate, pure, FlatSem.fixClock]

/-- The generated as-pattern name is invisible below the original-name bound,
while the user binding is visible just as it is in the matcher environment. -/
theorem compilePatBindings_as_step {C F : Type} (trace : BackendCommon.Tra) (i key bound : Nat)
    (pattern : FlatLang.Pat) (name : VarN) (expression body : FlatLang.Exp)
    (rest : List (FlatLang.Pat × Nat × FlatLang.Exp))
    (env : FlatSem.Environment FlatSem.Value) (state : FlatSem.State C F) (value : FlatSem.Value)
    (pre base : List (VarN × FlatSem.Value))
    (pure : FlatSem.evaluate env state [expression] = (state, .val [value]))
    (related : aLookupRel (fun n => decNameToNum n < bound) Eq env.v (pre ++ base))
    (fresh : bound ≤ i + 1) :
    let generated := encNumToName (i + 1)
    let next := { env with v := (generated, value) :: (name, value) :: env.v }
    FlatSem.evaluate env state [(compilePatBindings trace i ((.pas pattern name, key, expression) :: rest) body).2] =
      FlatSem.evaluate next state
        [(compilePatBindings trace (i + 2) ((pattern, i + 1, .varLocal trace generated) :: rest) body).2] ∧
    aLookupRel (fun n => decNameToNum n < bound) Eq next.v (((name, value) :: pre) ++ base) := by
  constructor
  · exact compilePatBindings_as_evaluate trace i key pattern name expression body rest env state value pure
  · have old := aLookupRel_cons (fun n => decNameToNum n < bound) Eq name value value env.v (pre ++ base)
      (fun _ => rfl) related
    apply ((aLookupRel_cons_false (fun n => decNameToNum n < bound) Eq (encNumToName (i + 1)) value
      ((name, value) :: env.v) (((name, value) :: pre) ++ base)).1 ?_).2 old
    simp only [decEnc]
    omega

end Flapjack.Compiler.Backend.FlatPattern
