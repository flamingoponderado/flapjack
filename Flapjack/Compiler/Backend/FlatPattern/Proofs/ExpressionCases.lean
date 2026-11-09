import Flapjack.Compiler.Backend.FlatPattern.Proofs.MatchSimulation
import Flapjack.Compiler.Backend.FlatPattern.Proofs.RecursiveClosures

/-! Expression cases for the flat pattern compiler's forward simulation.
The evaluator and proof-side relations remain pending HOL review. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Raising a value returned by the operand raises that value. -/
theorem evaluate_raise_value {C F : Type} (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F) (value : FlatSem.Value)
    (run : FlatSem.evaluate env state [body] = (next, .val [value])) :
    FlatSem.evaluate env state [.raise trace body] = (next, .err (.raise value)) := by
  simp [FlatSem.evaluate, run]

/-- Errors while evaluating a raise operand propagate unchanged. -/
theorem evaluate_raise_error {C F : Type} (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (env : FlatSem.Environment FlatSem.Value) (state next : FlatSem.State C F)
    (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state [body] = (next, .err error)) :
    FlatSem.evaluate env state [.raise trace body] = (next, .err error) := by
  simp [FlatSem.evaluate, run]

/-- Related values select the same conditional branch whenever the source
value is a valid Boolean. -/
theorem doIf_related {α : Type} (value value' : FlatSem.Value) (yes no branch : α)
    (related : ValueRel value value') (selected : FlatSem.doIf value yes no = some branch) :
    FlatSem.doIf value' yes no = some branch := by
  cases value with
  | conv stamp fields =>
    cases stamp with
    | none => simp [FlatSem.doIf] at selected
    | some stamp =>
      obtain ⟨tag, typeId⟩ := stamp
      cases typeId with
      | none => simp [FlatSem.doIf] at selected
      | some typeId =>
        cases fields with
        | cons first rest => simp [FlatSem.doIf] at selected
        | nil =>
          obtain ⟨fields', rfl, relatedFields⟩ := (valueRel_conv (some (tag, some typeId)) [] value').1 related
          cases relatedFields
          exact selected
  | litv _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ => simp [FlatSem.doIf] at selected

/-- Mapping both branches maps the conditional's selected branch. -/
theorem doIf_map {α β : Type} (f : α → β) (value : FlatSem.Value) (yes no : α) :
    FlatSem.doIf value (f yes) (f no) = (FlatSem.doIf value yes no).map f := by
  cases value with
  | conv stamp fields =>
    cases stamp with
    | none => rfl
    | some stamp =>
      obtain ⟨tag, typeId⟩ := stamp
      cases typeId <;> cases fields <;> simp [FlatSem.doIf]
      all_goals split <;> simp_all
  | litv _ | closure _ _ _ | recclosure _ _ _ | loc _ _ | vectorv _ => rfl

/-- A successful Boolean condition evaluates its selected branch. -/
theorem evaluate_if_selected {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no branch : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (value : FlatSem.Value)
    (run : FlatSem.evaluate env state [condition] = (next, .val [value]))
    (selected : FlatSem.doIf value yes no = some branch) :
    FlatSem.evaluate env state [.if_ trace condition yes no] =
      FlatSem.evaluate env { next with clock := min state.clock next.clock } [branch] := by
  simp only [FlatSem.evaluate, run, FlatSem.fixClock]
  split <;> simp_all

/-- An invalid Boolean condition produces a type error. -/
theorem evaluate_if_bad {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (value : FlatSem.Value)
    (run : FlatSem.evaluate env state [condition] = (next, .val [value]))
    (selected : FlatSem.doIf value yes no = none) :
    FlatSem.evaluate env state [.if_ trace condition yes no] =
      ({ next with clock := min state.clock next.clock }, .err (.abort .typeError)) := by
  simp only [FlatSem.evaluate, run, FlatSem.fixClock]
  split <;> simp_all

/-- A condition error propagates through the conditional. -/
theorem evaluate_if_error {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state [condition] = (next, .err error)) :
    FlatSem.evaluate env state [.if_ trace condition yes no] =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, run, FlatSem.fixClock]

/-- A successful let initializer extends the environment when a name is present. -/
theorem evaluate_let_value {C F : Type} (trace : BackendCommon.Tra) (name : Option VarN)
    (first body : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (value : FlatSem.Value)
    (run : FlatSem.evaluate env state [first] = (next, .val [value])) :
    FlatSem.evaluate env state [.let_ trace name first body] =
      FlatSem.evaluate { env with v := match name with | none => env.v | some name => (name, value) :: env.v }
        { next with clock := min state.clock next.clock } [body] := by
  cases name <;> simp [FlatSem.evaluate, run, FlatSem.fixClock]

/-- An error in a let initializer is propagated regardless of its binder. -/
theorem evaluate_let_error_any {C F : Type} (trace : BackendCommon.Tra) (name : Option VarN)
    (first body : FlatLang.Exp) (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (error : SemanticPrimitivesHOL.ErrorResult FlatSem.Value)
    (run : FlatSem.evaluate env state [first] = (next, .err error)) :
    FlatSem.evaluate env state [.let_ trace name first body] =
      ({ next with clock := min state.clock next.clock }, .err error) := by
  simp [FlatSem.evaluate, run, FlatSem.fixClock]

/-- Recursive function compilation maps bodies in source order. -/
theorem compileFuns_rows (cfg : Config) (funs : List (VarN × VarN × FlatLang.Exp)) :
    (compileFuns cfg funs).2.2 = compiledRecFuns cfg funs := by
  induction funs with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name, arg, body⟩ := entry
    cases first : compileExp cfg body with
    | mk bound result =>
      cases result with
      | mk flag compiled =>
        cases tail : compileFuns cfg rest with
        | mk tailBound result =>
          cases result with
          | mk tailFlag compiledTail =>
            simpa [compileFuns, compiledRecFuns, compileDec, first, tail] using ih

/-- Every recursive function body is bounded by the bundle's maximum. -/
theorem compileFuns_member_bound (cfg : Config) (funs : List (VarN × VarN × FlatLang.Exp))
    (entry : VarN × VarN × FlatLang.Exp) (member : entry ∈ funs) :
    (compileExp cfg entry.2.2).1 ≤ (compileFuns cfg funs).1 := by
  induction funs with
  | nil => simp at member
  | cons first rest ih =>
    obtain ⟨name, arg, body⟩ := first
    cases head : compileExp cfg body with
    | mk headBound result =>
      cases result with
      | mk flag compiled =>
        cases tail : compileFuns cfg rest with
        | mk tailBound result =>
          cases result with
          | mk tailFlag compiledTail =>
            simp only [List.mem_cons] at member
            rcases member with equal | later
            · subst entry
              simp [compileFuns, head, tail]
            · have bound := ih later
              simp only [tail] at bound
              simp only [compileFuns, head, tail]
              omega

end Flapjack.Compiler.Backend.FlatPattern
