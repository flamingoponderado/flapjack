import Flapjack.Compiler.Backend.ClosNumber
import Flapjack.Compiler.Backend.Semantics.ClosSem
import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic
import Mathlib.Data.List.Forall2

/-! Proof-side value relation for closure location numbering. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack.Compiler.Backend.ClosSem

/-- Values corresponding across closure numbering. Closure locations may
change, while bodies are numbered and captured environments remain related.
This is source-shaped infrastructure for the numbering simulation; its
carrier and HOL correspondence have not yet been reviewed. -/
inductive ValueRel (maxApp : Nat) : Value → Value → Prop where
  | number (value : Int) : ValueRel maxApp (.number value) (.number value)
  | word64 (value : BitVec 64) : ValueRel maxApp (.word64 value) (.word64 value)
  | block (tag : Nat) (left right : List Value) :
      List.Forall₂ (ValueRel maxApp) left right → ValueRel maxApp (.block tag left) (.block tag right)
  | byteVector (bytes : List (BitVec 8)) : ValueRel maxApp (.byteVector bytes) (.byteVector bytes)
  | refPtr (flag : Bool) (address : Nat) : ValueRel maxApp (.refPtr flag address) (.refPtr flag address)
  | closure (location nextLocation : Option Nat) (args nextArgs env nextEnv : List Value)
      (arity start : Nat) (body nextBody : ClosLang.Exp) :
      List.Forall₂ (ValueRel maxApp) env nextEnv →
      List.Forall₂ (ValueRel maxApp) args nextArgs →
      ¬ ClosProps.containsAppSome maxApp [body] →
      nextBody = (renumber start body).2 →
      ValueRel maxApp (.closure location args env arity body) (.closure nextLocation nextArgs nextEnv arity nextBody)
  | recclosure (location nextLocation : Option Nat) (args nextArgs env nextEnv : List Value)
      (functions nextFunctions : List (Nat × ClosLang.Exp)) (index start : Nat) :
      List.Forall₂ (ValueRel maxApp) env nextEnv →
      List.Forall₂ (ValueRel maxApp) args nextArgs →
      ¬ ClosProps.containsAppSome maxApp (functions.map Prod.snd) →
      nextFunctions = (functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2 →
      ValueRel maxApp (.recclosure location args env functions index)
        (.recclosure nextLocation nextArgs nextEnv nextFunctions index)

/-- Numbered values preserve scalar constructors and their payloads. -/
theorem valueRel_number_iff (maxApp : Nat) (number : Int) (target : Value) :
    ValueRel maxApp (.number number) target ↔ target = .number number := by
  constructor
  · intro related
    cases related
    rfl
  · intro equal
    subst target
    exact .number number

/-- Related blocks retain their tag and relate all component values. -/
theorem valueRel_block_iff (maxApp tag : Nat) (values : List Value) (target : Value) :
    ValueRel maxApp (.block tag values) target ↔
      ∃ targetValues, target = .block tag targetValues ∧ List.Forall₂ (ValueRel maxApp) values targetValues := by
  constructor
  · intro related
    cases related with
    | block _ _ targetValues entries => exact ⟨targetValues, rfl, entries⟩
  · rintro ⟨targetValues, rfl, entries⟩
    exact .block tag values targetValues entries

/-- List values preserve the relation when encoded as closure blocks. -/
theorem listToValue_related (maxApp : Nat) {left right : List Value}
    (related : List.Forall₂ (ValueRel maxApp) left right) :
    ValueRel maxApp (listToValue left) (listToValue right) := by
  induction related with
  | nil => exact .block _ [] [] .nil
  | cons head tail ih =>
    exact .block _ _ _ (.cons head (.cons ih .nil))

/-- Invert the closure case without requiring the two location annotations to
coincide. -/
theorem valueRel_closure_iff (maxApp : Nat) (location : Option Nat) (args env : List Value)
    (arity : Nat) (body : ClosLang.Exp) (target : Value) :
    ValueRel maxApp (.closure location args env arity body) target ↔
      ∃ nextLocation nextArgs nextEnv start,
        target = .closure nextLocation nextArgs nextEnv arity (renumber start body).2 ∧
        List.Forall₂ (ValueRel maxApp) env nextEnv ∧
        List.Forall₂ (ValueRel maxApp) args nextArgs ∧
        ¬ ClosProps.containsAppSome maxApp [body] := by
  constructor
  · intro related
    cases related with
    | closure _ nextLocation _ nextArgs _ nextEnv _ start _ nextBody envRel argsRel safe bodyEq =>
      subst nextBody
      exact ⟨nextLocation, nextArgs, nextEnv, start, rfl, envRel, argsRel, safe⟩
  · rintro ⟨nextLocation, nextArgs, nextEnv, start, rfl, envRel, argsRel, safe⟩
    exact .closure location nextLocation args nextArgs env nextEnv arity start body _ envRel argsRel safe rfl

/-- Invert recursive closures, retaining the source ordering and arities of
the numbered function bundle. -/
theorem valueRel_recclosure_iff (maxApp : Nat) (location : Option Nat) (args env : List Value)
    (functions : List (Nat × ClosLang.Exp)) (index : Nat) (target : Value) :
    ValueRel maxApp (.recclosure location args env functions index) target ↔
      ∃ nextLocation nextArgs nextEnv start,
        target = .recclosure nextLocation nextArgs nextEnv
          ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2) index ∧
        List.Forall₂ (ValueRel maxApp) env nextEnv ∧
        List.Forall₂ (ValueRel maxApp) args nextArgs ∧
        ¬ ClosProps.containsAppSome maxApp (functions.map Prod.snd) := by
  constructor
  · intro related
    cases related with
    | recclosure _ nextLocation _ nextArgs _ nextEnv _ nextFunctions _ start envRel argsRel safe functionsEq =>
      subst nextFunctions
      exact ⟨nextLocation, nextArgs, nextEnv, start, rfl, envRel, argsRel, safe⟩
  · rintro ⟨nextLocation, nextArgs, nextEnv, start, rfl, envRel, argsRel, safe⟩
    exact .recclosure location nextLocation args nextArgs env nextEnv functions _ index start envRel argsRel safe rfl

end Flapjack.Compiler.Backend.ClosNumber
