module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.ValueRelation

@[expose] public section

/-! Constructor characterizations of the numbering value relation. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack.Compiler.Backend.ClosSem

/-- The complete constructor equations for the numbering value relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_numberProofScript.sml" "v_rel_simp"]
theorem valueRel_simp (maxApp : Nat) (number : Int) (y : Value) (word : BitVec 64)
    (tag : Nat) (env : List Value) (bytes : List (BitVec 8)) (flag : Bool) (ptr : Nat)
    (location : Option Nat) (args : List Value) (arity : Nat) (body : ClosLang.Exp)
    (recLocation : Option Nat) (recArgs recEnv : List Value)
    (functions : List (Nat × ClosLang.Exp)) (index : Nat) :
    (ValueRel maxApp (.number number) y ↔ y = .number number) ∧
    (ValueRel maxApp (.word64 word) y ↔ y = .word64 word) ∧
    (ValueRel maxApp (.block tag env) y ↔
      ∃ ys, y = .block tag ys ∧ List.Forall₂ (ValueRel maxApp) env ys) ∧
    (ValueRel maxApp (.byteVector bytes) y ↔ y = .byteVector bytes) ∧
    (ValueRel maxApp (.refPtr flag ptr) y ↔ y = .refPtr flag ptr) ∧
    (ValueRel maxApp (.closure location args env arity body) y ↔
      ∃ nextArgs nextEnv start nextLocation,
        y = .closure nextLocation nextArgs nextEnv arity (renumber start body).2 ∧
        List.Forall₂ (ValueRel maxApp) env nextEnv ∧
        List.Forall₂ (ValueRel maxApp) args nextArgs ∧ ¬ ClosProps.containsAppSome maxApp [body]) ∧
    (ValueRel maxApp (.recclosure recLocation recArgs recEnv functions index) y ↔
      ∃ nextArgs nextEnv start nextLocation,
        y = .recclosure nextLocation nextArgs nextEnv
          ((functions.map Prod.fst).zip (renumberList start (functions.map Prod.snd)).2) index ∧
        List.Forall₂ (ValueRel maxApp) recEnv nextEnv ∧
        List.Forall₂ (ValueRel maxApp) recArgs nextArgs ∧
        ¬ ClosProps.containsAppSome maxApp (functions.map Prod.snd)) ∧
    (ValueRel maxApp y (.number number) ↔ y = .number number) ∧
    (ValueRel maxApp y (.word64 word) ↔ y = .word64 word) ∧
    (ValueRel maxApp y (.block tag env) ↔
      ∃ xs, y = .block tag xs ∧ List.Forall₂ (ValueRel maxApp) xs env) ∧
    (ValueRel maxApp y (.byteVector bytes) ↔ y = .byteVector bytes) ∧
    (ValueRel maxApp y (.refPtr flag ptr) ↔ y = .refPtr flag ptr) ∧
    (ValueRel maxApp y (.closure location args env arity body) ↔
      ∃ oldArgs oldBody oldEnv start oldLocation,
        y = .closure oldLocation oldArgs oldEnv arity oldBody ∧ body = (renumber start oldBody).2 ∧
        List.Forall₂ (ValueRel maxApp) oldEnv env ∧
        List.Forall₂ (ValueRel maxApp) oldArgs args ∧ ¬ ClosProps.containsAppSome maxApp [oldBody]) ∧
    (ValueRel maxApp y (.recclosure recLocation recArgs recEnv functions index) ↔
      ∃ oldArgs oldEnv oldFunctions start oldLocation,
        y = .recclosure oldLocation oldArgs oldEnv oldFunctions index ∧
        functions = ((oldFunctions.map Prod.fst).zip (renumberList start (oldFunctions.map Prod.snd)).2) ∧
        List.Forall₂ (ValueRel maxApp) oldEnv recEnv ∧
        List.Forall₂ (ValueRel maxApp) oldArgs recArgs ∧
        ¬ ClosProps.containsAppSome maxApp (oldFunctions.map Prod.snd)) := by
  repeat' constructor
  all_goals first
    | (intro h; cases h; rfl)
    | (intro h; subst y; constructor)
    | (intro h; cases h; solve | aesop (add safe constructors ValueRel))

end Flapjack.Compiler.Backend.ClosNumber
