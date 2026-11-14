module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.Relations
public import Flapjack.Misc.ListEl

@[expose] public section

/-! Constructor characterization of the multi-argument value relation. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosLang ClosSem

/-- The complete constructor-by-constructor characterization of `ValueRel`. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "v_rel_simps"]
theorem valueRel_simps :
    (∀ (x : Value) (n : Int) (m : Nat), ValueRel m x (.number n) ↔ x = .number n) ∧
    (∀ (x : Value) (p : List Value) (n m : Nat), ValueRel m x (.block n p) ↔
      ∃ xs, x = .block n xs ∧ List.Forall₂ (ValueRel m) xs p) ∧
    (∀ (x : Value) (p : BitVec 64) (m : Nat), ValueRel m x (.word64 p) ↔ x = .word64 p) ∧
    (∀ (x : Value) (p : List (BitVec 8)) (m : Nat), ValueRel m x (.byteVector p) ↔ x = .byteVector p) ∧
    (∀ (x : Value) (p m : Nat) (b : Bool), ValueRel m x (.refPtr b p) ↔ x = .refPtr b p) ∧
    (∀ (body : ClosLang.Exp) (arity : Nat) (env args : List Value) (loc : Option Nat) (x : Value) (m : Nat),
      ValueRel m x (.closure loc args env arity body) ↔
        ∃ args1 env1 e1 names, x = .closure none [] (args1 ++ env1) 1 (mkFns names e1) ∧
          loc = none ∧ arity = 1 + names.length + args1.length ∧ CodeRel m [e1] [body] ∧
          List.Forall₂ (ValueRel m) env1 env ∧ List.Forall₂ (ValueRel m) args1 args) ∧
    (∀ (index : Nat) (funs : List (Nat × ClosLang.Exp)) (env args : List Value) (loc : Option Nat)
      (x : Value) (m : Nat), ValueRel m x (.recclosure loc args env funs index) ↔
        (∃ env1 funs1, x = .recclosure none [] env1 funs1 index ∧ loc = none ∧ args = [] ∧
          List.Forall₂ (FunctionRel m) funs1 funs ∧ List.Forall₂ (ValueRel m) env1 env ∧ index < funs.length) ∨
        (∃ args1 env1 funs1 recursive names e1 e2,
          x = .closure none [] (args1 ++ recursive ++ env1) 1 (mkFns names e1) ∧ loc = none ∧
          List.Forall₂ (FunctionRel m) funs1 funs ∧ List.Forall₂ (ValueRel m) env1 env ∧
          List.Forall₂ (ValueRel m) args1 args ∧ args ≠ [] ∧ index < funs.length ∧
          holEl index funs = (1 + names.length + args1.length, e2) ∧ CodeRel m [e1] [e2] ∧
          List.Forall₂ (ValueRel m) recursive
            ((List.range funs.length).map (fun i => .recclosure none [] env funs i)))) ∧
    (∀ (x : Value) (m : Nat) (b : Bool), ValueRel m x (boolValue b) ↔ x = boolValue b) ∧
    (∀ (x : Value) (m : Nat), ValueRel m x unitValue ↔ x = unitValue) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n m
    constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .number n
  · intro x p n m
    constructor
    · intro h; cases h with | block _ left _ rel => exact ⟨left, rfl, rel⟩
    · rintro ⟨xs, rfl, rel⟩; exact .block n xs p rel
  · intro x p m
    constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .word64 p
  · intro x p m
    constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .byteVector p
  · intro x p m b
    constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .refPtr b p
  · intro body arity env args loc x m
    constructor
    · intro h
      cases h with
      | closure args1 args2 env1 env2 n e1 e2 names arityEq code envRel argsRel =>
        exact ⟨args1, env1, e1, names, rfl, rfl, arityEq.symm, code, envRel, argsRel⟩
    · rintro ⟨args1, env1, e1, names, rfl, rfl, arityEq, code, envRel, argsRel⟩
      exact .closure args1 args env1 env arity e1 body names arityEq.symm code envRel argsRel
  · intro index funs env args loc x m
    constructor
    · intro h
      cases h with
      | recclosure env1 env2 funs1 funs2 index fnRel envRel bound =>
        exact Or.inl ⟨env1, funs1, rfl, rfl, rfl, fnRel, envRel, bound⟩
      | partialRecclosure args1 env1 funs1 args2 env2 funs2 index recursive names e1 e2 arity bound fnRel envRel argsRel nonempty lookup arityEq code recursiveRel =>
        refine Or.inr ⟨args1, env1, funs1, recursive, names, e1, e2, rfl, rfl, fnRel, envRel, argsRel, nonempty, bound, ?_, code, recursiveRel⟩
        rw [holEl_eq_getElem index funs bound, lookup, ← arityEq]
    · rintro (⟨env1, funs1, rfl, rfl, rfl, fnRel, envRel, bound⟩ |
        ⟨args1, env1, funs1, recursive, names, e1, e2, rfl, rfl, fnRel, envRel, argsRel, nonempty, bound, lookup, code, recursiveRel⟩)
      · exact .recclosure env1 env funs1 funs index fnRel envRel bound
      · apply ValueRel.partialRecclosure args1 env1 funs1 args env funs index recursive names e1 e2
          (1 + names.length + args1.length) bound fnRel envRel argsRel nonempty
        · simpa [holEl_eq_getElem index funs bound] using lookup
        · rfl
        · exact code
        · exact recursiveRel
  · intro x m b
    cases b <;> simp only [boolValue, Bool.false_eq_true, ↓reduceIte]
    all_goals
      constructor
      · intro h; cases h with | block _ left _ rel => cases rel; rfl
      · intro h; subst x; exact .block _ [] [] .nil
  · intro x m
    simp only [unitValue]
    constructor
    · intro h; cases h with | block _ left _ rel => cases rel; rfl
    · intro h; subst x; exact .block _ [] [] .nil

end Flapjack.Compiler.Backend.ClosMti
