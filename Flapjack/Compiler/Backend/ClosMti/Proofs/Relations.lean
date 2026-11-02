import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView
import Flapjack.Compiler.Backend.ClosMti.Proofs.CollectArgs
import Flapjack.Compiler.Backend.Semantics.ClosSem
import Flapjack.Compiler.Backend.Semantics.ClosProps.SimpleRelations
import Mathlib.Data.List.Forall2

/-! Proof-side relations for the multi-argument introduction simulation. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang ClosSem

/-- Source expressions satisfy the unary invariant and transform to the
target expressions under multi-argument introduction. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "code_rel_def"]
def CodeRel (maxApp : Nat) (source target : List ClosLang.Exp) : Prop :=
  (∀ e ∈ source, ClosProps.noMti e) ∧ target = introList maxApp source

/-- The source relation is equivalent to successful execution of the pass at
any initial fuel. This execution connection has no separate HOL original. -/
theorem codeRel_iff_executed (fuel maxApp : Nat) (source target : List ClosLang.Exp) :
    CodeRel maxApp source target ↔
      (∀ e ∈ source, ClosProps.noMti e) ∧ compileFuel fuel true maxApp source = some target := by
  simp [CodeRel, compileFuel_introList, eq_comm]

/-- Relate a unary source function to a multi-argument target function. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "f_rel_def"]
def FunctionRel (maxApp : Nat) (source target : Nat × ClosLang.Exp) : Prop :=
  ∃ body names,
    CodeRel maxApp [body] [target.2] ∧ target.1 ≤ maxApp ∧ ClosProps.noMti body ∧
      source.1 = 1 ∧ source.2 = mkFns names body ∧ target.1 = names.length + 1

/-- Values corresponding across multi-argument introduction, including
recursive closures and partially applied recursive closures. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "v_rel"]
inductive ValueRel (maxApp : Nat) : Value → Value → Prop where
  | number (value : Int) : ValueRel maxApp (.number value) (.number value)
  | word64 (value : BitVec 64) : ValueRel maxApp (.word64 value) (.word64 value)
  | byteVector (bytes : List (BitVec 8)) :
      ValueRel maxApp (.byteVector bytes) (.byteVector bytes)
  | refPtr (flag : Bool) (address : Nat) :
      ValueRel maxApp (.refPtr flag address) (.refPtr flag address)
  | block (tag : Nat) (left right : List Value) :
      List.Forall₂ (ValueRel maxApp) left right →
      ValueRel maxApp (.block tag left) (.block tag right)
  | closure (args₁ args₂ env₁ env₂ : List Value) (arity : Nat)
      (body₁ body₂ : ClosLang.Exp) (names : List Flapjack.Basis.Pure.MlString.MlString) :
      1 + names.length + args₁.length = arity →
      CodeRel maxApp [body₁] [body₂] →
      List.Forall₂ (ValueRel maxApp) env₁ env₂ →
      List.Forall₂ (ValueRel maxApp) args₁ args₂ →
      ValueRel maxApp (.closure none [] (args₁ ++ env₁) 1 (mkFns names body₁))
        (.closure none args₂ env₂ arity body₂)
  | recclosure (env₁ env₂ : List Value) (funs₁ funs₂ : List (Nat × ClosLang.Exp)) (index : Nat) :
      List.Forall₂ (FunctionRel maxApp) funs₁ funs₂ →
      List.Forall₂ (ValueRel maxApp) env₁ env₂ →
      index < funs₂.length →
      ValueRel maxApp (.recclosure none [] env₁ funs₁ index)
        (.recclosure none [] env₂ funs₂ index)
  | partialRecclosure (args₁ env₁ : List Value) (funs₁ : List (Nat × ClosLang.Exp))
      (args₂ env₂ : List Value) (funs₂ : List (Nat × ClosLang.Exp)) (index : Nat)
      (recursive : List Value) (names : List Flapjack.Basis.Pure.MlString.MlString)
      (body₁ body₂ : ClosLang.Exp) (arity : Nat) (bound : index < funs₂.length) :
      List.Forall₂ (FunctionRel maxApp) funs₁ funs₂ →
      List.Forall₂ (ValueRel maxApp) env₁ env₂ →
      List.Forall₂ (ValueRel maxApp) args₁ args₂ → args₂ ≠ [] →
      funs₂[index] = (arity, body₂) →
      1 + names.length + args₁.length = arity → CodeRel maxApp [body₁] [body₂] →
      List.Forall₂ (ValueRel maxApp) recursive
        ((List.range funs₂.length).map (fun i => .recclosure none [] env₂ funs₂ i)) →
      ValueRel maxApp (.closure none [] (args₁ ++ recursive ++ env₁) 1 (mkFns names body₁))
        (.recclosure none args₂ env₂ funs₂ index)

/-- Optional globals are related exactly when both are absent or their values
are related. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "v_rel_opt_def"]
def ValueRelOpt (maxApp : Nat) : Option Value → Option Value → Prop
  | none, none => True
  | some left, some right => ValueRel maxApp left right
  | _, _ => False

/-- References preserve byte arrays and thunk modes, while their stored values
follow `ValueRel`. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "ref_rel"]
inductive RefRel (maxApp : Nat) : Ref Value → Ref Value → Prop where
  | byteArray (bytes : List (BitVec 8)) : RefRel maxApp (.byteArray bytes) (.byteArray bytes)
  | valueArray (left right : List Value) :
      List.Forall₂ (ValueRel maxApp) left right → RefRel maxApp (.valueArray left) (.valueArray right)
  | thunk (mode : AstHOL.ThunkMode) (left right : Value) :
      ValueRel maxApp left right → RefRel maxApp (.thunk mode left) (.thunk mode right)

/-- Related source and target code have the same number of expressions. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "code_rel_IMP_LENGTH"]
theorem codeRel_length {maxApp : Nat} {source target : List ClosLang.Exp}
    (related : CodeRel maxApp source target) : target.length = source.length := by
  rw [related.2]
  exact introList_length maxApp source

/-- The executed code relation splits over matching list heads. -/
theorem codeRel_cons {maxApp : Nat} (x y : ClosLang.Exp) (xs ys : List ClosLang.Exp) :
    CodeRel maxApp (x :: xs) (y :: ys) ↔
      CodeRel maxApp [x] [y] ∧ CodeRel maxApp xs ys := by
  simp [CodeRel, introList, and_assoc, and_left_comm, and_comm]

/-- Related scalar integers retain their payload exactly. -/
theorem valueRel_target_number {maxApp : Nat} {source : Value} {number : Int}
    (related : ValueRel maxApp source (.number number)) : source = .number number := by
  cases related
  rfl

/-- Related blocks retain the target's tag and relate each field. -/
theorem valueRel_target_block {maxApp tag : Nat} {source : Value} {fields : List Value}
    (related : ValueRel maxApp source (.block tag fields)) :
    ∃ left, source = .block tag left ∧ List.Forall₂ (ValueRel maxApp) left fields := by
  cases related with
  | block _ left _ rel => exact ⟨left, rfl, rel⟩

/-- A target closure related by multi-argument introduction comes from a
chain of unary source closures with related captured values and code. -/
theorem valueRel_target_closure {maxApp : Nat} {source : Value}
    {args₂ env₂ : List Value} {arity : Nat} {body₂ : ClosLang.Exp}
    (related : ValueRel maxApp source (.closure none args₂ env₂ arity body₂)) :
    ∃ args₁ env₁ names body₁,
      source = .closure none [] (args₁ ++ env₁) 1 (mkFns names body₁) ∧
      1 + names.length + args₁.length = arity ∧
      CodeRel maxApp [body₁] [body₂] ∧
      List.Forall₂ (ValueRel maxApp) env₁ env₂ ∧
      List.Forall₂ (ValueRel maxApp) args₁ args₂ := by
  cases related with
  | closure args₁ _ env₁ _ _ body₁ _ names arityRel code envRel argsRel =>
    exact ⟨args₁, env₁, names, body₁, rfl, arityRel, code, envRel, argsRel⟩

/-- The multi-argument value relation meets the generic simple-value
conditions used by primitive-operation simulations. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "simple_val_rel"]
theorem simpleValRel (maxApp : Nat) : ClosProps.simpleValRel (ValueRel maxApp) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n
    constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .number n
  · intro x fields tag
    constructor
    · intro h
      cases h with
      | block _ left _ rel => exact ⟨left, rfl, rel⟩
    · rintro ⟨left, rfl, rel⟩
      exact .block tag left fields rel
  · intro x word
    constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .word64 word
  · intro x bytes
    constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .byteVector bytes
  · intro x address flag
    constructor
    · intro h; cases h; rfl
    · intro h; subst x; exact .refPtr flag address
  · intro body arity env args loc x h
    cases h
    trivial
  · intro index funs env args loc x h
    cases h <;> trivial

/-- A source-related target function has positive arity. -/
theorem functionRel_target_arity_pos {maxApp : Nat} {source target : Nat × ClosLang.Exp}
    (related : FunctionRel maxApp source target) : 0 < target.1 := by
  obtain ⟨_, names, _, _, _, _, _, eq⟩ := related
  omega

/-- A list of related target functions cannot contain a zero-arity entry. -/
theorem functionRel_list_target_arity_pos {maxApp : Nat}
    {source target : List (Nat × ClosLang.Exp)} (related : List.Forall₂ (FunctionRel maxApp) source target)
    {arity : Nat} {body : ClosLang.Exp} (member : (arity, body) ∈ target) : 0 < arity := by
  induction related with
  | nil => simp at member
  | @cons a b left right rel tail ih =>
    simp only [List.mem_cons] at member
    rcases member with equal | member
    · subst b
      exact functionRel_target_arity_pos rel
    · exact ih member

end Flapjack.Compiler.Backend.ClosMti
