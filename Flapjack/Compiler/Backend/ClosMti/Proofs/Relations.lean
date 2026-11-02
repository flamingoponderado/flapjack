import Flapjack.Compiler.Backend.ClosMti.Proofs.TotalView
import Flapjack.Compiler.Backend.ClosMti.Proofs.CollectArgs
import Flapjack.Compiler.Backend.Semantics.ClosSem
import Mathlib.Data.List.Forall2

/-! Proof-side relations for the multi-argument introduction simulation. -/
namespace Flapjack.Compiler.Backend.ClosMti
open ClosLang ClosSem

/-- Relate source code to the executed fuel-based pass. The source HOL relation
uses the total `intro_multi`; this is untagged until its correspondence with
`compileFuel` has been established. -/
def CodeRel (fuel maxApp : Nat) (source target : List ClosLang.Exp) : Prop :=
  (∀ e ∈ source, ClosProps.noMti e) ∧ compileFuel fuel true maxApp source = some target

/-- The relation to the executed pass can be expressed using its total
proof-side view. HOL correspondence for that view remains to be reviewed. -/
theorem codeRel_iff_introList (fuel maxApp : Nat) (source target : List ClosLang.Exp) :
    CodeRel fuel maxApp source target ↔
      (∀ e ∈ source, ClosProps.noMti e) ∧ target = introList maxApp source := by
  simp [CodeRel, compileFuel_introList, eq_comm]

/-- Relate a unary source function to a multi-argument target function. This
uses the Lean-specific `CodeRel`, so it is not yet the HOL relation. -/
def FunctionRel (fuel maxApp : Nat) (source target : Nat × ClosLang.Exp) : Prop :=
  ∃ body names,
    CodeRel fuel maxApp [body] [target.2] ∧ target.1 ≤ maxApp ∧ ClosProps.noMti body ∧
      source.1 = 1 ∧ source.2 = mkFns names body ∧ target.1 = names.length + 1

/-- Values corresponding across multi-argument introduction. The recursive
cases retain all of the source relation's closure and environment structure.
This is untagged because `CodeRel` still uses the fuel-based Lean pass. -/
inductive ValueRel (fuel maxApp : Nat) : Value → Value → Prop where
  | number (value : Int) : ValueRel fuel maxApp (.number value) (.number value)
  | word64 (value : BitVec 64) : ValueRel fuel maxApp (.word64 value) (.word64 value)
  | byteVector (bytes : List (BitVec 8)) :
      ValueRel fuel maxApp (.byteVector bytes) (.byteVector bytes)
  | refPtr (flag : Bool) (address : Nat) :
      ValueRel fuel maxApp (.refPtr flag address) (.refPtr flag address)
  | block (tag : Nat) (left right : List Value) :
      List.Forall₂ (ValueRel fuel maxApp) left right →
      ValueRel fuel maxApp (.block tag left) (.block tag right)
  | closure (args₁ args₂ env₁ env₂ : List Value) (arity : Nat)
      (body₁ body₂ : ClosLang.Exp) (names : List Flapjack.Basis.Pure.MlString.MlString) :
      1 + names.length + args₁.length = arity →
      CodeRel fuel maxApp [body₁] [body₂] →
      List.Forall₂ (ValueRel fuel maxApp) env₁ env₂ →
      List.Forall₂ (ValueRel fuel maxApp) args₁ args₂ →
      ValueRel fuel maxApp (.closure none [] (args₁ ++ env₁) 1 (mkFns names body₁))
        (.closure none args₂ env₂ arity body₂)
  | recclosure (env₁ env₂ : List Value) (funs₁ funs₂ : List (Nat × ClosLang.Exp)) (index : Nat) :
      List.Forall₂ (FunctionRel fuel maxApp) funs₁ funs₂ →
      List.Forall₂ (ValueRel fuel maxApp) env₁ env₂ →
      index < funs₂.length →
      ValueRel fuel maxApp (.recclosure none [] env₁ funs₁ index)
        (.recclosure none [] env₂ funs₂ index)
  | partialRecclosure (args₁ env₁ : List Value) (funs₁ : List (Nat × ClosLang.Exp))
      (args₂ env₂ : List Value) (funs₂ : List (Nat × ClosLang.Exp)) (index : Nat)
      (recursive : List Value) (names : List Flapjack.Basis.Pure.MlString.MlString)
      (body₁ body₂ : ClosLang.Exp) (arity : Nat) (bound : index < funs₂.length) :
      List.Forall₂ (FunctionRel fuel maxApp) funs₁ funs₂ →
      List.Forall₂ (ValueRel fuel maxApp) env₁ env₂ →
      List.Forall₂ (ValueRel fuel maxApp) args₁ args₂ → args₂ ≠ [] →
      funs₂[index] = (arity, body₂) →
      1 + names.length + args₁.length = arity → CodeRel fuel maxApp [body₁] [body₂] →
      List.Forall₂ (ValueRel fuel maxApp) recursive
        ((List.range funs₂.length).map (fun i => .recclosure none [] env₂ funs₂ i)) →
      ValueRel fuel maxApp (.closure none [] (args₁ ++ recursive ++ env₁) 1 (mkFns names body₁))
        (.recclosure none args₂ env₂ funs₂ index)

/-- Optional globals are related exactly when both are absent or their values
are related. This depends on the Lean-specific `ValueRel`. -/
def ValueRelOpt (fuel maxApp : Nat) : Option Value → Option Value → Prop
  | none, none => True
  | some left, some right => ValueRel fuel maxApp left right
  | _, _ => False

/-- References preserve byte arrays and thunk modes, while their stored values
follow `ValueRel`. The relation is untagged pending `ValueRel` correspondence. -/
inductive RefRel (fuel maxApp : Nat) : Ref Value → Ref Value → Prop where
  | byteArray (bytes : List (BitVec 8)) : RefRel fuel maxApp (.byteArray bytes) (.byteArray bytes)
  | valueArray (left right : List Value) :
      List.Forall₂ (ValueRel fuel maxApp) left right → RefRel fuel maxApp (.valueArray left) (.valueArray right)
  | thunk (mode : AstHOL.ThunkMode) (left right : Value) :
      ValueRel fuel maxApp left right → RefRel fuel maxApp (.thunk mode left) (.thunk mode right)

/-- The executed traversal preserves the number of related expressions. -/
theorem codeRel_length {fuel maxApp : Nat} {source target : List ClosLang.Exp}
    (related : CodeRel fuel maxApp source target) : target.length = source.length := by
  apply ClosLang.mapM_length source (introMultiBounded fuel maxApp) target
  simpa [CodeRel, compileFuel] using related.2

/-- The executed code relation is independent of the initial traversal fuel. -/
theorem codeRel_fuel_independent (fuel₁ fuel₂ maxApp : Nat) (source target : List ClosLang.Exp) :
    CodeRel fuel₁ maxApp source target ↔ CodeRel fuel₂ maxApp source target := by
  simp [CodeRel, compileFuel_fuel_independent fuel₁ fuel₂ true maxApp source]

/-- The executed code relation splits over matching list heads. -/
theorem codeRel_cons {fuel maxApp : Nat} (x y : ClosLang.Exp) (xs ys : List ClosLang.Exp) :
    CodeRel fuel maxApp (x :: xs) (y :: ys) ↔
      CodeRel fuel maxApp [x] [y] ∧ CodeRel fuel maxApp xs ys := by
  cases head : introMultiBounded fuel maxApp x <;>
    cases tail : xs.mapM (introMultiBounded fuel maxApp) <;>
    simp [CodeRel, compileFuel, List.mapM_cons, head, tail, and_assoc, and_left_comm, and_comm]

/-- Related scalar integers retain their payload exactly. -/
theorem valueRel_target_number {fuel maxApp : Nat} {source : Value} {number : Int}
    (related : ValueRel fuel maxApp source (.number number)) : source = .number number := by
  cases related
  rfl

/-- Related blocks retain the target's tag and relate each field. -/
theorem valueRel_target_block {fuel maxApp tag : Nat} {source : Value} {fields : List Value}
    (related : ValueRel fuel maxApp source (.block tag fields)) :
    ∃ left, source = .block tag left ∧ List.Forall₂ (ValueRel fuel maxApp) left fields := by
  cases related with
  | block _ left _ rel => exact ⟨left, rfl, rel⟩

/-- A target closure related by multi-argument introduction comes from a
chain of unary source closures with related captured values and code. -/
theorem valueRel_target_closure {fuel maxApp : Nat} {source : Value}
    {args₂ env₂ : List Value} {arity : Nat} {body₂ : ClosLang.Exp}
    (related : ValueRel fuel maxApp source (.closure none args₂ env₂ arity body₂)) :
    ∃ args₁ env₁ names body₁,
      source = .closure none [] (args₁ ++ env₁) 1 (mkFns names body₁) ∧
      1 + names.length + args₁.length = arity ∧
      CodeRel fuel maxApp [body₁] [body₂] ∧
      List.Forall₂ (ValueRel fuel maxApp) env₁ env₂ ∧
      List.Forall₂ (ValueRel fuel maxApp) args₁ args₂ := by
  cases related with
  | closure args₁ _ env₁ _ _ body₁ _ names arityRel code envRel argsRel =>
    exact ⟨args₁, env₁, names, body₁, rfl, arityRel, code, envRel, argsRel⟩

/-- A source-related target function has positive arity. -/
theorem functionRel_target_arity_pos {fuel maxApp : Nat} {source target : Nat × ClosLang.Exp}
    (related : FunctionRel fuel maxApp source target) : 0 < target.1 := by
  obtain ⟨_, names, _, _, _, _, _, eq⟩ := related
  omega

/-- A list of related target functions cannot contain a zero-arity entry. -/
theorem functionRel_list_target_arity_pos {fuel maxApp : Nat}
    {source target : List (Nat × ClosLang.Exp)} (related : List.Forall₂ (FunctionRel fuel maxApp) source target)
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
