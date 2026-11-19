module

public import Flapjack.Pancake.WordConvs

@[expose] public section

namespace Flapjack.WordConvs
open Flapjack Flapjack.Compiler.Encoders.Asm

/-- Exact HOL `flat_exp_conventions_ShareInst`
(`wordConvsProofScript.sml:1390-1393`): a `ShareInst` keeps flat expressions
exactly when its expression is a variable or `Op Add [Var v; Const c]`. -/
@[hol "cakeml/compiler/backend/proofs/wordConvsProofScript.sml"
  "flat_exp_conventions_ShareInst" (words_as_type_indexed_bitvec)]
theorem flatExpConventions_shareInst {width : Nat} [NeZero width]
    (op : HolMemop) (v : Nat) (exp : WordLangExpHOL (BitVec width)) :
    flatExpConventions (.shareInst op v exp) = true ↔
      (∃ v c, exp = .op .add [.var v, .const c]) ∨ (∃ v, exp = .var v) := by
  cases exp
  all_goals simp [flatExpConventions]
  case op operator args =>
    cases operator
    all_goals
      cases args with
      | nil => simp [flatExpConventions]
      | cons a rest =>
        cases a
        all_goals
          cases rest with
          | nil => simp [flatExpConventions]
          | cons b rest' =>
            cases b
            all_goals
              cases rest' with
              | nil => simp [flatExpConventions]
              | cons c rest'' => simp [flatExpConventions]

end Flapjack.WordConvs
