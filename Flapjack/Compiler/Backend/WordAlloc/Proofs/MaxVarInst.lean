import Flapjack.Pancake.WordLang.MaxVarInst

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Every integer register in an instruction is bounded by its literal
maximum, including HOL's dimension-dependent floating-point transfers. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml"
  "max_var_inst_max" (words_as_type_indexed_bitvec)]
theorem maxVarInstMax {width : Nat} [NeZero width]
    (instruction : WordLangInst (BitVec width)) :
    everyVarInstHOL (fun x => decide (x ≤ maxVarInstHOL instruction)) instruction = true := by
  cases instruction with
  | skip => rfl
  | const r v => simp [everyVarInstHOL, maxVarInstHOL]
  | arith operation =>
      cases operation with
      | binop op a b right | shift op a b right =>
          cases right <;>
            simp [everyVarInstHOL, maxVarInstHOL, everyVarImmHOL, max3HOL]
          all_goals repeat' split
          all_goals simp_all [Nat.le_max_left, Nat.le_max_right]
          all_goals omega
      | div a b c =>
          simp [everyVarInstHOL, maxVarInstHOL, max3HOL]
          repeat' split
          all_goals omega
      | _ => simp [everyVarInstHOL, maxVarInstHOL] <;> omega
  | mem operator r address =>
      cases operator <;> cases address <;>
        simp [everyVarInstHOL, maxVarInstHOL, Nat.le_max_left, Nat.le_max_right]
  | fp operation =>
      cases operation <;> simp [everyVarInstHOL, maxVarInstHOL]
      all_goals split <;> simp_all <;> omega

end Flapjack.Compiler.Backend.WordAlloc
