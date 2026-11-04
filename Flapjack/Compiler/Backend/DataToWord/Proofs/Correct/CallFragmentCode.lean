import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Code

/-! Code-table preservation for the data simulation fragment with calls. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack DataSem

/-- A successful direct or indirect lookup selects a body from the source code tree. -/
theorem findCode_body_lookup (dest : Option Nat) (values : List DataSem.Value)
    (code : Spt (Nat × DataLang.Prog)) (sizes : Spt Nat)
    (args : List DataSem.Value) (body : DataLang.Prog) (size : Option Nat)
    (found : findCode dest values code sizes = some (args, body, size)) :
    ∃ label arity, sptLookup label code = some (arity, body) := by
  cases dest with
  | some label =>
    cases entry : sptLookup label code with
    | none => simp [findCode, entry] at found
    | some pair =>
      obtain ⟨arity, prog⟩ := pair
      by_cases length : values.length = arity
      · simp [findCode, entry, length] at found
        obtain ⟨_, rfl, _⟩ := found
        exact ⟨label, arity, entry⟩
      · simp [findCode, entry, length] at found
  | none =>
    by_cases empty : values.isEmpty
    · simp [findCode, empty] at found
    · cases last : holLast values with
      | number n => simp [findCode, empty, last] at found
      | word64 w => simp [findCode, empty, last] at found
      | block ts tag fields => simp [findCode, empty, last] at found
      | refPtr bit ptr => simp [findCode, empty, last] at found
      | codePtr label =>
        cases entry : sptLookup label code with
        | none => simp [findCode, empty, last, entry] at found
        | some pair =>
          obtain ⟨arity, prog⟩ := pair
          by_cases length : values.length = arity + 1
          · simp [findCode, empty, last, entry, length] at found
            obtain ⟨_, rfl, _⟩ := found
            exact ⟨label, arity, entry⟩
          · simp [findCode, empty, last, entry, length] at found

/-- Programs formed from the established fragment and arbitrary call sites,
with handler bodies and sequential branches recursively in the fragment. -/
inductive CallFragment : DataLang.Prog → Prop where
  | base {program : DataLang.Prog} : VerifiedFragment program → CallFragment program
  | seq {first second : DataLang.Prog} : CallFragment first → CallFragment second →
      CallFragment (.seq first second)
  | ite (name : Nat) {yes no : DataLang.Prog} : CallFragment yes → CallFragment no →
      CallFragment (.ifThenElse name yes no)
  | call (ret : Option (List Nat × NumSet)) (dest : Option Nat) (names : List Nat)
      (handler : Option (Nat × DataLang.Prog)) :
      (∀ name body, handler = some (name, body) → CallFragment body) →
      CallFragment (.call ret dest names handler)

/-- Every callable body in a code table is covered by the extended fragment. -/
def CallFragmentCode (code : Spt (Nat × DataLang.Prog)) : Prop :=
  ∀ label arity body, sptLookup label code = some (arity, body) → CallFragment body

/-- Evaluating the call-extended fragment preserves a code table whose bodies
are in that fragment. The clock induction handles recursive and mutually
recursive calls; this is Lean-side infrastructure, not a HOL correctness port. -/
theorem callFragment_code {C F : Type} (program : DataLang.Prog) (fragment : CallFragment program)
    (state : State C F) (closed : CallFragmentCode state.code) :
    (evaluate program state).2.code = state.code := by
  have allClocks : ∀ clock : Nat, ∀ (program : DataLang.Prog), CallFragment program →
      ∀ state : State C F, state.clock = clock → CallFragmentCode state.code →
        (evaluate program state).2.code = state.code := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro program fragment
      induction fragment with
      | base frag => intro state _ _; exact verifiedFragment_code _ frag state
      | @seq first second firstFrag secondFrag firstIH secondIH =>
        intro state eq closed
        apply evaluate_seq_code_step first second state (firstIH state eq closed)
        intro mid codeEq clockBound
        have midClosed : CallFragmentCode mid.code := by simpa [codeEq] using closed
        rcases Nat.lt_or_eq_of_le clockBound with less | equal
        · exact clockIH mid.clock (by omega) second secondFrag mid rfl midClosed
        · exact secondIH mid (by omega) midClosed
      | @ite name yes no yesFrag noFrag yesIH noIH =>
        intro state eq closed
        exact evaluate_if_code_step name yes no state (yesIH state eq closed) (noIH state eq closed)
      | @call ret dest names handler handlerFrag handlerIH =>
        intro state eq closed
        apply evaluate_call_code_step ret dest names handler state
        · intro values args body size found next smaller codeEq
          obtain ⟨label, arity, lookup⟩ := findCode_body_lookup dest values state.code state.stackFrameSizes args body size found
          have member := closed label arity body lookup
          have nextClosed : CallFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
        · intro name body handlerEq next smaller codeEq
          have member := handlerFrag name body handlerEq
          have nextClosed : CallFragmentCode next.code := by simpa [codeEq] using closed
          exact (clockIH next.clock (by omega) body member next rfl nextClosed).trans codeEq
  exact allClocks state.clock program fragment state rfl closed

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
