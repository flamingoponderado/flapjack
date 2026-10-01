import Flapjack.Compiler.Backend.WordToStack.ProductionProgramMaximum
import Flapjack.Compiler.Backend.WordAlloc.LimitVar

namespace Flapjack

/-- Actual production SSA counter agrees with native limit_var through the
partial program codec, for arbitrary formals and every positive word width.
This is Flapjack carrier infrastructure, not a HOL theorem port. Codec rejection
makes both sides none; the theorem does not supply a source-image acceptance
proof or establish that the executed caller invokes the native definition. -/
theorem wordSsaLimitVar_codec {width : Nat} [NeZero width]
    (parameters : List Nat) (program : WordProg (BitVec width)) :
    (wordLangProgToHOL program).map Compiler.Backend.WordAlloc.limitVar =
      (wordLangProgToHOL program).map (fun _ => wordSsaLimitVar parameters program) := by
  have maximum := wordProgCakeMaxVar_codec program
  cases encoded : wordLangProgToHOL program with
  | none => rfl
  | some native =>
      simp only [encoded, Option.map_some, Option.some.injEq] at maximum ⊢
      simp only [Compiler.Backend.WordAlloc.limitVar, wordSsaLimitVar]
      rw [maximum]

end Flapjack
