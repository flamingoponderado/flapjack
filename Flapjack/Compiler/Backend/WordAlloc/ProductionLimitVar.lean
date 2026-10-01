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

/-- Actual production SSA using native `limitVar` on the complete encoded
input program. Codec rejection stays explicit. This is an executable caller
boundary for subsequent pipeline wiring, not a HOL theorem port or proof that
the source compiler already invokes this boundary. -/
def wordFullSsaCcTransNativeLimit {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordProg (BitVec width)) :
    Option (WordSsaState × List Nat × WordProg (BitVec width)) :=
  (wordLangProgToHOL program).map (fun native =>
    wordFullSsaCcTransFromLimit (Compiler.Backend.WordAlloc.limitVar native)
      parameterCount program)

/-- Whole-result correspondence at the partial codec boundary, for all
programs and parameter counts. No allocation success or target execution is
assumed. Flapjack production-carrier infrastructure with no HOL original. -/
theorem wordFullSsaCcTransNativeLimit_eq {width : Nat} [NeZero width]
    (parameterCount : Nat) (program : WordProg (BitVec width)) :
    wordFullSsaCcTransNativeLimit parameterCount program =
      (wordLangProgToHOL program).map (fun _ => wordFullSsaCcTrans parameterCount program) := by
  have limit := wordSsaLimitVar_codec (wordSsaAbiParameters parameterCount) program
  cases encoded : wordLangProgToHOL program with
  | none => simp [wordFullSsaCcTransNativeLimit, encoded]
  | some native =>
      simp only [encoded, Option.map_some, Option.some.injEq] at limit
      simp only [wordFullSsaCcTransNativeLimit, encoded, Option.map_some, limit]
      rw [← wordFullSsaCcTrans_fromLimit]

end Flapjack
