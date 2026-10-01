import Flapjack.Compiler.Backend.WordToStack.ProductionExpressionMaximum
import Flapjack.Compiler.Backend.WordToStack.ProductionCutsetMaximum
import Flapjack.Compiler.Backend.WordToStack.ProductionInstructionMaximum
import Flapjack.Pancake.WordLang.MaxVar

namespace Flapjack

/-- Flapjack-only accumulator normalization, with no separate HOL original. -/
private theorem foldMaximum {α : Type} (value : α → Nat) (values : List α)
    (initial : Nat) :
    values.foldl (fun result item => max result (value item)) initial =
      max initial (maxList (values.map value)) := by
  induction values generalizing initial with
  | nil => simp [maxList]
  | cons head tail ih => simp only [List.foldl_cons, List.map_cons, maxList, ih, Nat.max_assoc]

/-- Flapjack-only specialization to the production natural-name scan. -/
private theorem foldNames (values : List Nat) (initial : Nat) :
    values.foldl max initial = max initial (maxList values) := by
  induction values generalizing initial with
  | nil => simp [maxList]
  | cons head tail ih => simp only [List.foldl_cons, maxList, ih, Nat.max_assoc]

/-- Flapjack-only equality between the two full Move name scans. -/
private theorem moveMaximum (moves : List (Nat × Nat)) :
    moves.foldl (fun result move => max result (max move.1 move.2)) 0 =
      maxList (moves.map Prod.fst ++ moves.map Prod.snd) := by
  rw [foldMaximum, Nat.zero_max, maxList_append]
  induction moves with
  | nil => simp [maxList]
  | cons head tail ih =>
      simp only [List.map_cons, maxList] at *
      omega

/-- Flapjack-only normalization of the reviewed three-way maximum. -/
private theorem max3Maximum (a b c : Nat) : max3HOL a b c = max a (max b c) := by
  unfold max3HOL
  split <;> split <;> omega

/-- Flapjack-only encoder-image specialization of the reviewed instruction
correspondence. The memory premise is the actual existing guard. -/
private theorem instructionMaximum {width : Nat} [NeZero width]
    (instruction : WordInst (BitVec width))
    (supported : RiscV.allocatorMemorySupported (.inst instruction) = true)
    (native : WordLangInst (BitVec width))
    (encoded : wordLangInstToHOL instruction = some native) :
    wordInstCakeMaxVar instruction = maxVarInstHOL native := by
  have same := wordInstCakeMaxVar_codec instruction supported
  simpa only [encoded, Option.map_some, Option.some.injEq] using same.symm

/-- Internal encoder-image proof used to establish the public Option result.
This assumes only the actual encoder equation, never the target maximum or
evaluation. It is Flapjack carrier infrastructure, not a HOL theorem port. -/
private theorem encodedMaximum {width : Nat} [NeZero width]
    (program : WordProg (BitVec width))
    (supported : RiscV.allocatorMemorySupported program = true)
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    wordProgCakeMaxVar program = maxVarHOL native := by
  fun_induction wordProgCakeMaxVar program generalizing native
  all_goals
    simp only [wordLangProgToHOL, Option.map_eq_some_iff,
      Option.some.injEq] at encoded
  all_goals try subst native
  all_goals
    try simp_all [maxVarHOL, RiscV.allocatorMemorySupported,
      moveMaximum, foldNames, maxList,
      wordCutsetsCakeMaxVar_eq_cutsetsMaxHOL, wordExpCakeMaxVar_eq_maxVarExpHOL]
  case case18 =>
    rename_i target arguments handler
    cases handler with
    | none =>
        simp only [Option.some.injEq] at encoded
        subst native
        simp only [maxVarHOL]
    | some handler =>
        rcases handler with ⟨exception, body, firstLabel, secondLabel⟩
        simp only [Option.bind_eq_some_iff, Option.some.injEq] at encoded
        rcases encoded with ⟨handlerBody, _, rfl⟩
        simp only [maxVarHOL]
  all_goals try simp only [Option.bind_eq_some_iff, Option.some.injEq] at encoded
  all_goals repeat' (first | (rcases encoded with ⟨a, h, encoded⟩) | (subst native))
  all_goals try simp_all [maxVarHOL, max3Maximum, maxList_toNumSetHOL, instructionMaximum]
  all_goals try cases ‹WordRegImm (BitVec width)›
  all_goals try simp_all [maxVarHOL, max3Maximum]
  all_goals omega

/-- Full production program maximum correspondence through the actual
partial native codec under the allocator's existing checked memory guard.
No successful-codec, desired-maximum, target-evaluation or compiler-success
premise is assumed. When five-register AddCarry is codec-rejected, both mapped expressions are
none; no maximum correspondence is asserted for that case. This is Flapjack-only carrier correspondence; source-to-SSA codec image,
native frame/config integration and executed routing remain separate work. -/
theorem wordProgCakeMaxVar_codec {width : Nat} [NeZero width]
    (program : WordProg (BitVec width))
    (supported : RiscV.allocatorMemorySupported program = true) :
    (wordLangProgToHOL program).map maxVarHOL =
      (wordLangProgToHOL program).map (fun _ => wordProgCakeMaxVar program) := by
  cases encoded : wordLangProgToHOL program with
  | none => rfl
  | some native =>
      simp only [Option.map_some]
      exact congrArg some (encodedMaximum program supported native encoded).symm

end Flapjack
