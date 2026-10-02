import Flapjack.RiscV.WordToStack

/-!
Original oracle: scripts/hol-probes/word_to_stack_tail_handler_probeScript.sml,
word_to_stackScript.sml comp_def495-504. Original complete result equality
(including bitmap state) is T for direct/indirect calls and both perf modes.
These generic kernel regressions exercise the actual production functions,
not the proof-side native duplicate. No HOL tags: optimized production trees
and optional failure carriers require their separate correspondence proof.
-/
namespace Flapjack.Test.WordToStackTailHandlerParity
open Flapjack RiscV

theorem nat_handler_ignored (config : WordStackConfig)
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordProg Nat × Nat × Nat)) :
    wordToStackProgNat config (.call none target arguments handler) =
      wordToStackProgNat config (.call none target arguments none) := by
  cases target <;> cases handler <;> simp only [wordToStackProgNat]

theorem nat_bitmap_handler_ignored (config : WordStackConfig)
    (builder : List Nat → List Nat) (registerCount bitmapRegister frameSlots wordBits : Nat)
    (stub : Option Nat) (state : WordStackBitmapState)
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordProg Nat × Nat × Nat)) :
    wordToStackProgNatWithBitmapBuilder config builder registerCount bitmapRegister
      frameSlots wordBits stub state (.call none target arguments handler) =
    wordToStackProgNatWithBitmapBuilder config builder registerCount bitmapRegister
      frameSlots wordBits stub state (.call none target arguments none) := by
  cases target <;> cases handler <;> simp only [wordToStackProgNatWithBitmapBuilder]

theorem nat_bitmap_state_unchanged (config : WordStackConfig)
    (builder : List Nat → List Nat) (registerCount bitmapRegister frameSlots wordBits : Nat)
    (stub : Option Nat) (state finalState : WordStackBitmapState)
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordProg Nat × Nat × Nat)) (code : StackProg Nat)
    (result : wordToStackProgNatWithBitmapBuilder config builder registerCount bitmapRegister
      frameSlots wordBits stub state (.call none target arguments handler) = some (code, finalState)) :
    finalState = state := by
  cases target <;> cases handler <;> simp [wordToStackProgNatWithBitmapBuilder] at result
  all_goals rcases result with ⟨_, _, rfl, rfl⟩
  all_goals rfl

theorem word_bitmap_handler_ignored {width : Nat} [NeZero width]
    (config : WordStackConfig) (builder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (stub : Option Nat) (state : WordStackBitmapState)
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordProg (Word width) × Nat × Nat)) :
    wordToStackProgWordWithBitmapBuilder (width := width) config builder registerCount bitmapRegister
      frameSlots wordBits stub state (.call none target arguments handler) =
    wordToStackProgWordWithBitmapBuilder (width := width) config builder registerCount bitmapRegister
      frameSlots wordBits stub state (.call none target arguments none) := by
  cases target <;> cases handler <;> simp only [wordToStackProgWordWithBitmapBuilder]

theorem word_bitmap_state_unchanged {width : Nat} [NeZero width]
    (config : WordStackConfig) (builder : List Nat → List Nat)
    (registerCount bitmapRegister frameSlots wordBits : Nat)
    (stub : Option Nat) (state finalState : WordStackBitmapState)
    (target : Option Nat) (arguments : List Nat)
    (handler : Option (Nat × WordProg (Word width) × Nat × Nat)) (code : StackProg Nat)
    (result : wordToStackProgWordWithBitmapBuilder (width := width) config builder
      registerCount bitmapRegister frameSlots wordBits stub state
      (.call none target arguments handler) = some (code, finalState)) :
    finalState = state := by
  rw [word_bitmap_handler_ignored] at result
  cases target with
  | some target =>
    simp [wordToStackProgWordWithBitmapBuilder] at result
    exact result.2.symm
  | none =>
    simp only [wordToStackProgWordWithBitmapBuilder] at result
    cases found : wordStackIndirectCallNat config arguments with
    | none => simp [found] at result
    | some value =>
      rcases value with ⟨direct, target, prelude⟩
      simp [found] at result
      exact result.2.symm

-- Original frame (k,f,f')=(4,7,9); production stores frame occupancy6,
-- so its actual f is7. Production removes original leading Seq Skip through
-- wordStackJoin; this fixture records that normalization explicitly.
private def oracleConfig (perf : Bool) : WordStackConfig :=
  { locations := [(2,.register 1),(4,.register 2),(6,.register 3)]
    scratch := 4, stackBase := 0, perf := perf, abiRegisterCount := 4, abiFrameSlots := 6 }
private def oracleState : WordStackBitmapState := { data := [4,7], length := 17 }

example : wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig false) (fun _ => [999]) 4 4 7 64 none oracleState
    (.call none (some 17) [2,4] (some (200,.move 0 [(200,202)],31,37))) =
    some (.seq (.stackFree 7) (.call none (.label 17) none), oracleState) := by
  cbv

example : wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig false) (fun _ => [999]) 4 4 7 64 none oracleState
    (.call none (some 17) [2,4] (some (200,.alloc 0 ([],[]),31,37))) =
    some (.seq (.stackFree 7) (.call none (.label 17) none), oracleState) := by
  cbv

example : wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig false) (fun _ => [999]) 4 4 7 64 none oracleState
    (.call none (none) [2,4,6] (some (200,.move 0 [(200,202)],31,37))) =
    some (.seq (.stackFree 7) (.call none (.register 3) none), oracleState) := by
  cbv

example : wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig false) (fun _ => [999]) 4 4 7 64 none oracleState
    (.call none (none) [2,4,6] (some (200,.alloc 0 ([],[]),31,37))) =
    some (.seq (.stackFree 7) (.call none (.register 3) none), oracleState) := by
  cbv

example : wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig true) (fun _ => [999]) 4 4 7 64 none oracleState
    (.call none (some 17) [2,4] (some (200,.move 0 [(200,202)],31,37))) =
    some (.seq (.stackFree 7) (.call none (.label 17) none), oracleState) := by
  cbv

example : wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig true) (fun _ => [999]) 4 4 7 64 none oracleState
    (.call none (some 17) [2,4] (some (200,.alloc 0 ([],[]),31,37))) =
    some (.seq (.stackFree 7) (.call none (.label 17) none), oracleState) := by
  cbv

example : wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig true) (fun _ => [999]) 4 4 7 64 none oracleState
    (.call none (none) [2,4,6] (some (200,.move 0 [(200,202)],31,37))) =
    some (.seq (.stackFree 7) (.call none (.register 3) none), oracleState) := by
  cbv

example : wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig true) (fun _ => [999]) 4 4 7 64 none oracleState
    (.call none (none) [2,4,6] (some (200,.alloc 0 ([],[]),31,37))) =
    some (.seq (.stackFree 7) (.call none (.register 3) none), oracleState) := by
  cbv

-- Original SOME-return controls append two 512-word bitmaps, counter19.
example : (wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig false) (fun _ => [512]) 4 4 7 64 none oracleState
    (.call (some ([2],([],[]),.skip,41,43)) (some 17) [2,4]
      (some (200,.alloc 0 ([],[]),31,37)))).map Prod.snd =
    some { data := [4,7,512,512], length := 19 } := by
  cbv

example : (wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig false) (fun _ => [512]) 4 4 7 64 none oracleState
    (.call (some ([2],([],[]),.skip,41,43)) (none) [2,4,6]
      (some (200,.alloc 0 ([],[]),31,37)))).map Prod.snd =
    some { data := [4,7,512,512], length := 19 } := by
  cbv

example : (wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig true) (fun _ => [512]) 4 4 7 64 none oracleState
    (.call (some ([2],([],[]),.skip,41,43)) (some 17) [2,4]
      (some (200,.alloc 0 ([],[]),31,37)))).map Prod.snd =
    some { data := [4,7,512,512], length := 19 } := by
  cbv

example : (wordToStackProgWordWithBitmapBuilder (width := 64)
    (oracleConfig true) (fun _ => [512]) 4 4 7 64 none oracleState
    (.call (some ([2],([],[]),.skip,41,43)) (none) [2,4,6]
      (some (200,.alloc 0 ([],[]),31,37)))).map Prod.snd =
    some { data := [4,7,512,512], length := 19 } := by
  cbv

end Flapjack.Test.WordToStackTailHandlerParity
