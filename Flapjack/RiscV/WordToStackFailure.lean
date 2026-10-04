import Flapjack.RiscV.WordToStack

/-!
# Classified Word-to-Stack lowering failures

Flapjack diagnostic infrastructure (no HOL counterpart; HOL `word_to_stack$compile` is
total). The executed bitmap-aware Word-to-Stack lowering
`wordToStackProgWordWithBitmapBuilder` is `Option`-valued: each leaf helper may reject its
input. `wordToStackFirstFailure` searches the program without its bitmap state
(no failure depends on that state), and returns a sequence path and failure kind.
The proof does not establish that this is the lowering's first rejecting leaf.
`wordToStackFirstFailure_complete` proves that every
failed lowering is located, so pipeline callers report a precise path and kind instead of an
empty-path fallback (GitHub issue #1158).
-/

namespace Flapjack.RiscV

/-- The leaf operation of the bitmap-aware Word-to-Stack lowering that rejected its input. -/
inductive WordToStackFailureKind where
  | move | assign | const | arith | inst | get | store | set
  | condition | returnValues | locValue | indirectCall
  | opCurrHeap | install | bufferWrite | ffi | shareInst
  deriving DecidableEq, Repr

/-- A failure located by diagnostic traversal, with its sequence
path (`0`/`1` for `Seq` first/second, `If` then/else, call return/handler program; `0` for
`Loop`/`MustTerminate` bodies). Completeness, not agreement on the first failure
or traversal order, is proved below. -/
def wordToStackFirstFailure [NeZero width] (config : WordStackConfig) :
    WordProg (Word width) → Option (List Nat × WordToStackFailureKind)
  | .skip => none
  | .move _ moves => match wordStackMoveList (α := Nat) config moves with
      | some _ => none
      | none => some ([], .move)
  | .assign destination value =>
      match wordStackCompileExpNat config destination (wordExpToNat value) with
      | some _ => none
      | none => some ([], .assign)
  | .inst (.const destination value) =>
      match wordStackCompileExpToPhysicalNat config destination (.const value.toNat) with
      | some _ => none
      | none => some ([], .const)
  | .inst (.arith (.binOp operator destination sourceLeft sourceRight)) =>
      match wordStackArithInst config
          (wordArithToNat (.binOp operator destination sourceLeft sourceRight)) with
      | some _ => none
      | none => some ([], .arith)
  | .inst (.arith (.shift operator destination sourceLeft sourceRight)) =>
      match wordStackArithInst config
          (wordArithToNat (.shift operator destination sourceLeft sourceRight)) with
      | some _ => none
      | none => some ([], .arith)
  | .inst instruction =>
      match wordToStackInst config (wordInstToNat instruction) with
      | some _ => none
      | none => some ([], .inst)
  | .get destination store =>
      match wordStackGetNat config destination (wordStoreToNat store) with
      | some _ => none
      | none => some ([], .get)
  | .store address value =>
      match (match address with
          | .const _ | .var _ | .lookup _ =>
              wordStackCompileStoreNat config (wordExpToNat address) (.var value)
          | _ => wordStackCompileStoreNatNested config (wordExpToNat address) (.var value)) with
      | some _ => none
      | none => some ([], .store)
  | .set store value =>
      match wordStackSetNat config (wordStoreToNat store) (wordExpToNat value) with
      | some _ => none
      | none => some ([], .set)
  | .seq first second =>
      match wordToStackFirstFailure config first with
      | some (path, kind) => some (0 :: path, kind)
      | none => (wordToStackFirstFailure config second).map fun (path, kind) => (1 :: path, kind)
  | .ite _ condition right thenBranch elseBranch =>
      match wordStackConditionOperands config condition (wordRegImmToNat right) with
      | none => some ([], .condition)
      | some _ =>
          match wordToStackFirstFailure config thenBranch with
          | some (path, kind) => some (0 :: path, kind)
          | none => (wordToStackFirstFailure config elseBranch).map
              fun (path, kind) => (1 :: path, kind)
  | .loop _ body _ =>
      (wordToStackFirstFailure config body).map fun (path, kind) => (0 :: path, kind)
  | .mustTerminate body =>
      (wordToStackFirstFailure config body).map fun (path, kind) => (0 :: path, kind)
  | .break _ | .continue _ | .raise _ | .tick => none
  | .return returnLabel values =>
      match wordStackReturn (α := Nat) config returnLabel values with
      | some _ => none
      | none => some ([], .returnValues)
  | .locValue destination source =>
      match wordStackLocValue (α := Nat) config destination source with
      | some _ => none
      | none => some ([], .locValue)
  | .call (some (_, _, returnProgram, _, _)) (some _) _ (some (_, body, _, _)) =>
      match wordToStackFirstFailure config returnProgram with
      | some (path, kind) => some (0 :: path, kind)
      | none => (wordToStackFirstFailure config body).map fun (path, kind) => (1 :: path, kind)
  | .call (some (_, _, returnProgram, _, _)) (some _) _ none =>
      (wordToStackFirstFailure config returnProgram).map fun (path, kind) => (0 :: path, kind)
  | .call none (some _) _ _ => none
  | .call none none arguments _ =>
      match wordStackIndirectCallNat config arguments with
      | some _ => none
      | none => some ([], .indirectCall)
  | .call (some (_, _, returnProgram, _, _)) none arguments none =>
      match wordStackIndirectCallNat config arguments with
      | none => some ([], .indirectCall)
      | some _ =>
          (wordToStackFirstFailure config returnProgram).map fun (path, kind) => (0 :: path, kind)
  | .call (some (_, _, returnProgram, _, _)) none arguments (some (_, body, _, _)) =>
      match wordStackIndirectCallNat config arguments with
      | none => some ([], .indirectCall)
      | some _ =>
          match wordToStackFirstFailure config returnProgram with
          | some (path, kind) => some (0 :: path, kind)
          | none => (wordToStackFirstFailure config body).map
              fun (path, kind) => (1 :: path, kind)
  | .alloc _ _ | .storeConsts _ _ _ _ _ => none
  | .opCurrHeap operator destination source =>
      match wordStackOpCurrHeap (α := Nat) config operator destination source with
      | some _ => none
      | none => some ([], .opCurrHeap)
  | .install codeBuffer codeLength dataBuffer dataLength _ =>
      match wordStackInstall (α := Nat) config codeBuffer codeLength dataBuffer dataLength with
      | some _ => none
      | none => some ([], .install)
  | .codeBufferWrite address value =>
      match wordStackBufferWrite (α := Nat) config true address value with
      | some _ => none
      | none => some ([], .bufferWrite)
  | .dataBufferWrite address value =>
      match wordStackBufferWrite (α := Nat) config false address value with
      | some _ => none
      | none => some ([], .bufferWrite)
  | .ffi function configuration configurationLength array arrayLength _ =>
      match wordStackFfiCake (α := Nat) config function configuration configurationLength
          array arrayLength with
      | some _ => none
      | none => some ([], .ffi)
  | .shareInst operator name address =>
      match wordStackCompileSharedNat config operator name (wordExpToNat address) with
      | some _ => none
      | none => some ([], .shareInst)
termination_by program => sizeOf program
decreasing_by
  all_goals first | decreasing_trivial | (simp [sizeOf] <;> omega)

/-- If no leaf is located, the bitmap-aware lowering succeeds from every bitmap state. -/
theorem wordToStackFirstFailure_none [BEq Nat] [NeZero width] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat) (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) :
    ∀ (program : WordProg (Word width)), wordToStackFirstFailure config program = none →
      ∀ state, (wordToStackProgWordWithBitmapBuilder config bitmapBuilder registerCount
        bitmapRegister frameSlots wordBits storeConstsStub state program).isSome := by
  intro program
  induction hsize : sizeOf program using Nat.strongRecOn generalizing program with
  | ind n ih =>
  intro hnone state
  have ih' : ∀ q : WordProg (Word width), sizeOf q < sizeOf program →
      wordToStackFirstFailure config q = none → ∀ st,
        (wordToStackProgWordWithBitmapBuilder config bitmapBuilder registerCount
          bitmapRegister frameSlots wordBits storeConstsStub st q).isSome :=
    fun q hq => ih _ (hsize ▸ hq) q rfl
  clear ih hsize
  have get : ∀ q (hq : sizeOf q < sizeOf program), wordToStackFirstFailure config q = none →
      ∀ st, ∃ r, wordToStackProgWordWithBitmapBuilder config bitmapBuilder registerCount
        bitmapRegister frameSlots wordBits storeConstsStub st q = some r :=
    fun q hq h st => Option.isSome_iff_exists.mp (ih' q hq h st)
  cases program with
  | inst i =>
    cases i with
    | const d v =>
      simp only [wordToStackFirstFailure] at hnone
      unfold wordToStackProgWordWithBitmapBuilder; split at hnone <;> simp_all
    | arith a =>
      cases a <;> simp only [wordToStackFirstFailure] at hnone <;>
        unfold wordToStackProgWordWithBitmapBuilder <;> split at hnone <;> simp_all
    | _ =>
      simp only [wordToStackFirstFailure] at hnone
      unfold wordToStackProgWordWithBitmapBuilder; split at hnone <;> simp_all
  | seq a b =>
    simp only [wordToStackFirstFailure] at hnone
    split at hnone
    · simp at hnone
    · rename_i ha
      have hb : wordToStackFirstFailure config b = none := by simpa using hnone
      obtain ⟨⟨ca, sa⟩, hca⟩ := get a (by simp; omega) ha state
      obtain ⟨⟨cb, sb⟩, hcb⟩ := get b (by simp; omega) hb sa
      unfold wordToStackProgWordWithBitmapBuilder
      simp only
      split <;> simp [hca, hcb]
  | ite op c r t e =>
    simp only [wordToStackFirstFailure] at hnone
    split at hnone
    · simp at hnone
    · rename_i operands hop
      split at hnone
      · simp at hnone
      · rename_i ht
        have he : wordToStackFirstFailure config e = none := by simpa using hnone
        obtain ⟨⟨ct, st⟩, hct⟩ := get t (by simp; omega) ht state
        obtain ⟨⟨ce, se⟩, hce⟩ := get e (by simp; omega) he st
        unfold wordToStackProgWordWithBitmapBuilder
        obtain ⟨p1, p2, p3⟩ := operands
        simp [hop, hct, hce]
  | loop l body x =>
    simp only [wordToStackFirstFailure] at hnone
    have hb : wordToStackFirstFailure config body = none := by simpa using hnone
    obtain ⟨⟨cb, sb⟩, hcb⟩ := get body (by simp; omega) hb state
    unfold wordToStackProgWordWithBitmapBuilder; simp [hcb]
  | mustTerminate body =>
    simp only [wordToStackFirstFailure] at hnone
    have hb : wordToStackFirstFailure config body = none := by simpa using hnone
    unfold wordToStackProgWordWithBitmapBuilder; exact ih' body (by simp) hb state
  | store address value =>
    unfold wordToStackFirstFailure at hnone
    unfold wordToStackProgWordWithBitmapBuilder
    cases address <;> simp only at hnone ⊢ <;> split at hnone <;> simp_all
  | call returns target arguments handler =>
    rcases returns with _ | ⟨ds, cs, rp, rl, el⟩ <;> rcases target with _ | t <;>
      rcases handler with _ | ⟨ex, body, hl, hel⟩
    · -- indirect tail call
      unfold wordToStackFirstFailure at hnone; unfold wordToStackProgWordWithBitmapBuilder
      split at hnone <;> simp_all
    · unfold wordToStackFirstFailure at hnone; unfold wordToStackProgWordWithBitmapBuilder
      split at hnone <;> simp_all
    · unfold wordToStackProgWordWithBitmapBuilder; simp
    · unfold wordToStackProgWordWithBitmapBuilder; simp
    · -- indirect returning call without handler
      unfold wordToStackFirstFailure at hnone
      split at hnone
      · simp at hnone
      · rename_i call hcall
        have hr : wordToStackFirstFailure config rp = none := by simpa using hnone
        unfold wordToStackProgWordWithBitmapBuilder
        obtain ⟨d, tg, ld⟩ := call
        obtain ⟨⟨cr, sr⟩, hcr⟩ := get rp (by simp; omega) hr
          (wordStackCallLiveBitmapWord config bitmapBuilder bitmapRegister frameSlots state
            (some (ds, cs, rp, rl, el))).2
        simp [hcall, hcr]
    · -- indirect returning call with handler
      unfold wordToStackFirstFailure at hnone
      split at hnone
      · simp at hnone
      · rename_i call hcall
        split at hnone
        · simp at hnone
        · rename_i hr
          have hb : wordToStackFirstFailure config body = none := by simpa using hnone
          unfold wordToStackProgWordWithBitmapBuilder
          obtain ⟨d, tg, ld⟩ := call
          obtain ⟨⟨cr, sr⟩, hcr⟩ := get rp (by simp; omega) hr
            (wordStackCallLiveBitmapWord config bitmapBuilder bitmapRegister frameSlots state
              (some (ds, cs, rp, rl, el))).2
          obtain ⟨⟨cb, sb⟩, hcb⟩ := get body (by simp; omega) hb sr
          simp [hcall, hcr, hcb]
    · -- direct returning call without handler
      unfold wordToStackFirstFailure at hnone
      have hr : wordToStackFirstFailure config rp = none := by simpa using hnone
      unfold wordToStackProgWordWithBitmapBuilder
      obtain ⟨⟨cr, sr⟩, hcr⟩ := get rp (by simp; omega) hr
        (wordStackCallLiveBitmapWord config bitmapBuilder bitmapRegister frameSlots state
          (some (ds, cs, rp, rl, el))).2
      simp [hcr]
    · -- direct returning call with handler
      unfold wordToStackFirstFailure at hnone
      split at hnone
      · simp at hnone
      · rename_i hr
        have hb : wordToStackFirstFailure config body = none := by simpa using hnone
        unfold wordToStackProgWordWithBitmapBuilder
        obtain ⟨⟨cr, sr⟩, hcr⟩ := get rp (by simp; omega) hr
          (wordStackCallLiveBitmapWord config bitmapBuilder bitmapRegister frameSlots state
            (some (ds, cs, rp, rl, el))).2
        obtain ⟨⟨cb, sb⟩, hcb⟩ := get body (by simp; omega) hb sr
        simp [hcr, hcb]
  | _ =>
    first
      | (simp only [wordToStackFirstFailure] at hnone
         unfold wordToStackProgWordWithBitmapBuilder; split at hnone <;> simp_all; done)
      | (unfold wordToStackProgWordWithBitmapBuilder; simp; done)

/-- Every failed bitmap-aware lowering is located: the empty-path fallback is unreachable. -/
theorem wordToStackFirstFailure_complete [BEq Nat] [NeZero width] (config : WordStackConfig)
    (bitmapBuilder : List Nat → List Nat) (registerCount bitmapRegister frameSlots wordBits : Nat)
    (storeConstsStub : Option Nat) (state : WordStackBitmapState) (program : WordProg (Word width))
    (h : wordToStackProgWordWithBitmapBuilder config bitmapBuilder registerCount bitmapRegister
      frameSlots wordBits storeConstsStub state program = none) :
    (wordToStackFirstFailure config program).isSome := by
  cases hf : wordToStackFirstFailure config program
  · have := wordToStackFirstFailure_none config bitmapBuilder registerCount bitmapRegister
      frameSlots wordBits storeConstsStub program hf state
    simp [h] at this
  · rfl

/-- The function-level lowerings used by the executed pipeline fail only where the
located leaf fails. -/
theorem wordToStackFirstFailure_complete_function [NeZero width] (config : WordStackConfig)
    (parameters : List Nat) (sourceRegister : Nat → Nat)
    (registerCount bitmapRegister frameSlots : Nat) (storeConstsStub : Option Nat)
    (state : WordStackBitmapState) (program : WordProg (Word width)) :
    (wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMovesWithSources config
        parameters sourceRegister registerCount bitmapRegister frameSlots storeConstsStub state
        program = none →
      (wordToStackFirstFailure config program).isSome) ∧
    (wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMovesWithSources config
        parameters sourceRegister registerCount bitmapRegister frameSlots storeConstsStub state
        program = none →
      (wordToStackFirstFailure config program).isSome) ∧
    (wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMoves config
        parameters registerCount bitmapRegister frameSlots storeConstsStub state
        program = none →
      (wordToStackFirstFailure config program).isSome) ∧
    (wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMoves config
        parameters registerCount bitmapRegister frameSlots storeConstsStub state
        program = none →
      (wordToStackFirstFailure config program).isSome) := by
  have key : wordToStackProgWordWithLocationBitmapsFused config registerCount bitmapRegister
      frameSlots width storeConstsStub state program = none →
      (wordToStackFirstFailure config program).isSome :=
    wordToStackFirstFailure_complete config _ registerCount bitmapRegister frameSlots width
      storeConstsStub state program
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> apply key <;>
    simp only [wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMovesWithSources,
      wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMovesWithSources,
      wordToStackFunctionWithParametersAndLocationBitmapsAfterDeadMoves,
      wordToStackFunctionWithCakeFrameAndLocationBitmapsAfterDeadMoves] at h <;>
    cases hf : wordToStackProgWordWithLocationBitmapsFused config registerCount bitmapRegister
      frameSlots width storeConstsStub state program <;> simp_all

end Flapjack.RiscV
