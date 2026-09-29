import Flapjack.Pancake.LoopToWord.ExpCarrierCodec
import Flapjack.Pancake.LoopToWord

/-!
# Width-specialized executable Loop program codec

This Flapjack-specific bridge converts executable `LoopProg (BitVec width)`
into exact `HolLoopProg width`. It is partial exactly where an executable
expression contains the extra `crepOp` or `cmp` constructors. List-backed live
sets are translated with HOL `toNumSet`; the existing executable/faithful
relation requires duplicate-free source lists. FFI names are encoded using
`MlString.ofString`, which truncates non-byte Lean characters; reverse name
equality requires the explicit `NameRanged` premise. The production route
checks the FFI byte range before using this codec and preserves the legacy
implementation for executable-only syntax.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.LoopToWord

/-- Convert executable Loop syntax to the fixed-width HOL carrier. Every
program constructor is retained; conversion can fail only in an expression
subtree rejected by `executableLoopExpToHol`. -/
def executableLoopProgToHol {width : Nat} [NeZero width] :
    LoopProg (BitVec width) → Option (HolLoopProg width)
  | .skip => some .skip
  | .assign name value => (executableLoopExpToHol value).map (.assign name)
  | .primitive destinations operator arguments =>
      some (.primitive destinations operator arguments)
  | .arith operation => some (.arith operation)
  | .store address value =>
      (executableLoopExpToHol address).map (fun address => .store address value)
  | .setGlobal address value =>
      (executableLoopExpToHol value).map (.setGlobal address)
  | .load32 address destination => some (.load32 address destination)
  | .loadByte address destination => some (.loadByte address destination)
  | .store32 address value => some (.store32 address value)
  | .storeByte address value => some (.storeByte address value)
  | .seq first second => do
      let first ← executableLoopProgToHol first
      let second ← executableLoopProgToHol second
      pure (.seq first second)
  | .ite operator condition right thenBranch elseBranch live => do
      let thenBranch ← executableLoopProgToHol thenBranch
      let elseBranch ← executableLoopProgToHol elseBranch
      pure (.ite operator condition right thenBranch elseBranch
        (Flapjack.LoopToWord.toNumSetHOL live))
  | .loop liveIn body liveOut => do
      let body ← executableLoopProgToHol body
      pure (.loop (Flapjack.LoopToWord.toNumSetHOL liveIn) body
        (Flapjack.LoopToWord.toNumSetHOL liveOut))
  | .break label => some (.break label)
  | .continue label => some (.continue label)
  | .raise exception => some (.raise exception)
  | .return values => some (.return values)
  | .shMem operator name address =>
      (executableLoopExpToHol address).map (.shMem operator name)
  | .tick => some .tick
  | .mark body => (executableLoopProgToHol body).map .mark
  | .fail => some .fail
  | .locValue destination source => some (.locValue destination source)
  | .call returns target arguments handler => do
      let returns ← match returns with
        | none => pure none
        | some (values, live) =>
            pure (some (values, Flapjack.LoopToWord.toNumSetHOL live))
      let handler ← match handler with
        | none => pure none
        | some (exception, handlerBody, returnBody, live) => do
            let handlerBody ← executableLoopProgToHol handlerBody
            let returnBody ← executableLoopProgToHol returnBody
            pure (some (exception, handlerBody, returnBody,
              Flapjack.LoopToWord.toNumSetHOL live))
      pure (.call returns target arguments handler)
  | .ffi function configuration configurationLength array arrayLength live =>
      some (.ffi (ofString function) configuration configurationLength
        array arrayLength (Flapjack.LoopToWord.toNumSetHOL live))
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-- A live-set list accepted by `loopProgExecRel` must be duplicate-free; the
HOL carrier itself is an Spt set. -/
def loopProgLiveSetsNodup : LoopProg α → Prop
  | .seq first second => loopProgLiveSetsNodup first ∧ loopProgLiveSetsNodup second
  | .ite _ _ _ thenBranch elseBranch live =>
      live.Nodup ∧ loopProgLiveSetsNodup thenBranch ∧ loopProgLiveSetsNodup elseBranch
  | .loop liveIn body liveOut =>
      liveIn.Nodup ∧ loopProgLiveSetsNodup body ∧ liveOut.Nodup
  | .mark body => loopProgLiveSetsNodup body
  | .call returns _ _ handler =>
      (match returns with | none => True | some (_, live) => live.Nodup) ∧
      (match handler with
       | none => True
       | some (_, handlerBody, returnBody, live) =>
           live.Nodup ∧ loopProgLiveSetsNodup handlerBody ∧
             loopProgLiveSetsNodup returnBody)
  | _ => True

/-- HOL `toNumSet` preserves the key-membership view of every source list,
including duplicates. -/
theorem sptLookup_toNumSetHOL_iff_mem (key : Nat) :
    ∀ live : List Nat,
      sptLookup key (Flapjack.LoopToWord.toNumSetHOL live) = some () ↔
        key ∈ live := by
  intro live
  induction live with
  | nil => simp [Flapjack.LoopToWord.toNumSetHOL]
  | cons head tail ih =>
      by_cases hkey : key = head
      · subst key
        simp [Flapjack.LoopToWord.toNumSetHOL,
          sptLookup_sptInsert_same]
      · simp [Flapjack.LoopToWord.toNumSetHOL,
          sptLookup_sptInsert_ne, hkey, ih]

/-- Duplicate-free source live sets satisfy the existing executable/faithful
representation relation after `toNumSet` conversion. -/
theorem numSetListRel_toNumSetHOL {live : List Nat} (hnodup : live.Nodup) :
    numSetListRel live (Flapjack.LoopToWord.toNumSetHOL live) := by
  refine ⟨hnodup, ?_⟩
  intro key
  exact sptLookup_toNumSetHOL_iff_mem key live

end Flapjack
