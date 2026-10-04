import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.LiveLength

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack-only proof packaging for the original length bound and gap
equality. There is no separate HOL declaration for this implication. -/
@[irreducible] private def BitmapAccounting {α : Type} (before after : AppList α × Nat) : Prop :=
  (appListAppend before.1).length ≤ before.2 →
    (appListAppend after.1).length ≤ after.2 ∧
      before.2 - (appListAppend before.1).length =
        after.2 - (appListAppend after.1).length

private theorem bitmapAccounting_refl {α : Type} (bs : AppList α × Nat) :
    BitmapAccounting bs bs := by
  unfold BitmapAccounting
  exact fun h => ⟨h, rfl⟩

private theorem bitmapAccounting_trans {α : Type} {a b c : AppList α × Nat}
    (first : BitmapAccounting a b) (second : BitmapAccounting b c) :
    BitmapAccounting a c := by
  unfold BitmapAccounting at *
  intro bound
  obtain ⟨middleBound, firstGap⟩ := first bound
  obtain ⟨lastBound, secondGap⟩ := second middleBound
  exact ⟨lastBound, firstGap.trans secondGap⟩

private theorem wLive_bitmapAccounting {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (program : HolProg width)
    (output : AppList (BitVec width) × Nat)
    (h : wLiveNative live bs frame = (program, output)) : BitmapAccounting bs output := by
  unfold BitmapAccounting
  exact fun bound => wLiveLength live bs frame program output ⟨h, bound⟩

private theorem insert_bitmapAccounting {α : Type} (words : List α)
    (bs output : AppList α × Nat) (index : Nat)
    (h : insertBitmap words bs = (output, index)) : BitmapAccounting bs output := by
  have hout := congrArg Prod.fst h
  simp only [insertBitmap] at hout
  rw [← hout]
  unfold BitmapAccounting
  intro bound
  rw [(appListAppend_thm bs.1 (.list words) words).1]
  simp only [appListAppend, appendAux, List.append_nil, List.length_append]
  exact ⟨Nat.add_le_add_right bound _, by omega⟩

private theorem compNative_bitmapAccounting {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) :
    BitmapAccounting bs (compNative conf perf program bs frame).2 := by
  apply compNative.induct conf perf frame
    (motive := fun program bs => BitmapAccounting bs (compNative conf perf program bs frame).2)
  all_goals intros
  all_goals try simp_all only []
  all_goals simp only [compNative, *]
  all_goals try first
    | exact bitmapAccounting_refl _
    | solve_by_elim (maxDepth := 5) only
        [*, bitmapAccounting_trans, wLive_bitmapAccounting, insert_bitmapAccounting]
  case case22 =>
    rename_i input destination arguments target values live returnCode label1 label2
      pre liveBody afterLive liveEq returnBody afterReturn returnEq handlerVariable
      handlerCode handlerLabel1 handlerLabel2 handlerBody afterHandler handlerEq
      targetEq returnIH handlerIH
    exact bitmapAccounting_trans (wLive_bitmapAccounting live input frame liveBody afterLive liveEq)
      (bitmapAccounting_trans returnIH handlerIH)

/-- Complete original bitmap accounting theorem: the actual compiler output
equation and sole initial length bound imply both final accounting conjuncts. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compImpLength {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (body : HolProg width)
    (output : AppList (BitVec width) × Nat)
    (h : compNative conf perf program bs frame = (body, output) ∧
      (appListAppend bs.1).length ≤ bs.2) :
    (appListAppend output.1).length ≤ output.2 ∧
      bs.2 - (appListAppend bs.1).length = output.2 - (appListAppend output.1).length := by
  have accounting := compNative_bitmapAccounting conf perf program bs frame
  unfold BitmapAccounting at accounting
  have hout := congrArg Prod.snd h.1
  simpa only [hout] using accounting h.2

end Flapjack.Compiler.Backend.WordToStack.Native
