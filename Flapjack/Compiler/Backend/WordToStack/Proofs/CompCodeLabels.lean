import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.CodeLabels
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterLabels
import Flapjack.Pancake.WordConvs.CodeLabels
import Flapjack.Pancake.WordConvs
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Image
import Mathlib.Tactic.Tauto

/-! Full referenced-code label bound for the literal Word-to-Stack compiler.
The private equations are Flapjack-specific proof infrastructure for native
lowering; they do not claim separately named HOL originals or evaluation
simulation. All emitted code and the full original handler guard are retained.
-/

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

private theorem moveSingleLabels {width : Nat} [NeZero width]
    (xy : Sum Nat Nat × Sum Nat Nat) (frame : Nat × Nat × Nat) :
    getCodeLabels (wMoveSingleNative (width := width) xy frame) = ∅ := by
  rcases xy with ⟨x, y⟩
  cases x <;> cases y <;> simp [wMoveSingleNative, getCodeLabels]

private theorem moveAuxLabels {width : Nat} [NeZero width]
    (moves : List (Sum Nat Nat × Sum Nat Nat)) (frame : Nat × Nat × Nat) :
    getCodeLabels (wMoveAuxNative (width := width) moves frame) = ∅ := by
  induction moves with
  | nil => simp [wMoveAuxNative, getCodeLabels]
  | cons xy rest ih =>
    cases rest with
    | nil => exact moveSingleLabels xy frame
    | cons next tail => simp only [wMoveAuxNative, getCodeLabels, moveSingleLabels,
        ih, Set.empty_union]

private theorem moveLabels {width : Nat} [NeZero width]
    (moves : List (Nat × Nat)) (frame : Nat × Nat × Nat) :
    getCodeLabels (wMoveNative (width := width) moves frame) = ∅ := by
  exact moveAuxLabels _ frame

private theorem write1Labels {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat)
    (labels : Set (Nat × Nat)) (h : ∀ n, getCodeLabels (g n) = labels) :
    getCodeLabels (wRegWrite1Native g r frame) = labels := by
  simp only [wRegWrite1Native]
  split <;> simp [getCodeLabels, h]

private theorem write2Labels {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat)
    (labels : Set (Nat × Nat)) (h : ∀ n, getCodeLabels (g n) = labels) :
    getCodeLabels (wRegWrite2Native g r frame) = labels := by
  simp only [wRegWrite2Native]
  split <;> simp [getCodeLabels, h]

private theorem loadLabels {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (p : HolProg width) :
    getCodeLabels (wStackLoadNative loads p) = getCodeLabels p :=
  (getCodeHandlerLabelsWStackLoad loads p 0).1

private theorem loadHandlers {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (p : HolProg width) (owner : Nat) :
    stackGetHandlerLabels owner (wStackLoadNative loads p) = stackGetHandlerLabels owner p :=
  (getCodeHandlerLabelsWStackLoad loads p owner).2

private theorem write1LabelEquation {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat) :
    getCodeLabels (wRegWrite1Native g r frame) =
      if r / 2 < frame.1 then getCodeLabels (g (r / 2))
      else getCodeLabels (g frame.1) := by
  simp only [wRegWrite1Native]
  split <;> simp [getCodeLabels]

private theorem shareLabels {width : Nat} [NeZero width]
    (op : HolMemop) (r : Nat) (address : HolAddr width) (frame : Nat × Nat × Nat) :
    getCodeLabels (wShareInstNative op r address frame) = ∅ := by
  cases address
  cases op <;> simp [wShareInstNative, loadLabels, write1LabelEquation, getCodeLabels]

private theorem instLabels {width : Nat} [NeZero width]
    (i : HolInst width) (frame : Nat × Nat × Nat) :
    getCodeLabels (wInstNative i frame) = ∅ := by
  unfold wInstNative
  split
  all_goals try split
  all_goals try simp only [*]
  all_goals try simp only [loadLabels]
  all_goals first
    | exact write1Labels _ _ _ ∅ (fun _ => rfl)
    | exact write2Labels _ _ _ ∅ (fun _ => write1Labels _ _ _ ∅ (fun _ => rfl))
    | rfl

private theorem freeLabels {width : Nat} [NeZero width]
    (slots : Nat) (program : HolProg width) :
    getCodeLabels (seqStackFreeNative slots program) = getCodeLabels program := by
  by_cases h : slots = 0 <;> simp [seqStackFreeNative, h, getCodeLabels]

private theorem callDestFacts {width : Nat} [NeZero width]
    (pos : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat) :
    getCodeLabels (callDestNative (width := width) pos args frame).1 = ∅ ∧
    getCodeLabels (StackLang.Prog.call none (callDestNative (width := width) pos args frame).2 none : HolProg width) ⊆
      insert (raiseStubLocation, 0)
        ((fun label => (label, 0)) '' (match pos with | some label => {label} | none => ∅)) := by
  cases pos with
  | some label => simp [callDestNative, getCodeLabels]
  | none =>
    by_cases h : args.length = 0
    · simp [callDestNative, h, getCodeLabels]
    · simp [callDestNative, h, loadLabels, getCodeLabels]

private theorem stackArgsLabels {width : Nat} [NeZero width] {α β : Type}
    (dest : Sum α β) (count : Nat) (frame : Nat × Nat × Nat) :
    getCodeLabels (stackArgsNative (width := width) dest count frame) = ∅ := by
  simp only [stackArgsNative, stackMoveCodeLabels, getCodeLabels]

private theorem copyLabels {width : Nat} [NeZero width] {β : Type}
    (perf handle : Bool) (frame : Nat × Nat × Nat) (vs : List β) (p : HolProg width) :
    getCodeLabels (copyRetNative perf handle frame vs p) = getCodeLabels p :=
  (getCodeHandlerLabelsCopyRet perf handle frame vs p 0).1

private theorem copyHandlers {width : Nat} [NeZero width] {β : Type}
    (perf handle : Bool) (frame : Nat × Nat × Nat) (vs : List β) (p : HolProg width) (owner : Nat) :
    stackGetHandlerLabels owner (copyRetNative perf handle frame vs p) = stackGetHandlerLabels owner p :=
  (getCodeHandlerLabelsCopyRet perf handle frame vs p owner).2

private theorem pushLabels {width : Nat} [NeZero width]
    (l1 l2 : Nat) (frame : Nat × Nat × Nat) :
    getCodeLabels (pushHandlerNative (width := width) false l1 l2 frame) = {(l1, l2)} := by
  simp [pushHandlerNative, getCodeLabels]

private theorem popLabels {width : Nat} [NeZero width]
    (frame : Nat × Nat × Nat) (p : HolProg width) :
    getCodeLabels (popHandlerNative false frame p) = getCodeLabels p := by
  simp [popHandlerNative, getCodeLabels]

private theorem popHandlers {width : Nat} [NeZero width]
    (frame : Nat × Nat × Nat) (p : HolProg width) (owner : Nat) :
    stackGetHandlerLabels owner (popHandlerNative false frame p) = stackGetHandlerLabels owner p := by
  simp [popHandlerNative, stackGetHandlerLabels]

/-- Full original comp code-label bound, with only the original good-handler
guard and perf=false hypothesis. Arbitrary assembler config, bitmap state,
frame tuple and owner are retained; only the positive HOL word dimension is
translated to the width-indexed native BitVec carrier. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_comp_code_labels" (words_as_type_indexed_bitvec)]
theorem wordToStackCompCodeLabels {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (owner : Nat)
    (good : goodHandlersHOL owner program = true) (noPerf : perf = false) :
    getCodeLabels (compNative conf perf program bs frame).1 ⊆
      insert (raiseStubLocation, 0) (insert (storeConstsStubLocation, 0)
        ((fun label => (label, 0)) '' getCodeLabelsHOL program ∪
          stackGetHandlerLabels owner (compNative conf perf program bs frame).1)) := by
  subst perf
  revert good
  apply compNative.induct conf false frame
    (motive := fun program bs => goodHandlersHOL owner program = true →
      getCodeLabels (compNative conf false program bs frame).1 ⊆
        insert (raiseStubLocation, 0) (insert (storeConstsStubLocation, 0)
          ((fun label => (label, 0)) '' getCodeLabelsHOL program ∪
            stackGetHandlerLabels owner (compNative conf false program bs frame).1)))
  all_goals intros
  all_goals try simp_all only []
  all_goals simp only [compNative, *]
  all_goals simp_all only [goodHandlersHOL, Bool.and_eq_true]
  all_goals simp only [getCodeLabels, stackGetHandlerLabels, getCodeLabelsHOL,
    moveLabels, instLabels, freeLabels, loadLabels, loadHandlers]
  all_goals try simp
  all_goals try simp_all only [loadLabels, loadHandlers, getCodeLabels, stackGetHandlerLabels,
    write1LabelEquation, shareLabels, Set.empty_union, Set.image_union, true_implies,
    ite_self]
  all_goals try simp only [Set.subset_def, Set.mem_insert_iff, Set.mem_union] at *
  all_goals try solve | intro label member; cases member
  all_goals try solve | aesop (config := { enableSimp := false, maxRuleApplications := 30 })

  case case11 =>
    rename_i leftIH rightIH
    constructor
    · intro label member
      rcases leftIH label member with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · intro label member
      rcases rightIH label member with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

  case case12 =>
    rename_i leftIH rightIH
    constructor
    · intro label member
      rcases leftIH label member with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · intro label member
      rcases rightIH label member with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

  case case13 =>
    rename_i leftIH rightIH
    intro label member
    rcases member with member | member
    · rcases leftIH label member with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rcases rightIH label member with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

  case case14 =>
    rename_i leftIH rightIH
    intro label member
    rcases member with member | member
    · rcases leftIH label member with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rcases rightIH label member with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

  case case23 =>
    rename_i liveEq
    have empty := wLiveCodeLabels _ _ _ _ _ liveEq
    simp [empty]

  case case20 =>
    rename_i pos args handler dest q eq
    have facts := callDestFacts (width := width) pos args frame
    rw [eq] at facts
    rcases facts with ⟨empty, direct⟩
    simp only [getCodeLabels, Set.subset_def, Set.mem_insert_iff] at direct
    simp only [empty, Set.mem_empty_iff_false, false_implies, forall_const, true_and,
      Set.union_empty] at *
    intro label member
    rcases direct label member with stub | source
    · exact Or.inl stub
    · apply Or.inr
      apply Or.inr
      apply Or.inl
      rcases source with ⟨n, member, eqLabel⟩
      refine ⟨n, ?_, eqLabel⟩
      cases pos <;> rcases handler with _ | ⟨handlerVar, body, h1, h2⟩ <;>
        simp_all [getCodeLabelsHOL]

  case case21 =>
    rename_i input pos args dest vs live ret l1 l2 q0 liveProg afterLive liveEq qret afterRet retEq destEq good retIH
    have facts := callDestFacts (width := width) pos args frame
    rw [destEq] at facts
    simp only [getCodeLabels, Set.union_empty, Set.subset_def,
      Set.mem_insert_iff] at facts
    have liveEmpty := wLiveCodeLabels live input frame liveProg afterLive liveEq
    simp only [facts.1, liveEmpty, stackArgsLabels, copyLabels, copyHandlers,
      Set.mem_empty_iff_false, false_implies, forall_const, true_and]
    constructor
    · intro label member
      rcases facts.2 label member with stub | source
      · exact Or.inl stub
      · exact Or.inr (Or.inr (Or.inl (Or.inl source)))
    · intro label member
      rcases retIH label member with stub | store | source | handler
      · exact Or.inl stub
      · exact Or.inr (Or.inl store)
      · exact Or.inr (Or.inr (Or.inl (Or.inr source)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr handler)))))

  case case22 =>
    rename_i input pos args dest vs live ret l1 l2 q0 liveProg afterLive liveEq qret afterRet retEq handlerVar handler h1 h2 qhandler afterHandler handlerEq destEq good retIH handlerIH
    have facts := callDestFacts (width := width) pos args frame
    rw [destEq] at facts
    simp only [getCodeLabels, Set.union_empty, Set.subset_def,
      Set.mem_insert_iff] at facts
    have liveEmpty := wLiveCodeLabels live input frame liveProg afterLive liveEq
    have owned : h1 = owner := by simpa using good.2.1
    simp only [facts.1, liveEmpty, stackHandlerArgsNative, stackArgsLabels, copyLabels,
      copyHandlers, pushLabels, popLabels, popHandlers, owned, if_true,
      Set.mem_empty_iff_false, false_implies, forall_const, true_and, Set.mem_singleton_iff]
    refine ⟨?_, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · intro label member
      tauto
    · intro label member
      have bound := facts.2 label member
      tauto
    · intro label member
      have bound := retIH label member
      tauto
    · intro label member
      have bound := handlerIH label member
      tauto

end Flapjack.Compiler.Backend.WordToStack.Native
