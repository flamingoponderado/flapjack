import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundFlat
import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnRegisterBounds
import Mathlib.Tactic.Tauto

namespace Flapjack.WordToStackProofs.RegisterBoundRecursive
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- Internal destination preparation calculation from the original Call case.
No standalone HOL theorem names this combined prefix/destination bound. -/
theorem callDestBound {width : Nat} [NeZero width]
    (dest : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat) :
    regBound (callDestNative (width := width) dest args frame).1 (frame.1 + 2) ∧
      (match (callDestNative (width := width) dest args frame).2 with
       | .inr r => r < frame.1 + 2 | .inl _ => True) := by
  cases dest with
  | some n => trivial
  | none =>
      simp only [callDestNative]
      split
      · trivial
      · simp only [wReg2]
        split <;> simp only [wStackLoadNative, regBound]
        all_goals repeat' apply And.intro
        all_goals first | trivial | omega

/-- Internal argument frame bound from the original Call proof; movement
uses the accepted full stack_move_reg_bound theorem, with no slot-count guard. -/
theorem stackArgsBound {width : Nat} [NeZero width] {α β : Type}
    (dest : Sum α β) (n : Nat) (frame : Nat × Nat × Nat) :
    regBound (stackArgsNative dest n frame : HolProg width) (frame.1 + 2) := by
  simp only [stackArgsNative]
  exact Flapjack.WordToStackProofs.stackMoveRegBound _ _ _ _ _ _ (by omega) (by trivial)

/-- Internal false-performance handler setup calculation. No separately named
HOL theorem claims this intermediate register-bound result. -/
theorem pushHandlerBound {width : Nat} [NeZero width] {β γ : Type}
    (l1 l2 : Nat) (frame : Nat × β × γ) :
    regBound (pushHandlerNative false l1 l2 frame : HolProg width) (frame.1 + 2) := by
  simp [pushHandlerNative, regBound, regBoundInst]

/-- Internal restoration calculation with the arbitrary original continuation;
there is no separately named HOL declaration for this intermediate. -/
theorem popHandlerBound {width : Nat} [NeZero width] {β γ : Type}
    (frame : Nat × β × γ) (p : HolProg width)
    (h : regBound p (frame.1 + 2)) :
    regBound (popHandlerNative false frame p) (frame.1 + 2) := by
  simp [popHandlerNative, regBound, h]

/-- Full original MustTerminate case, retaining all original inputs and guards;
only genuine proper-subprogram induction hypotheses are added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_reg_bound" (words_as_type_indexed_bitvec)]
theorem wordToStackRegBoundMustTerminate {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (body : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (conventions : postAllocConventionsHOL frame.1 (.mustTerminate body) = true)
    (room : 4 ≤ frame.1) (plain : perf = false)
    (ih : ∀ bs frame, postAllocConventionsHOL frame.1 body = true →
      4 ≤ frame.1 → perf = false → regBound (compNative conf perf body bs frame).1 (frame.1 + 2)) :
    regBound (compNative conf perf (.mustTerminate body) bs frame).1 (frame.1 + 2) := by
  have bodyConv : postAllocConventionsHOL frame.1 body = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    tauto
  simpa only [compNative, regBound] using ih bs frame bodyConv room plain

/-- Full original Loop case, retaining all original inputs and guards;
only genuine proper-subprogram induction hypotheses are added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_reg_bound" (words_as_type_indexed_bitvec)]
theorem wordToStackRegBoundLoop {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (liveIn liveOut : WordLangNumSetHOL)
    (body : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (conventions : postAllocConventionsHOL frame.1 (.loop liveIn body liveOut) = true)
    (room : 4 ≤ frame.1) (plain : perf = false)
    (ih : ∀ bs frame, postAllocConventionsHOL frame.1 body = true →
      4 ≤ frame.1 → perf = false → regBound (compNative conf perf body bs frame).1 (frame.1 + 2)) :
    regBound (compNative conf perf (.loop liveIn body liveOut) bs frame).1 (frame.1 + 2) := by
  have bodyConv : postAllocConventionsHOL frame.1 body = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    tauto
  simpa only [compNative, regBound] using ih bs frame bodyConv room plain

/-- Full original Seq case, retaining all original inputs and guards;
only genuine proper-subprogram induction hypotheses are added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_reg_bound" (words_as_type_indexed_bitvec)]
theorem wordToStackRegBoundSeq {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (first second : WordLangProgHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (conventions : postAllocConventionsHOL frame.1 (.seq first second) = true)
    (room : 4 ≤ frame.1) (plain : perf = false)
    (ih1 : ∀ bs frame, postAllocConventionsHOL frame.1 first = true →
      4 ≤ frame.1 → perf = false → regBound (compNative conf perf first bs frame).1 (frame.1 + 2))
    (ih2 : ∀ bs frame, postAllocConventionsHOL frame.1 second = true →
      4 ≤ frame.1 → perf = false → regBound (compNative conf perf second bs frame).1 (frame.1 + 2)) :
    regBound (compNative conf perf (.seq first second) bs frame).1 (frame.1 + 2) := by
  have firstConv : postAllocConventionsHOL frame.1 first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    tauto
  have secondConv : postAllocConventionsHOL frame.1 second = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    tauto
  have h1 := ih1 bs frame firstConv room plain
  have h2 := ih2 (compNative conf perf first bs frame).2 frame secondConv room plain
  simpa only [compNative, regBound] using And.intro h1 h2

/-- Full original If case, retaining all original inputs and guards;
only genuine proper-subprogram induction hypotheses are added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_reg_bound" (words_as_type_indexed_bitvec)]
theorem wordToStackRegBoundIf {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (cmp : Cmp) (reg : Nat)
    (ri : WordRegImm (BitVec width)) (first second : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (conventions : postAllocConventionsHOL frame.1 (.ite cmp reg ri first second) = true)
    (room : 4 ≤ frame.1) (plain : perf = false)
    (ih1 : ∀ bs frame, postAllocConventionsHOL frame.1 first = true →
      4 ≤ frame.1 → perf = false → regBound (compNative conf perf first bs frame).1 (frame.1 + 2))
    (ih2 : ∀ bs frame, postAllocConventionsHOL frame.1 second = true →
      4 ≤ frame.1 → perf = false → regBound (compNative conf perf second bs frame).1 (frame.1 + 2)) :
    regBound (compNative conf perf (.ite cmp reg ri first second) bs frame).1 (frame.1 + 2) := by
  have firstConv : postAllocConventionsHOL frame.1 first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    tauto
  have secondConv : postAllocConventionsHOL frame.1 second = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    tauto
  have h1 := ih1 bs frame firstConv room plain
  have h2 := ih2 (compNative conf perf first bs frame).2 frame secondConv room plain
  cases ri
  all_goals simp only [compNative, wReg1, wReg2]
  all_goals try split_ifs
  all_goals simp only [wStackLoadNative, List.append_nil, List.nil_append, List.cons_append, regBound, regBoundInst]
  all_goals repeat' apply And.intro
  all_goals first | exact h1 | exact h2 | trivial | omega

/-- Full original CallTail case, retaining all original inputs and guards;
only genuine proper-subprogram induction hypotheses are added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_reg_bound" (words_as_type_indexed_bitvec)]
theorem wordToStackRegBoundCallTail {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (_conventions : postAllocConventionsHOL frame.1 (.call none dest args handler) = true)
    (_room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf (.call none dest args handler) bs frame).1 (frame.1 + 2) := by
  subst perf
  have hd := callDestBound (width := width) dest args frame
  simp only [compNative, regBound, seqStackFreeNative]
  split <;> simp_all [regBound]
  all_goals exact hd.2

/-- Full original CallReturn case, retaining all original inputs and guards;
only genuine proper-subprogram induction hypotheses are added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_reg_bound" (words_as_type_indexed_bitvec)]
theorem wordToStackRegBoundCallReturn {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (values : List Nat)
    (live : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (conventions : postAllocConventionsHOL frame.1 (.call (some (values,live,retCode,l1,l2)) dest args none) = true)
    (room : 4 ≤ frame.1) (plain : perf = false)
    (ih : ∀ bs frame, postAllocConventionsHOL frame.1 retCode = true →
      4 ≤ frame.1 → perf = false → regBound (compNative conf perf retCode bs frame).1 (frame.1 + 2)) :
    regBound (compNative conf perf (.call (some (values,live,retCode,l1,l2)) dest args none) bs frame).1 (frame.1 + 2) := by
  have retCodeConv : postAllocConventionsHOL frame.1 retCode = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    tauto
  subst perf
  have hd := callDestBound (width := width) dest args frame
  have retSafe := ih (wLiveNative live bs frame).2 frame retCodeConv room rfl
  simp only [compNative, regBound]
  repeat' apply And.intro
  all_goals first
    | exact hd.1
    | exact hd.2
    | exact Flapjack.WordToStackProofs.RegisterBoundFlat.liveBound _ _ _
    | exact stackArgsBound _ _ _
    | exact pushHandlerBound _ _ _
    | trivial
    | simp
    | omega
    | apply Flapjack.WordToStackProofs.copyRetRegBound
      exact retSafe

/-- Full original CallHandler case, retaining all original inputs and guards;
only genuine proper-subprogram induction hypotheses are added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_reg_bound" (words_as_type_indexed_bitvec)]
theorem wordToStackRegBoundCallHandler {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (values : List Nat)
    (live : WordLangCutsetsHOL) (retCode handleCode : WordLangProgHOL (BitVec width))
    (l1 l2 handleValue h1 h2 : Nat) (dest : Option Nat) (args : List Nat)
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (conventions : postAllocConventionsHOL frame.1 (.call (some (values,live,retCode,l1,l2)) dest args (some (handleValue,handleCode,h1,h2))) = true)
    (room : 4 ≤ frame.1) (plain : perf = false)
    (ih1 : ∀ bs frame, postAllocConventionsHOL frame.1 retCode = true →
      4 ≤ frame.1 → perf = false → regBound (compNative conf perf retCode bs frame).1 (frame.1 + 2))
    (ih2 : ∀ bs frame, postAllocConventionsHOL frame.1 handleCode = true →
      4 ≤ frame.1 → perf = false → regBound (compNative conf perf handleCode bs frame).1 (frame.1 + 2)) :
    regBound (compNative conf perf
      (.call (some (values,live,retCode,l1,l2)) dest args
        (some (handleValue,handleCode,h1,h2))) bs frame).1 (frame.1 + 2) := by
  have retCodeConv : postAllocConventionsHOL frame.1 retCode = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    tauto
  have handleCodeConv : postAllocConventionsHOL frame.1 handleCode = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    tauto
  subst perf
  have hd := callDestBound (width := width) dest args frame
  have retSafe := ih1 (wLiveNative live bs frame).2 frame retCodeConv room rfl
  have handlerSafe := ih2 (compNative conf false retCode (wLiveNative live bs frame).2 frame).2 frame handleCodeConv room rfl
  simp only [compNative, regBound]
  repeat' apply And.intro
  all_goals try simp only [regBound, regBoundInst]
  all_goals first
    | exact hd.1
    | exact hd.2
    | exact Flapjack.WordToStackProofs.RegisterBoundFlat.liveBound _ _ _
    | exact stackArgsBound _ _ _
    | exact pushHandlerBound _ _ _
    | exact handlerSafe
    | trivial
    | simp
    | omega
    | apply Flapjack.WordToStackProofs.copyRetRegBound
      first | exact retSafe | exact popHandlerBound _ _ retSafe

end Flapjack.WordToStackProofs.RegisterBoundRecursive
