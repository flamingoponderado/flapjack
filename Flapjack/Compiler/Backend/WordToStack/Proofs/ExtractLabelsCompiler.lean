import Flapjack.Compiler.Backend.WordToStack.Proofs.ExtractLabelsHelpers
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Pancake.WordConvs

namespace Flapjack.Compiler.Backend.WordToStack.Native.ExtractLabelsCompiler
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open ExtractLabelsHelpers

/- Private untagged equations organize the native syntax proof; there are no
independently named HOL originals for these stronger helper interfaces. -/
private theorem moveSingleLabels {width : Nat} [NeZero width]
    (xy : Sum Nat Nat × Sum Nat Nat) (frame : Nat × Nat × Nat) :
    StackProps.extractLabels (wMoveSingleNative (width := width) xy frame) = [] := by
  rcases xy with ⟨x,y⟩
  cases x <;> cases y <;> simp [wMoveSingleNative, StackProps.extractLabels]

private theorem moveAuxLabels {width : Nat} [NeZero width]
    (moves : List (Sum Nat Nat × Sum Nat Nat)) (frame : Nat × Nat × Nat) :
    StackProps.extractLabels (wMoveAuxNative (width := width) moves frame) = [] := by
  induction moves with
  | nil => simp only [wMoveAuxNative, StackProps.extractLabels]
  | cons xy rest ih =>
    cases rest with
    | nil => exact moveSingleLabels xy frame
    | cons next tail => simp only [wMoveAuxNative, StackProps.extractLabels,
        moveSingleLabels, ih, List.nil_append]

private theorem moveLabels {width : Nat} [NeZero width]
    (moves : List (Nat × Nat)) (frame : Nat × Nat × Nat) :
    StackProps.extractLabels (wMoveNative (width := width) moves frame) = [] :=
  moveAuxLabels _ frame

private theorem write1Labels {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat)
    (labels : List (Nat × Nat)) (h : ∀ n, StackProps.extractLabels (g n) = labels) :
    StackProps.extractLabels (wRegWrite1Native g r frame) = labels := by
  simp only [wRegWrite1Native]
  split <;> simp [StackProps.extractLabels, h]

private theorem write2Labels {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat)
    (labels : List (Nat × Nat)) (h : ∀ n, StackProps.extractLabels (g n) = labels) :
    StackProps.extractLabels (wRegWrite2Native g r frame) = labels := by
  simp only [wRegWrite2Native]
  split <;> simp [StackProps.extractLabels, h]

private theorem write1Equation {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat) :
    StackProps.extractLabels (wRegWrite1Native g r frame) =
      if r / 2 < frame.1 then StackProps.extractLabels (g (r / 2))
      else StackProps.extractLabels (g frame.1) := by
  simp only [wRegWrite1Native]
  split <;> simp [StackProps.extractLabels]

private theorem shareLabels {width : Nat} [NeZero width]
    (op : HolMemop) (r : Nat) (address : HolAddr width) (frame : Nat × Nat × Nat) :
    StackProps.extractLabels (wShareInstNative op r address frame) = [] := by
  cases address
  cases op <;> simp [wShareInstNative, stackLoadLabels, write1Equation, StackProps.extractLabels]

private theorem instLabels {width : Nat} [NeZero width]
    (i : HolInst width) (frame : Nat × Nat × Nat) :
    StackProps.extractLabels (wInstNative i frame) = [] := by
  unfold wInstNative
  split
  all_goals try split
  all_goals try simp only [*]
  all_goals try simp only [stackLoadLabels]
  all_goals first
    | exact write1Labels _ _ _ [] (fun _ => by simp only [StackProps.extractLabels])
    | exact write2Labels _ _ _ [] (fun _ => write1Labels _ _ _ [] (fun _ => by simp only [StackProps.extractLabels]))
    | simp only [StackProps.extractLabels]

private theorem freeLabels {width : Nat} [NeZero width]
    (slots : Nat) (p : HolProg width) :
    StackProps.extractLabels (seqStackFreeNative slots p) = StackProps.extractLabels p := by
  by_cases h : slots = 0 <;> simp [seqStackFreeNative, h, StackProps.extractLabels]

private theorem liveLabels {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) :
    StackProps.extractLabels (wLiveNative live bs frame).1 = [] := by
  by_cases h : frame.2.1 = 0 <;> simp [wLiveNative, h, StackProps.extractLabels]

private theorem destLabels {width : Nat} [NeZero width]
    (dest : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat) :
    StackProps.extractLabels (callDestNative (width := width) dest args frame).1 = [] := by
  cases dest with
  | some _ => simp only [callDestNative, StackProps.extractLabels]
  | none =>
    by_cases h : args.length = 0
    · simp [callDestNative, h, StackProps.extractLabels]
    · simp [callDestNative, h, stackLoadLabels, StackProps.extractLabels]

private theorem pushLabels {width : Nat} [NeZero width] {β γ : Type}
    (perf : Bool) (l1 l2 : Nat) (frame : Nat × β × γ) :
    StackProps.extractLabels (pushHandlerNative (width := width) perf l1 l2 frame) = [] := by
  cases perf <;> simp [pushHandlerNative, listSeq, StackProps.extractLabels]

private theorem perfPrefixLabels {width : Nat} [NeZero width]
    (perf : Bool) (l1 l2 k : Nat) :
    StackProps.extractLabels (if perf then perfCallPrefixNative (width := width) l1 l2 k else .skip) = [] := by
  cases perf <;> simp [perfCallPrefixNative, listSeq, StackProps.extractLabels]

private theorem perfSuffixLabels {width : Nat} [NeZero width] (perf : Bool) :
    StackProps.extractLabels (if perf then perfCallSuffixNative (width := width) else .skip) = [] := by
  cases perf <;> simp [perfCallSuffixNative, listSeq, StackProps.extractLabels]

private theorem liveResultLabels {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (q : HolProg width) (rest : AppList (BitVec width) × Nat)
    (eq : wLiveNative live bs frame = (q,rest)) : StackProps.extractLabels q = [] := by
  have h := liveLabels live bs frame
  simpa only [eq] using h

private theorem destResultLabels {width : Nat} [NeZero width]
    (dest : Option Nat) (args : List Nat) (frame : Nat × Nat × Nat)
    (q : HolProg width) (target : Sum Nat Nat)
    (eq : callDestNative dest args frame = (q,target)) : StackProps.extractLabels q = [] := by
  have h := destLabels (width := width) dest args frame
  simpa only [eq] using h

/-- Complete original all-program ordered-label equality. Only the standard
positive word translation is qualified; all compiler inputs are arbitrary.
Recursion uses proper source subprograms and actual residual bitmaps. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_lab_pres" (words_as_type_indexed_bitvec)]
theorem wordToStackLabPres {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (p : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) :
    Flapjack.extractLabels p = StackProps.extractLabels (compNative conf perf p bs frame).1 := by
  apply compNative.induct conf perf frame
    (motive := fun p bs => Flapjack.extractLabels p =
      StackProps.extractLabels (compNative conf perf p bs frame).1)
  all_goals intros
  all_goals try
    have liveEmpty := liveResultLabels (width := width) _ _ frame _ _ (by assumption)
  all_goals try
    have destEmpty := destResultLabels (width := width) _ _ frame _ _ (by assumption)
  all_goals simp_all only [compNative, Flapjack.extractLabels, StackProps.extractLabels,
    moveLabels, instLabels, freeLabels, stackLoadLabels, write1Equation, shareLabels,
    copyRetLabels, stackArgsNative, stackHandlerArgsNative, stackMoveLabels,
    popHandlerNative, pushLabels, perfPrefixLabels, perfSuffixLabels,
    List.nil_append, List.append_nil]
  all_goals simp_all [StackProps.extractLabels, stackLoadLabels]


/- The following untagged projection equations are stronger proof infrastructure,
not independently named HOL ports. They retain each complete ordered label list. -/
private theorem compileProgLabels {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (p : WordLangProgHOL (BitVec width))
    (argc k : Nat) (bs : AppList (BitVec width) × Nat) :
    StackProps.extractLabels (compileProgNative conf perf p argc k bs).1 =
      Flapjack.extractLabels p := by
  simp [compileProgNative, StackProps.extractLabels, ← wordToStackLabPres]

private theorem compileListLabels {width : Nat} [NeZero width] {β : Type}
    (conf : AsmConfigExact width) (perf : Bool) (k : Nat)
    (rows : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat) :
    (compileWordToStackNative conf perf k rows bs).1.map
        (fun row => (row.1, StackProps.extractLabels row.2)) =
      rows.map (fun row => (row.1, Flapjack.extractLabels row.2.2)) := by
  induction rows generalizing bs with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨id,argc,p⟩
    simp [compileWordToStackNative, ih, compileProgLabels]

/-- Full original program-list label-preservation theorem. The compilation
result equation aliases the actual complete output, including frames and bitmaps.
The only source guard is the original ordered-label ownership/distinctness guard. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "compile_word_to_stack_lab_pres" (words_as_type_indexed_bitvec)]
theorem compileWordToStackLabPres {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (k : Nat)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bs : AppList (BitVec width) × Nat) (output : List (Nat × HolProg width))
    (rest : List Nat × (AppList (BitVec width) × Nat))
    (eq : compileWordToStackNative conf perf k rows bs = (output,rest))
    (source : ∀ row ∈ rows,
      (∀ label ∈ Flapjack.extractLabels row.2.2,
        label.1 = row.1 ∧ label.2 ≠ 0 ∧ label.2 ≠ 1) ∧
      (Flapjack.extractLabels row.2.2).Nodup) :
    ∀ row ∈ output,
      (∀ label ∈ StackProps.extractLabels row.2,
        label.1 = row.1 ∧ label.2 ≠ 0 ∧ label.2 ≠ 1) ∧
      (StackProps.extractLabels row.2).Nodup := by
  intro row member
  have projected := compileListLabels conf perf k rows bs
  rw [eq] at projected
  have mapped : (row.1, StackProps.extractLabels row.2) ∈
      output.map (fun row => (row.1, StackProps.extractLabels row.2)) :=
    List.mem_map.mpr ⟨row,member,rfl⟩
  rw [projected] at mapped
  obtain ⟨input,inRows,same⟩ := List.mem_map.mp mapped
  have keyEq := congrArg Prod.fst same
  have labelEq := congrArg Prod.snd same
  change input.1 = row.1 at keyEq
  change Flapjack.extractLabels input.2.2 = StackProps.extractLabels row.2 at labelEq
  simpa only [keyEq, labelEq] using source input inRows

/-- Full original top-level key and ordered-label result, over actual native
compilation including both complete stubs. Only the original source label guard
is assumed; no target property or successful result is supplied. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_compile_lab_pres" (words_as_type_indexed_bitvec)]
theorem wordToStackCompileLabPres {width : Nat} [NeZero width]
    (conf : AsmConfigExact width)
    (rows : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (source : ∀ row ∈ rows,
      (∀ label ∈ Flapjack.extractLabels row.2.2,
        label.1 = row.1 ∧ label.2 ≠ 0 ∧ label.2 ≠ 1) ∧
      (Flapjack.extractLabels row.2.2).Nodup) :
    let output := (compileNative conf false rows).2.2.2
    output.map Prod.fst = raiseStubLocation :: storeConstsStubLocation :: rows.map Prod.fst ∧
    ∀ row ∈ output,
      (∀ label ∈ StackProps.extractLabels row.2,
        label.1 = row.1 ∧ label.2 ≠ 0 ∧ label.2 ≠ 1) ∧
      (StackProps.extractLabels row.2).Nodup := by
  have projected := compileListLabels conf false
    (conf.regCount - (5 + conf.avoidRegs.length)) rows (.list [4],1)
  have keys := congrArg (List.map Prod.fst) projected
  simp only [List.map_map, Function.comp_def] at keys
  have safe := compileWordToStackLabPres conf false
    (conf.regCount - (5 + conf.avoidRegs.length)) rows (.list [4],1)
    (compileWordToStackNative conf false
      (conf.regCount - (5 + conf.avoidRegs.length)) rows (.list [4],1)).1
    (compileWordToStackNative conf false
      (conf.regCount - (5 + conf.avoidRegs.length)) rows (.list [4],1)).2 rfl source
  simp only [compileNative, List.map_cons]
  refine ⟨?_, ?_⟩
  · simpa using keys
  · intro row member
    simp only [List.mem_cons] at member
    rcases member with rfl | rfl | member
    · simp [raiseStubNative, StackProps.extractLabels]
    · simp [storeConstsStubNative, StackProps.extractLabels]
    · exact safe row member

end Flapjack.Compiler.Backend.WordToStack.Native.ExtractLabelsCompiler
