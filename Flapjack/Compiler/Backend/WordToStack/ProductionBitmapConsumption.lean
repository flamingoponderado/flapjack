import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapWritePair
import Flapjack.Compiler.Backend.WordRemove.Production

/-! Flapjack caller invariants across the executed native MustTerminate removal.
These are structural carrier consequences, not HOL semantic theorem ports.
Actual writer-traversal discharge remains separate from the cleanup invariant. -/
namespace Flapjack.ProductionBitmapConsumption
open Compiler.Backend ProductionGcCutsets RiscV RiscV.CakeRegAlloc

/-- Native removal preserves every original stack-cutset predicate, including
both cutsets, both returning Call bodies, FFI/Install and tail-handler erasure. -/
theorem everyStack_remove {width : Nat} [NeZero width] (predicate : Nat → Bool) :
    ∀ program : WordLangProgHOL (BitVec width),
      everyStackVarHOL predicate (WordRemove.removeMustTerminate program) =
        everyStackVarHOL predicate program
  | .mustTerminate body => by
      simpa only [WordRemove.removeMustTerminate, everyStackVarHOL] using
        everyStack_remove predicate body
  | .seq first second => by
      simp only [WordRemove.removeMustTerminate, everyStackVarHOL,
        everyStack_remove predicate first, everyStack_remove predicate second]
  | .ite op condition right first second => by
      simp only [WordRemove.removeMustTerminate, everyStackVarHOL,
        everyStack_remove predicate first, everyStack_remove predicate second]
  | .loop before body after => by
      simpa only [WordRemove.removeMustTerminate, everyStackVarHOL] using
        everyStack_remove predicate body
  | .call returns target arguments handler => by
      rcases returns with _ | ⟨values, sets, body, l1, l2⟩
      · rcases handler with _ | ⟨exception, hbody, h1, h2⟩ <;>
          simp [WordRemove.removeMustTerminate, everyStackVarHOL]
      · rcases handler with _ | ⟨exception, hbody, h1, h2⟩ <;>
          simp [WordRemove.removeMustTerminate, everyStackVarHOL,
            everyStack_remove predicate body]
        exact congrArg _ (everyStack_remove predicate hbody)
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .set _ _ |
      .store _ _ | .alloc _ _ | .storeConsts _ _ _ _ _ | .raise _ |
      .return _ _ | .break _ | .continue _ | .tick | .opCurrHeap _ _ _ |
      .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _ |
      .dataBufferWrite _ _ | .ffi _ _ _ _ _ _ | .shareInst _ _ _ => by rfl

/-- Every stack-cutset name in an accepted codec input belongs to the original
production read domain. This checks both cutsets and all returning subtrees. -/
theorem inputStack_readDomain {width : Nat} [NeZero width]
    (predicate : Nat → Bool) (source : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (checked : ∀ name ∈ wordProgReadVars source, predicate name = true) :
    everyStackVarHOL predicate native = true := by
  cases source <;>
    try simp only [wordLangProgToHOL, bind, pure,
      Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq] at encoded
  all_goals try (subst native; rfl)
  all_goals try simp only [wordProgReadVars, List.mem_append, List.mem_cons] at checked
  case inst instruction =>
    obtain ⟨instruction, _, rfl⟩ := encoded
    rfl
  case seq first second =>
    obtain ⟨left, hl, right, hr, rfl⟩ := encoded
    simp only [everyStackVarHOL, Bool.and_eq_true]
    exact ⟨inputStack_readDomain predicate first left hl (fun n hn => checked n (Or.inl hn)),
      inputStack_readDomain predicate second right hr (fun n hn => checked n (Or.inr hn))⟩
  case ite op condition right first second =>
    obtain ⟨left, hl, right, hr, rfl⟩ := encoded
    simp only [everyStackVarHOL, Bool.and_eq_true]
    exact ⟨inputStack_readDomain predicate first left hl (fun n hn => checked n (Or.inl (Or.inr hn))),
      inputStack_readDomain predicate second right hr (fun n hn => checked n (Or.inr hn))⟩
  case loop before body after =>
    obtain ⟨bodyNative, hb, rfl⟩ := encoded
    exact inputStack_readDomain predicate body bodyNative hb (fun n hn => checked n (Or.inl (Or.inr hn)))
  case mustTerminate body =>
    obtain ⟨bodyNative, hb, rfl⟩ := encoded
    exact inputStack_readDomain predicate body bodyNative hb checked
  case call returns target arguments handler =>
    generalize hreturns : returns = returnsNew at *
    rcases hretParts : returnsNew with _ | ⟨values, ⟨other, live⟩, body, l1, l2⟩
    · generalize hhandler : handler = handlerNew at *
      rcases hhandlerParts : handlerNew with _ | ⟨exception, hbody, h1, h2⟩
      all_goals rw [hretParts, hhandlerParts] at encoded checked
      all_goals simp only [wordLangProgToHOL, bind, pure, Option.bind_some,
          Option.bind_eq_some_iff, Option.some.injEq] at encoded
      · cases encoded; rfl
      · obtain ⟨_, _, rfl⟩ := encoded; rfl
    · have returnBound : sizeOf body < sizeOf returns := by
        rw [hreturns, hretParts]
        simp
        omega
      generalize hhandler : handler = handlerNew at *
      rcases hhandlerParts : handlerNew with _ | ⟨exception, hbody, h1, h2⟩
      all_goals rw [hretParts, hhandlerParts] at encoded checked
      all_goals simp only [wordLangProgToHOL, bind, pure, Option.bind_some,
        Option.bind_eq_some_iff, Option.some.injEq] at encoded
      all_goals simp only [wordProgReadVars, List.mem_append] at checked
      · obtain ⟨ret, hr, rfl⟩ := encoded
        simp only [everyStackVarHOL, everyNameHOL, wordCutsetsToHOL,
          Bool.and_eq_true, List.all_eq_true, sptMemMapFstToAList,
          LoopToWord.sptDomain_toNumSetHOL]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, True.intro⟩
        · intro n hn; exact checked n (Or.inl (Or.inr (Or.inl (Or.inl hn))))
        · intro n hn; exact checked n (Or.inl (Or.inr (Or.inl (Or.inr hn))))
        · exact inputStack_readDomain predicate body ret hr (fun n hn => checked n (Or.inl (Or.inr (Or.inr hn))))
      · have handlerBound : sizeOf hbody < sizeOf handler := by
          rw [hhandler, hhandlerParts]
          simp
          omega
        obtain ⟨ret, hr, hret, hh, rfl⟩ := encoded
        simp only [everyStackVarHOL, everyNameHOL, wordCutsetsToHOL,
          Bool.and_eq_true, List.all_eq_true, sptMemMapFstToAList,
          LoopToWord.sptDomain_toNumSetHOL]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · intro n hn; exact checked n (Or.inl (Or.inr (Or.inl (Or.inl hn))))
        · intro n hn; exact checked n (Or.inl (Or.inr (Or.inl (Or.inr hn))))
        · exact inputStack_readDomain predicate body ret hr (fun n hn => checked n (Or.inl (Or.inr (Or.inr hn))))
        · exact inputStack_readDomain predicate hbody hret hh (fun n hn => checked n (Or.inr hn))
  all_goals subst native
  all_goals simp only [everyStackVarHOL, everyNameHOL, wordCutsetsToHOL,
    Bool.and_eq_true, List.all_eq_true, sptMemMapFstToAList,
    LoopToWord.sptDomain_toNumSetHOL]
  all_goals constructor <;> intro n hn <;> apply checked <;> tauto
termination_by sizeOf source
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals simp only [Option.some.sizeOf_spec] at *
  all_goals omega

/-- The actual successful cleanup/codec result supplies each selected post-remove
GC predicate from the checked input predicate. No desired output predicate is
assumed; encoding normalization is discharged by its existing universal law. -/
theorem selectedAfterRemove {width : Nat} [NeZero width]
    (source result : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (removed : RiscV.wordRemoveMustTerminateViaHOL? source = some result)
    (predicate : Nat → Bool) (checked : everyStackVarHOL predicate native = true)
    (name : Nat) (selected : GcName name result) : predicate name = true := by
  obtain ⟨input, inputCodec, decoded⟩ := RiscV.wordRemoveMustTerminateViaHOL?_native
    source result removed
  rw [encoded] at inputCodec
  cases Option.some.inj inputCodec
  have resultCodec := wordLangProgToHOL_of_fromHOL
    (WordRemove.removeMustTerminate native) result decoded
  apply selected.stackPredicate _ resultCodec predicate
  rw [everyStackVarHOL_normalizeCutsets,
    everyStack_remove]
  exact checked

/-- Actual post-remove GC names inherit the original stack-variable guard from
the allocator's input conventions, not from a final-colour assumption. -/
theorem selectedAfterRemove_stack {width : Nat} [NeZero width]
    (source result : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (removed : RiscV.wordRemoveMustTerminateViaHOL? source = some result)
    (pre : preAllocConventionsHOL native = true)
    (name : Nat) (selected : GcName name result) : isStackVar name = true := by
  simp only [preAllocConventionsHOL, Bool.and_eq_true] at pre
  exact selectedAfterRemove source result native encoded removed isStackVar pre.1 name selected

/-- Actual post-remove GC names belong to the original allocator input's clash
tree; the universal input occurrence theorem supplies this predicate outright. -/
theorem selectedAfterRemove_clash {width : Nat} [NeZero width]
    (source result : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (removed : RiscV.wordRemoveMustTerminateViaHOL? source = some result)
    (name : Nat) (selected : GcName name result) :
    RegAlloc.inClashTree (WordAlloc.getClashTree native []) name := by
  classical
  have everyName := WordAlloc.everyVar_inGetClashTree native []
  have checked := everyVar_stackSubset _ native everyName
  exact of_decide_eq_true
    (selectedAfterRemove source result native encoded removed _ checked name selected)

/-- Names selected by the executed post-remove writer remain in the original
production read domain, despite cutset enumeration normalization. -/
theorem selectedAfterRemove_reads {width : Nat} [NeZero width]
    (source result : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (removed : RiscV.wordRemoveMustTerminateViaHOL? source = some result)
    (name : Nat) (selected : GcName name result) : name ∈ wordProgReadVars source := by
  classical
  have checked := inputStack_readDomain (fun n => decide (n ∈ wordProgReadVars source))
    source native encoded (fun n hn => decide_eq_true hn)
  exact of_decide_eq_true
    (selectedAfterRemove source result native encoded removed _ checked name selected)

/-- The actual cleanup result discharges all three bitmap-placement input
obligations together, using only original input conventions and the real codec
and cleanup branches. No selected-name membership callback is assumed. -/
theorem selectedAfterRemove_allocatorDomain {width : Nat} [NeZero width]
    (parameters : List Nat) (source result : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL source = some native)
    (removed : RiscV.wordRemoveMustTerminateViaHOL? source = some result)
    (pre : preAllocConventionsHOL native = true)
    (name : Nat) (selected : GcName name result) :
    name ∈ parameters ++ wordProgVariables source ∧
      RegAlloc.inClashTree (WordAlloc.getClashTree native []) name ∧
      isStackVar name = true := by
  refine ⟨?_, selectedAfterRemove_clash source result native encoded removed name selected,
    selectedAfterRemove_stack source result native encoded removed pre name selected⟩
  simp only [List.mem_append, wordProgVariables]
  exact Or.inr (Or.inl (selectedAfterRemove_reads source result native encoded removed name selected))

/-- The retained allocator's real post-remove GC consumer produces the exact
source bitmap. Selection refers to the executed cleanup result; original-domain,
stack and clash obligations are all derived internally. -/
theorem retainedAfterRemove_liveBitmap {width : Nat} [NeZero width]
    (copy dead : WordProg (BitVec width) → WordProg (BitVec width))
    (unreach : WordProg (BitVec width) → Option (WordProg (BitVec width)))
    (ssa : Nat → WordProg (BitVec width) → Option (WordSsaState × List Nat × WordProg (BitVec width)))
    (label : Nat) (parameters : List Nat) (source : WordProg (BitVec width))
    (output : RiscV.CakeRegAlloc.CakeAllocationWithColour (BitVec width))
    (produced : RiscV.CakeRegAlloc.cakeAllocateWordFunctionAfterDeadWithColourWithSsaAndCopy
      copy dead unreach ssa label parameters source = some output)
    (input : ProductionCleanupConventions.NativeInput output.program)
    (result : WordProg (BitVec width))
    (removed : RiscV.wordRemoveMustTerminateViaHOL? output.program = some result)
    (config : Compiler.Encoders.Asm.AsmConfigExact width) (target : config.isa = .riscv)
    (live : List Nat) (consumed : ∀ name ∈ live, GcName name result) :
    let slots := (RiscV.CakeRegAlloc.cakeColourFrameSlots
      cakeRiscVRegisterCount parameters output.program output.colouring).1
    RiscV.wordStackLiveBitmapFromLocations
      (RiscV.sourceWordStackConfig label output.allocation slots) slots width live =
      CakeAlloc.writeBitmap (live.map (CakeAlloc.totalColour output.colouring))
        cakeRiscVRegisterCount slots width := by
  obtain ⟨native, encoded, pre, _⟩ := input.encoded output.program
  obtain ⟨spill, allocator⟩ := allocatorWithCopy_retained
    copy dead unreach ssa label parameters source output produced
  dsimp only
  rw [spill]
  exact ProductionBitmapTransport.sourceAllocator_liveBitmap output.program native encoded config target
    .IRC (wordGetHeuristics 3 label output.program).2 cakeRiscVRegisterCount
    ((wordGetHeuristics 3 label output.program).1.map
      (fun move => (move.priority, (move.left, move.right)))) output.colouring
    (by simpa only [RegAlloc.Algorithm.toProduction] using allocator) label parameters live
    (fun name member => (selectedAfterRemove_allocatorDomain parameters output.program result native
      encoded removed pre name (consumed name member)).1)
    (fun name member => (selectedAfterRemove_allocatorDomain parameters output.program result native
      encoded removed pre name (consumed name member)).2.1)
    (fun name member => (selectedAfterRemove_allocatorDomain parameters output.program result native
      encoded removed pre name (consumed name member)).2.2)

end Flapjack.ProductionBitmapConsumption
