import Flapjack.Compiler.Backend.WordAlloc.ProductionSSAStateRoute
import Flapjack.RiscV.AllocatorCorrectness
import Flapjack.RiscV.LocValue

/-!
Semantic facts for the SSA-renaming stage of the Word allocator.

The CakeML reference renames every read through the current SSA map while
leaving a store's state and fresh-name counter unchanged.  This file starts
the corresponding executable proof boundary; subsequent instruction cases can
be added without unfolding the graph allocator.
-/

namespace Flapjack.RiscV

open Flapjack

theorem wordSsaRenameInst_store {width : Nat}
    (ssa : WordSsaState) (source address : Nat) :
    wordSsaRenameInst ssa (.mem .store source address : WordInst (Word width)) =
      (ssa, .mem .store (wordSsaRead ssa source) (wordSsaRead ssa address)) := by
  rfl

theorem wordSsaRead_fresh_name (state : WordSsaState) (name : Nat) :
    wordSsaRead (wordSsaFresh state name).1 name = state.next := by
  simp only [wordSsaRead,wordSsaFresh,
    Compiler.Backend.WordAlloc.ssaNextVarRenameExecutable,
    Compiler.Backend.WordAlloc.nextVarRename]
  rw [Compiler.Backend.WordAlloc.productionSsaDecodedLookup,sptLookup_sptInsert_same]

theorem wordSsaRead_fresh_of_ne (state : WordSsaState) (name other : Nat)
    (hneq : other ≠ name) :
    wordSsaRead (wordSsaFresh state name).1 other = wordSsaRead state other := by
  simp only [wordSsaRead,wordSsaFresh,
    Compiler.Backend.WordAlloc.ssaNextVarRenameExecutable,
    Compiler.Backend.WordAlloc.nextVarRename]
  rw [Compiler.Backend.WordAlloc.productionSsaDecodedLookup,
    sptLookup_sptInsert_ne name other state.next _ hneq,sptLookup_sptFromAList,
    ← Compiler.Backend.WordAlloc.productionMergeMapLookup]

theorem wordSsaRenameInst_load {width : Nat}
    (ssa : WordSsaState) (destination address : Nat) :
    wordSsaRenameInst ssa (.mem .load destination address : WordInst (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .mem .load (wordSsaFresh ssa destination).2
          (wordSsaRead ssa address)) := by
  rfl

theorem wordSsaRenameProgram_locValue [OfNat α 0]
    (ssa : WordSsaState) (destination label : Nat) :
    wordSsaRenameProgram ssa (.locValue destination label : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .locValue (wordSsaFresh ssa destination).2 label) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops]

theorem wordSsaRenameProgram_assign_var [OfNat α 0]
    (ssa : WordSsaState) (destination source : Nat) :
    wordSsaRenameProgram ssa
        (.assign destination (.var source) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.var (wordSsaRead ssa source))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

/-- Cake Move namespace equation for a singleton move. -/
theorem wordSsaRenameProgram_move_one [OfNat α 0]
    (ssa : WordSsaState) (priority source destination : Nat) :
    wordSsaRenameProgram ssa
        (.move priority [(destination, source)] : WordProg α) =
      let (freshState, fresh) := wordSsaFresh ssa destination
      let finalState :=
        if source = destination then freshState
        else wordSsaForceRename [(source, fresh)] freshState
      (finalState,
        .move priority
          [(fresh, if priority == 0 then wordSsaReadMoveSource ssa source
            else wordSsaRead ssa source)]) := by
  by_cases hsource : source = destination
  · subst source
    simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
      wordSsaRenameMove, wordSsaFreshList, wordSsaForceRename,
      wordSsaFresh, Compiler.Backend.WordAlloc.ssaNextVarRenameExecutable,
      Compiler.Backend.WordAlloc.nextVarRename, Compiler.Backend.WordAlloc.ssaForceRenameExecutable,
      Compiler.Backend.WordAlloc.forceRename, sptToAListFromAListToAList,
      wordSsaReadMoveSource]
  · simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
      wordSsaRenameMove, wordSsaFreshList, wordSsaForceRename, hsource,
      wordSsaReadMoveSource]

theorem wordSsaRenameProgram_assign_const
    (ssa : WordSsaState) (destination : Nat) (value : Word width) :
    wordSsaRenameProgram ssa
        (.assign destination (.const value) : WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2 (.const value)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_assign_binary_var_var [OfNat α 0]
    (ssa : WordSsaState) (destination : Nat) (operator : BinOp)
    (left right : Nat) :
    wordSsaRenameProgram ssa
        (.assign destination (.op operator [.var left, .var right]) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.op operator [.var (wordSsaRead ssa left), .var (wordSsaRead ssa right)])) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_assign_binary_var_const
    (ssa : WordSsaState) (destination : Nat) (operator : BinOp)
    (source : Nat) (value : Word width) :
    wordSsaRenameProgram ssa
        (.assign destination (.op operator [.var source, .const value]) :
          WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.op operator [.var (wordSsaRead ssa source), .const value])) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_assign_binary_const_const
    (ssa : WordSsaState) (destination : Nat) (operator : BinOp)
    (left right : Word width) :
    wordSsaRenameProgram ssa
        (.assign destination (.op operator [.const left, .const right]) :
          WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.op operator [.const left, .const right])) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_assign_shift_var_const
    (ssa : WordSsaState) (destination : Nat) (operator : Shift)
    (source : Nat) (amount : Word width) :
    wordSsaRenameProgram ssa
        (.assign destination (.shift operator (.var source) (.const amount)) :
          WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.shift operator (.var (wordSsaRead ssa source)) (.const amount))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_assign_shift_var_var [OfNat α 0]
    (ssa : WordSsaState) (destination : Nat) (operator : Shift)
    (left right : Nat) :
    wordSsaRenameProgram ssa
        (.assign destination (.shift operator (.var left) (.var right)) :
          WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.shift operator (.var (wordSsaRead ssa left))
            (.var (wordSsaRead ssa right)))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_assign_rotate_var_const
    (ssa : WordSsaState) (destination : Nat) (source : Nat)
    (amount : Word width) :
    wordSsaRenameProgram ssa
        (.assign destination (.shift .ror (.var source) (.const amount)) :
          WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.shift .ror (.var (wordSsaRead ssa source)) (.const amount))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_assign_rotate_var_var [OfNat α 0]
    (ssa : WordSsaState) (destination left right : Nat) :
    wordSsaRenameProgram ssa
        (.assign destination (.shift .ror (.var left) (.var right)) :
          WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .assign (wordSsaFresh ssa destination).2
          (.shift .ror (.var (wordSsaRead ssa left))
            (.var (wordSsaRead ssa right)))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_store_var [OfNat α 0]
    (ssa : WordSsaState) (address value : Nat) :
    wordSsaRenameProgram ssa
        (.store (.var address) value : WordProg α) =
      (ssa, .store (.var (wordSsaRead ssa address))
        (wordSsaRead ssa value)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_load_var [OfNat α 0]
    (ssa : WordSsaState) (destination address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .load destination (.var address) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load (wordSsaFresh ssa destination).2
          (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_load8_var [OfNat α 0]
    (ssa : WordSsaState) (destination address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .load8 destination (.var address) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load8 (wordSsaFresh ssa destination).2
          (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_load16_var [OfNat α 0]
    (ssa : WordSsaState) (destination address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .load16 destination (.var address) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load16 (wordSsaFresh ssa destination).2
          (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_load32_var [OfNat α 0]
    (ssa : WordSsaState) (destination address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .load32 destination (.var address) : WordProg α) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load32 (wordSsaFresh ssa destination).2
          (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_store_var [OfNat α 0]
    (ssa : WordSsaState) (value address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .store value (.var address) : WordProg α) =
      (ssa, .shareInst .store (wordSsaRead ssa value)
        (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_store8_var [OfNat α 0]
    (ssa : WordSsaState) (value address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .store8 value (.var address) : WordProg α) =
      (ssa, .shareInst .store8 (wordSsaRead ssa value)
        (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_store16_var [OfNat α 0]
    (ssa : WordSsaState) (value address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .store16 value (.var address) : WordProg α) =
      (ssa, .shareInst .store16 (wordSsaRead ssa value)
        (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_store32_var [OfNat α 0]
    (ssa : WordSsaState) (value address : Nat) :
    wordSsaRenameProgram ssa
        (.shareInst .store32 value (.var address) : WordProg α) =
      (ssa, .shareInst .store32 (wordSsaRead ssa value)
        (.var (wordSsaRead ssa address))) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_load_const
    (ssa : WordSsaState) (destination : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .load destination (.const address) : WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load (wordSsaFresh ssa destination).2 (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_store_const
    (ssa : WordSsaState) (value : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .store value (.const address) : WordProg (Word width)) =
      (ssa, .shareInst .store (wordSsaRead ssa value) (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_load8_const
    (ssa : WordSsaState) (destination : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .load8 destination (.const address) : WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load8 (wordSsaFresh ssa destination).2 (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_load16_const
    (ssa : WordSsaState) (destination : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .load16 destination (.const address) : WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load16 (wordSsaFresh ssa destination).2 (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_load32_const
    (ssa : WordSsaState) (destination : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .load32 destination (.const address) : WordProg (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .shareInst .load32 (wordSsaFresh ssa destination).2 (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_store8_const
    (ssa : WordSsaState) (value : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .store8 value (.const address) : WordProg (Word width)) =
      (ssa, .shareInst .store8 (wordSsaRead ssa value) (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_store16_const
    (ssa : WordSsaState) (value : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .store16 value (.const address) : WordProg (Word width)) =
      (ssa, .shareInst .store16 (wordSsaRead ssa value) (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameProgram_shareInst_store32_const
    (ssa : WordSsaState) (value : Nat) (address : Word width) :
    wordSsaRenameProgram ssa
        (.shareInst .store32 value (.const address) : WordProg (Word width)) =
      (ssa, .shareInst .store32 (wordSsaRead ssa value) (.const address)) := by
  simp [wordSsaRenameProgram, wordSsaRenameProgramWithLoops,
    wordSsaRenameExp]

theorem wordSsaRenameInst_div {width : Nat}
    (ssa : WordSsaState) (destination dividend divisor : Nat) :
    wordSsaRenameInst ssa (.arith (.div destination dividend divisor) : WordInst (Word width)) =
      ((wordSsaFresh ssa destination).1,
        .arith (.div (wordSsaFresh ssa destination).2
          (wordSsaRead ssa dividend) (wordSsaRead ssa divisor))) := by
  rfl

theorem wordSsaRenameInst_longMul {width : Nat}
    (ssa : WordSsaState) (destinationLeft destinationRight sourceLeft sourceRight : Nat) :
    wordSsaRenameInst ssa
        (.arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) : WordInst (Word width)) =
      (let sourceLeft := wordSsaRead ssa sourceLeft
       let sourceRight := wordSsaRead ssa sourceRight
       let (ssa, freshLeft) := wordSsaFresh ssa destinationLeft
       let (ssa, freshRight) := wordSsaFresh ssa destinationRight
       (ssa, .arith (.longMul freshLeft freshRight
         sourceLeft sourceRight))) := by
  rfl

end Flapjack.RiscV
