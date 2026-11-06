import Flapjack.Compiler.Backend.LinearScan.HiddenState
import Flapjack.Compiler.Backend.RegAlloc.Proofs.AccessorEqns

/-!
Array-backed state for a future executable linear-scan allocator. The current
compiler still runs the list-backed source definition. These conversions and
primitive correspondences are Flapjack infrastructure; they have no HOL
declaration of their own.
-/
namespace Flapjack.LinearScan

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

structure ProductionState where
  colors : Array Nat
  int_beg : Array Int
  int_end : Array Int
  sorted_regs : Array Nat
  sorted_moves : Array (Nat × (Nat × Nat))

def ProductionState.ofSource (s : LinearScanHiddenState) : ProductionState :=
  ⟨s.colors.toArray, s.int_beg.toArray, s.int_end.toArray,
    s.sorted_regs.toArray, s.sorted_moves.toArray⟩

def ProductionState.toSource (s : ProductionState) : LinearScanHiddenState :=
  ⟨s.colors.toList, s.int_beg.toList, s.int_end.toList,
    s.sorted_regs.toList, s.sorted_moves.toList⟩

theorem ProductionState.toSource_ofSource (s : LinearScanHiddenState) :
    (ofSource s).toSource = s := by
  cases s
  simp [ofSource, toSource]

theorem ProductionState.ofSource_toSource (s : ProductionState) :
    ofSource s.toSource = s := by
  cases s
  simp [ofSource, toSource]

/-- Indexed read with the same explicit out-of-range exception as `mSub`. -/
def productionSub {α ε : Type} (error : ε) (index : Nat) (xs : Array α) : Exc α ε :=
  if h : index < xs.size then .success xs[index] else .failure error

/-- Indexed update with the same explicit out-of-range exception as `mUpdate`. -/
def productionUpdate {α ε : Type} (error : ε) (index : Nat) (x : α)
    (xs : Array α) : Exc (Array α) ε :=
  if h : index < xs.size then .success (xs.set index x h) else .failure error

theorem productionSub_correct {α ε : Type} [Nonempty α] (error : ε)
    (index : Nat) (xs : Array α) :
    productionSub error index xs = mSub error index xs.toList := by
  rw [Flapjack.RegAlloc.msubEqn]
  by_cases h : index < xs.size
  · simp [productionSub, h, Flapjack.holEl_eq_getElem]
  · simp [productionSub, h]

theorem productionUpdate_correct {α ε : Type} (error : ε) (index : Nat)
    (x : α) (xs : Array α) :
    (match productionUpdate error index x xs with
      | .success result => .success result.toList
      | .failure e => .failure e) = mUpdate error x index xs.toList := by
  rw [Flapjack.RegAlloc.mupdateEqn]
  by_cases h : index < xs.size <;> simp [productionUpdate, h, Array.toList_set]

/-- A production operation simulates the source operation if both return the
same result and the resulting states agree after conversion. -/
def Simulates {α ε : Type} (fast : M ProductionState α ε)
    (source : M LinearScanHiddenState α ε) : Prop :=
  ∀ s, let (result, next) := fast s
       (result, next.toSource) = source s.toSource

def productionArrayLength {α ε : Type} (get : ProductionState → Array α) :
    M ProductionState Nat ε := fun s => (.success (get s).size, s)

def productionArraySub {α : Type} (get : ProductionState → Array α)
    (index : Nat) : M ProductionState α StateException :=
  fun s => (productionSub .Subscript index (get s), s)

def productionArrayUpdate {α : Type} (get : ProductionState → Array α)
    (set : Array α → ProductionState → ProductionState) (index : Nat) (x : α) :
    M ProductionState Unit StateException := fun s =>
  match productionUpdate .Subscript index x (get s) with
  | .success values => (.success (), set values s)
  | .failure e => (.failure e, s)

theorem productionArrayLength_correct {α ε : Type}
    (get : ProductionState → Array α) (sourceGet : LinearScanHiddenState → List α)
    (hget : ∀ s, (get s).toList = sourceGet s.toSource) :
    Simulates (productionArrayLength (ε := ε) get) (arrayLength sourceGet) := by
  intro s
  simp [productionArrayLength, arrayLength, ← hget s]

theorem productionArraySub_correct {α : Type} [Nonempty α]
    (get : ProductionState → Array α) (sourceGet : LinearScanHiddenState → List α)
    (hget : ∀ s, (get s).toList = sourceGet s.toSource) (index : Nat) :
    Simulates (productionArraySub get index) (arraySub sourceGet .Subscript index) := by
  intro s
  simp [productionArraySub, arraySub, productionSub_correct, hget]

theorem productionArrayUpdate_correct {α : Type}
    (get : ProductionState → Array α) (set : Array α → ProductionState → ProductionState)
    (sourceGet : LinearScanHiddenState → List α)
    (sourceSet : List α → LinearScanHiddenState → LinearScanHiddenState)
    (hget : ∀ s, (get s).toList = sourceGet s.toSource)
    (hset : ∀ values s, (set values s).toSource = sourceSet values.toList s.toSource)
    (index : Nat) (x : α) :
    Simulates (productionArrayUpdate get set index x)
      (arrayUpdate sourceGet sourceSet .Subscript index x) := by
  intro s
  have h := productionUpdate_correct StateException.Subscript index x (get s)
  rw [hget s] at h
  unfold productionArrayUpdate arrayUpdate
  cases hp : productionUpdate StateException.Subscript index x (get s) <;>
    simp only [hp] at h ⊢ <;> rw [← h] <;> simp [hset]

theorem simulates_ret {α ε : Type} (value : α) :
    Simulates (ret value : M ProductionState α ε)
      (ret value : M LinearScanHiddenState α ε) := by
  intro s
  rfl

theorem simulates_bind {α β ε : Type}
    (fast : M ProductionState α ε) (source : M LinearScanHiddenState α ε)
    (fastNext : α → M ProductionState β ε) (sourceNext : α → M LinearScanHiddenState β ε)
    (h : Simulates fast source) (hn : ∀ x, Simulates (fastNext x) (sourceNext x)) :
    Simulates (bind fast fastNext) (bind source sourceNext) := by
  intro s
  have hs := h s
  cases he : fast s with
  | mk result next =>
    simp only [he] at hs
    unfold Flapjack.Translator.Monadic.MonadBase.bind
    rw [he, ← hs]
    cases result with
    | success value => exact hn value next
    | failure error => rfl

theorem simulates_ignoreBind {α β ε : Type}
    (fast : M ProductionState α ε) (source : M LinearScanHiddenState α ε)
    (fastNext : M ProductionState β ε) (sourceNext : M LinearScanHiddenState β ε)
    (h : Simulates fast source) (hn : Simulates fastNext sourceNext) :
    Simulates (ignoreBind fast fastNext) (ignoreBind source sourceNext) := by
  exact simulates_bind fast source (fun _ => fastNext) (fun _ => sourceNext) h (fun _ => hn)


namespace Production

def colorsLength {ε : Type} : M ProductionState Nat ε :=
  productionArrayLength (fun s => s.colors)

def colorsSub : Nat → M ProductionState (Nat) StateException :=
  productionArraySub (fun s => s.colors)

def updateColors : Nat → (Nat) → M ProductionState Unit StateException :=
  productionArrayUpdate (fun s => s.colors) (fun values s => {s with colors := values})

theorem colorsLength_correct {ε : Type} :
    Simulates (colorsLength : M ProductionState Nat ε)
      (Flapjack.LinearScan.colorsLength : M LinearScanHiddenState Nat ε) :=
  productionArrayLength_correct _ _ (fun _ => rfl)

theorem colorsSub_correct (n : Nat) :
    Simulates (colorsSub n) (Flapjack.LinearScan.colorsSub n) :=
  productionArraySub_correct _ _ (fun _ => rfl) n

theorem updateColors_correct (n : Nat) (x : Nat) :
    Simulates (updateColors n x) (Flapjack.LinearScan.updateColors n x) :=
  productionArrayUpdate_correct _ _ _ _ (fun _ => rfl) (fun _ _ => rfl) n x

def intBegLength {ε : Type} : M ProductionState Nat ε :=
  productionArrayLength (fun s => s.int_beg)

def intBegSub : Nat → M ProductionState (Int) StateException :=
  productionArraySub (fun s => s.int_beg)

def updateIntBeg : Nat → (Int) → M ProductionState Unit StateException :=
  productionArrayUpdate (fun s => s.int_beg) (fun values s => {s with int_beg := values})

theorem intBegLength_correct {ε : Type} :
    Simulates (intBegLength : M ProductionState Nat ε)
      (Flapjack.LinearScan.intBegLength : M LinearScanHiddenState Nat ε) :=
  productionArrayLength_correct _ _ (fun _ => rfl)

theorem intBegSub_correct (n : Nat) :
    Simulates (intBegSub n) (Flapjack.LinearScan.intBegSub n) :=
  productionArraySub_correct _ _ (fun _ => rfl) n

theorem updateIntBeg_correct (n : Nat) (x : Int) :
    Simulates (updateIntBeg n x) (Flapjack.LinearScan.updateIntBeg n x) :=
  productionArrayUpdate_correct _ _ _ _ (fun _ => rfl) (fun _ _ => rfl) n x

def intEndLength {ε : Type} : M ProductionState Nat ε :=
  productionArrayLength (fun s => s.int_end)

def intEndSub : Nat → M ProductionState (Int) StateException :=
  productionArraySub (fun s => s.int_end)

def updateIntEnd : Nat → (Int) → M ProductionState Unit StateException :=
  productionArrayUpdate (fun s => s.int_end) (fun values s => {s with int_end := values})

theorem intEndLength_correct {ε : Type} :
    Simulates (intEndLength : M ProductionState Nat ε)
      (Flapjack.LinearScan.intEndLength : M LinearScanHiddenState Nat ε) :=
  productionArrayLength_correct _ _ (fun _ => rfl)

theorem intEndSub_correct (n : Nat) :
    Simulates (intEndSub n) (Flapjack.LinearScan.intEndSub n) :=
  productionArraySub_correct _ _ (fun _ => rfl) n

theorem updateIntEnd_correct (n : Nat) (x : Int) :
    Simulates (updateIntEnd n x) (Flapjack.LinearScan.updateIntEnd n x) :=
  productionArrayUpdate_correct _ _ _ _ (fun _ => rfl) (fun _ _ => rfl) n x

def sortedRegsLength {ε : Type} : M ProductionState Nat ε :=
  productionArrayLength (fun s => s.sorted_regs)

def sortedRegsSub : Nat → M ProductionState (Nat) StateException :=
  productionArraySub (fun s => s.sorted_regs)

def updateSortedRegs : Nat → (Nat) → M ProductionState Unit StateException :=
  productionArrayUpdate (fun s => s.sorted_regs) (fun values s => {s with sorted_regs := values})

theorem sortedRegsLength_correct {ε : Type} :
    Simulates (sortedRegsLength : M ProductionState Nat ε)
      (Flapjack.LinearScan.sortedRegsLength : M LinearScanHiddenState Nat ε) :=
  productionArrayLength_correct _ _ (fun _ => rfl)

theorem sortedRegsSub_correct (n : Nat) :
    Simulates (sortedRegsSub n) (Flapjack.LinearScan.sortedRegsSub n) :=
  productionArraySub_correct _ _ (fun _ => rfl) n

theorem updateSortedRegs_correct (n : Nat) (x : Nat) :
    Simulates (updateSortedRegs n x) (Flapjack.LinearScan.updateSortedRegs n x) :=
  productionArrayUpdate_correct _ _ _ _ (fun _ => rfl) (fun _ _ => rfl) n x

def sortedMovesLength {ε : Type} : M ProductionState Nat ε :=
  productionArrayLength (fun s => s.sorted_moves)

def sortedMovesSub : Nat → M ProductionState (Nat × (Nat × Nat)) StateException :=
  productionArraySub (fun s => s.sorted_moves)

def updateSortedMoves : Nat → (Nat × (Nat × Nat)) → M ProductionState Unit StateException :=
  productionArrayUpdate (fun s => s.sorted_moves) (fun values s => {s with sorted_moves := values})

theorem sortedMovesLength_correct {ε : Type} :
    Simulates (sortedMovesLength : M ProductionState Nat ε)
      (Flapjack.LinearScan.sortedMovesLength : M LinearScanHiddenState Nat ε) :=
  productionArrayLength_correct _ _ (fun _ => rfl)

theorem sortedMovesSub_correct (n : Nat) :
    Simulates (sortedMovesSub n) (Flapjack.LinearScan.sortedMovesSub n) :=
  productionArraySub_correct _ _ (fun _ => rfl) n

theorem updateSortedMoves_correct (n : Nat) (x : Nat × (Nat × Nat)) :
    Simulates (updateSortedMoves n x) (Flapjack.LinearScan.updateSortedMoves n x) :=
  productionArrayUpdate_correct _ _ _ _ (fun _ => rfl) (fun _ _ => rfl) n x

end Production

end Flapjack.LinearScan
