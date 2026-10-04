import Flapjack.Compiler.Backend.RegAlloc.ProductionWrapper
import Flapjack.Compiler.Backend.RegAlloc.Proofs.DoRegAllocCorrect
import Flapjack.RiscV.CakeAllocatorBitsBridge
import Flapjack.RiscV.PipelineDiagnostics
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile

namespace Flapjack.ProductionBitmapTransport
open RiscV Compiler.Backend.WordToStack

/-! Flapjack infrastructure for the executed bitmap carrier. These are not
additional HOL theorem ports. Encoding preserves arbitrary stored counts,
including inconsistent counts; live-cutset and whole-body transport remain open. -/

def encode {width : Nat} (state : WordStackBitmapState) : AppList (BitVec width) × Nat :=
  (.list (state.data.map (BitVec.ofNat width)), state.length)

/-- Actual initial output, including positive widths smaller than five. -/
theorem initial {width : Nat} (perf : Bool) :
    encode (width := width) (wordStackInitialBitmaps perf) =
      if perf then (.list [BitVec.ofNat width 16], 1)
      else (.list [BitVec.ofNat width 4], 1) := by
  cases perf <;> rfl

/-- Full insertion projection; count and returned offset are retained without
assuming count equals data length. Native tree shape is observed by flattening. -/
theorem insert {width : Nat} (state : WordStackBitmapState) (words : List Nat) :
    let actual := wordStackInsertBitmap state words
    let native := insertBitmap (words.map (BitVec.ofNat width)) (encode state)
    (appListAppend (encode (width := width) actual.1).1, (encode (width := width) actual.1).2, actual.2) =
      (appListAppend native.1.1, native.1.2, native.2) := by
  simp [wordStackInsertBitmap, insertBitmap, encode, appListAppend,
    appendAux, List.map_append]

/-- Actual location-derived packing uses the reviewed word-list recursion at
all positive widths. This deliberately retains the actual filtered locations;
relating them to the native coloured GC cutset is a separate caller obligation. -/
theorem livePacking {width : Nat} [NeZero width] (config : WordStackConfig)
    (slots : Nat) (live : List Nat) :
    (wordStackLiveBitmapFromLocations config slots width live).map (BitVec.ofNat width) =
      wordListW
        ((List.range slots).map (fun slot =>
          (live.filterMap (fun name => match wordStackLocation config name with
            | some (.stack index) => some (index - 1)
            | _ => none)).contains slot) ++ [true]) (width - 1) := by
  unfold wordStackLiveBitmapFromLocations
  exact CakeAlloc.frameBitmapWords_map (width - 1) _

/-- Stack-variable placement follows from the actual allocator run, through
its native correspondence and the original allocator correctness theorem.
Forced-input domain/bounds are original producer obligations, not desired
output facts. No final colour bound is assumed. -/
theorem allocator_stackColour (algorithm : RegAlloc.Algorithm)
    (entries : Option (NatInfoMap Nat)) (limit : Nat)
    (moves : List (Nat × (Nat × Nat))) (tree : WordClashTree)
    (forced : List (Nat × Nat)) (stackOnly : List Nat) (colours : NatInfoMap Nat)
    (bounds : ∀ pair ∈ forced,
      CakeRegAlloc.cakeSpDefaultIndexed (CakeRegAlloc.cakeSpDefaultIndex (CakeRegAlloc.cakeMkBij tree).toAllocator) pair.1 <
        (CakeRegAlloc.cakeMkBij tree).nextNode ∧
      CakeRegAlloc.cakeSpDefaultIndexed (CakeRegAlloc.cakeSpDefaultIndex (CakeRegAlloc.cakeMkBij tree).toAllocator) pair.2 <
        (CakeRegAlloc.cakeMkBij tree).nextNode)
    (domain : ∀ pair ∈ forced,
      RegAlloc.inClashTree (RegAlloc.productionClashTreeToNative tree) pair.1 ∧
      RegAlloc.inClashTree (RegAlloc.productionClashTreeToNative tree) pair.2)
    (produced : CakeRegAlloc.cakeDoRegAlloc algorithm.toProduction
      (entries.map (CakeRegAlloc.cakeSpillCostMap (CakeRegAlloc.cakeMkBij tree).nextNode))
      limit moves tree forced stackOnly = some colours)
    (name : Nat) (occurs : RegAlloc.inClashTree (RegAlloc.productionClashTreeToNative tree) name)
    (stacked : Flapjack.isStackVar name = true) :
    2 * limit ≤ CakeAlloc.totalColour colours name := by
  obtain ⟨actual, actualRun, productionRun⟩ :=
    RegAlloc.regAlloc_production algorithm entries limit moves tree forced stackOnly bounds
  rw [produced] at productionRun
  cases Option.some.inj productionRun
  obtain ⟨native, live, fullLive, nativeRun, checked, conventions, support, forcedOk⟩ :=
    RegAlloc.regAllocCorrect algorithm (entries.map sptFromAList) limit moves
      (RegAlloc.productionClashTreeToNative tree) forced
      (sptFromAList (stackOnly.map (fun name => (name, ())))) domain
  rw [actualRun] at nativeRun
  cases nativeRun
  have bound := (conventions name occurs).2
  have physical : Flapjack.isPhyVar name = false := by
    simp [Flapjack.isPhyVar, Flapjack.isStackVar] at stacked ⊢
    omega
  simp only [physical, Bool.false_eq_true, if_false, stacked, if_true] at bound
  have lookup := RegAlloc.tagDecoder_production colours name
  rw [spDefaultIndexed_corresponds] at lookup
  unfold CakeAlloc.totalColour
  rw [lookup]
  omega

/-- One physical spill slot is encoded at source bitmap index zero. This
is a regression for the executed builder, not an independent HOL port. -/
theorem oneSpill_repairedBitmap :
    wordStackLiveBitmapFromLocations
      (sourceWordStackConfig 0 { locations := [(3, .stack 1)], nextSpill := 1 } 1)
      1 64 [3] = [3] := by
  simp [wordStackLiveBitmapFromLocations, wordStackLocation, sourceWordStackConfig,
    lookupNatInfo, CakeAlloc.frameBitmapWords, CakeAlloc.frameBitmapWordsAux,
    CakeAlloc.bitsToWord]

/-- The corresponding original-coloured domain uses the same bit index. -/
theorem oneSpill_sourceBitmap : CakeAlloc.writeBitmap [44] 22 1 64 = [3] := by
  simp [CakeAlloc.writeBitmap, CakeAlloc.frameBitmapWords,
    CakeAlloc.frameBitmapWordsAux, CakeAlloc.bitsToWord]

/-- Full physical-frame to source-bitmap index arithmetic, including the
empty frame and truncating subtraction beyond its bounds. -/
theorem physicalSlot_bitmapIndex (slots distance : Nat) :
    ((if slots = 0 then 0 else slots + 1) - 1 - distance) - 1 =
      slots - 1 - distance := by
  split <;> omega

/-- Concrete retained colour formatting supplies the source bitmap index.
The register/stack threshold is supplied by allocator_stackColour, rather
than by a desired final-location equality. -/
theorem stackColour_bitmapIndex (k slots colour : Nat) (stacked : 2 * k ≤ colour) :
    (match CakeRegAlloc.cakeColourLocation k
        (if slots = 0 then 0 else slots + 1) colour with
      | .stack slot => some (slot - 1)
      | .register _ => none) = some (slots - 1 - (colour / 2 - k)) := by
  have bound : k ≤ colour / 2 := by omega
  simp only [CakeRegAlloc.cakeColourLocation, Nat.not_lt.mpr bound, if_false]
  rw [physicalSlot_bitmapIndex]

end Flapjack.ProductionBitmapTransport
