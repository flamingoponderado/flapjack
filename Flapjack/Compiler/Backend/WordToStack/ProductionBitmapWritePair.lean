module

public import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapTransport
public import Flapjack.Compiler.Backend.WordToStack.ProductionGcCutsets

@[expose] public section

/-! Complete actual caller bitmap-write transport. This is Flapjack production
carrier infrastructure with no HOL declaration. The shared native codec and
consumer are used directly, and the allocator producer supplies the coloured GC
domain. This does not establish whole-body or final compiler simulation. -/
namespace Flapjack.ProductionBitmapWritePair
open RiscV RiscV.CakeRegAlloc Compiler.Backend.WordToStack
open Compiler.Backend.StackLang

/-- Arbitrary native AppList prefixes commute with the whole writer observation.
The stored count stays independent of the prefix/data lengths. This supplies the
actual caller's empty-local-chunk/global-count convention without a new bound. -/
theorem nativePrefix {width : Nat} [NeZero width] (cutsets : Spt Unit × Spt Unit)
    (bitmaps : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat)
    (priorData : AppList (BitVec width)) :
    let plain := Native.wLiveNative cutsets bitmaps kf
    let prefixed := Native.wLiveNative cutsets (.append priorData bitmaps.1, bitmaps.2) kf
    (prefixed.1, appListAppend prefixed.2.1, prefixed.2.2) =
      (plain.1, appListAppend priorData ++ appListAppend plain.2.1, plain.2.2) := by
  have flattenAppend (left right : AppList (BitVec width)) :
      appListAppend (.append left right) = appListAppend left ++ appListAppend right :=
    (appListAppend_thm left right []).1
  by_cases empty : kf.2.1 = 0 <;>
    simp [Native.wLiveNative, empty, insertBitmap, flattenAppend, List.append_assoc]

end Flapjack.ProductionBitmapWritePair
