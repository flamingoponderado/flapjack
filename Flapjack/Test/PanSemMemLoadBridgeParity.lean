import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge

/-!
Concrete instances of the production-to-exact `mem_load_def` codec theorem.
The production and exact outputs are compared after `holValueToHOL`; direct
oracle rows for both sides are replayed in PanSemStateEvalParity and
PanSemMemLoadExactParity.
-/

namespace Flapjack.Test.PanSemMemLoadBridgeParity

open Flapjack
open Flapjack.Pancake.PanLang

private abbrev Word64 := RiscV.Word 64

private def loadDomain : Word64 → Prop := fun address => address = 0 ∨ address = 8

private instance : DecidablePred loadDomain := fun address => by
  unfold loadDomain
  infer_instance

private def loadMemory : Word64 → HolWordLab 64 := fun address =>
  if address == 0 then .word (BitVec.ofNat 64 0x11)
  else if address == 8 then .word (BitVec.ofNat 64 0x22)
  else .word 0

private def strideMemory : Word64 → HolWordLab 64 := fun address =>
  .word (BitVec.ofNat 64 (10 * (address.toNat / 8)))

private def structContext : StructContextHOL :=
  [("S", { fields := [("f", Shape.one)], size := 3 })]

private theorem bridgeLoad (shape : Shape) (address : Word64)
    (context : StructContextHOL)
    (namesRanged : ∀ p ∈ context, NameRanged p.1)
    (infosRanged : ∀ p ∈ context, StructInfoByteRanged p.2)
    (shapeRanged : ShapeByteRanged shape)
    (memory : Word64 → HolWordLab 64) :
    ((panMemLoadHOL shape address loadDomain memory context).map
        (holValueToHOL (width := 64)) : Option (ValueHOL 64)) =
      memLoadHOLExact (shapeToHOL shape) address loadDomain memory
        (structContextToHOL context) := by
  exact panMemLoadHOL_map_holValueToHOL loadDomain memory loadDomain memory
    (by intro a; rfl) (by intro a _; rfl) shape address context
    namesRanged infosRanged shapeRanged

-- Production and exact results agree for the total One branch and its domain miss.
example :
    ((panMemLoadHOL Shape.one 0 loadDomain loadMemory []).map
        (holValueToHOL (width := 64)) : Option (ValueHOL 64)) =
      memLoadHOLExact ShapeHOL.one 0 loadDomain loadMemory [] := by
  simpa [shapeToHOL, structContextToHOL] using
    (bridgeLoad Shape.one 0 [] (by intro p hp; simp at hp)
      (by intro p hp; simp at hp) (by simp [ShapeByteRanged]) loadMemory)

example :
    ((panMemLoadHOL Shape.one 1 loadDomain loadMemory []).map
        (holValueToHOL (width := 64)) : Option (ValueHOL 64)) =
      memLoadHOLExact ShapeHOL.one 1 loadDomain loadMemory [] := by
  simpa [shapeToHOL, structContextToHOL] using
    (bridgeLoad Shape.one 1 [] (by intro p hp; simp at hp)
      (by intro p hp; simp at hp) (by simp [ShapeByteRanged]) loadMemory)

-- The Comb fixture checks the context-sensitive stride across two word cells.
example :
    ((panMemLoadHOL (.comb [.one, .one]) 0 loadDomain loadMemory []).map
        (holValueToHOL (width := 64)) : Option (ValueHOL 64)) =
      memLoadHOLExact (.comb [.one, .one]) 0 loadDomain loadMemory [] := by
  simpa [shapeToHOL, structContextToHOL] using
    (bridgeLoad (.comb [.one, .one]) 0 [] (by intro p hp; simp at hp)
      (by intro p hp; simp at hp) (by simp [ShapeByteRanged]) loadMemory)

example :
    ((panMemLoadHOL (.comb [.one, .one]) 0 loadDomain strideMemory []).map
        (holValueToHOL (width := 64)) : Option (ValueHOL 64)) =
      memLoadHOLExact (.comb [.one, .one]) 0 loadDomain strideMemory [] := by
  simpa [shapeToHOL, structContextToHOL] using
    (bridgeLoad (.comb [.one, .one]) 0 [] (by intro p hp; simp at hp)
      (by intro p hp; simp at hp) (by simp [ShapeByteRanged]) strideMemory)

-- Named lookup and the absent-name result use byte-ranged MlString codecs.
example :
    ((panMemLoadHOL (.named "S") 0 loadDomain loadMemory structContext).map
        (holValueToHOL (width := 64)) : Option (ValueHOL 64)) =
      memLoadHOLExact (.named (Flapjack.Basis.Pure.MlString.ofString "S"))
        0 loadDomain loadMemory
        (structContextToHOL structContext) := by
  simpa [shapeToHOL, structContextToHOL] using
    (bridgeLoad (.named "S") 0 structContext (by
      intro p hp
      simp [structContext] at hp
      rcases hp with rfl
      simp [NameRanged]) (by
      intro p hp
      simp [structContext] at hp
      rcases hp with rfl
      simp [StructInfoByteRanged, ListParamByteRanged, ParamByteRanged,
        NameRanged, ShapeByteRanged]) (by
      simp [ShapeByteRanged]) loadMemory)

example :
    ((panMemLoadHOL (.named "T") 0 loadDomain loadMemory structContext).map
        (holValueToHOL (width := 64)) : Option (ValueHOL 64)) =
      memLoadHOLExact (.named (Flapjack.Basis.Pure.MlString.ofString "T"))
        0 loadDomain loadMemory
        (structContextToHOL structContext) := by
  simpa [shapeToHOL, structContextToHOL] using
    (bridgeLoad (.named "T") 0 structContext (by
      intro p hp
      simp [structContext] at hp
      rcases hp with rfl
      simp [NameRanged]) (by
      intro p hp
      simp [structContext] at hp
      rcases hp with rfl
      simp [StructInfoByteRanged, ListParamByteRanged, ParamByteRanged,
        NameRanged, ShapeByteRanged]) (by
      simp [ShapeByteRanged]) loadMemory)

-- Pin the transported results, not only the relation: these are concrete
-- values for the successful One, two-cell Comb, and Named branches.
example :
    ((panMemLoadHOL Shape.one 0 loadDomain loadMemory []).map
        (holValueToHOL (width := 64)) : Option (ValueHOL 64)) =
      some (.val (.word (BitVec.ofNat 64 0x11))) := by
  simp [panMemLoadHOL, loadDomain, loadMemory, holValueToHOL,
    HolWordLab.toPanWordLab]

example :
    ((panMemLoadHOL (.comb [.one, .one]) 0 loadDomain loadMemory []).map
        (holValueToHOL (width := 64)) : Option (ValueHOL 64)) =
      some (.rStruct [.val (.word (BitVec.ofNat 64 0x11)),
        .val (.word (BitVec.ofNat 64 0x22))]) := by
  simp [panMemLoadHOL, panMemLoadsHOL, loadDomain, loadMemory,
    panBytesInWord, sizeOfShWithCtxt, holValueToHOL, HolWordLab.toPanWordLab]

example :
    ((panMemLoadHOL (.named "S") 0 loadDomain loadMemory structContext).map
        (holValueToHOL (width := 64)) : Option (ValueHOL 64)) =
      some (.nStruct (Flapjack.Basis.Pure.MlString.ofString "S")
        [(Flapjack.Basis.Pure.MlString.ofString "f",
          .val (.word (BitVec.ofNat 64 0x11)))]) := by
  simp [panMemLoadHOL, panMemLoadFldsHOL, loadDomain, loadMemory, structContext,
    holValueToHOL, HolWordLab.toPanWordLab]

def runChecks : IO Bool := do
  IO.println "PASS production panMemLoadHOL and exact memLoadHOLExact agree under the checked codecs"
  pure true

end Flapjack.Test.PanSemMemLoadBridgeParity
