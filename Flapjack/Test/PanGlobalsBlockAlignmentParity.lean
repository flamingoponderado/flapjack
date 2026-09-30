import Flapjack.Pancake.Proofs.PanGlobals.GlobalBlockAlignment
open Flapjack

/- Kernel replay of original alignmentTheory observations in
 scripts/hol-probes/pan_globals_block_alignment_probe.out. -/
private def observe {width : Nat} (a b : BitVec width) :=
  ((a-b).toNat, decide (panByteAlignHOL a = a),
    decide (panByteAlignHOL b = b), decide (panByteAlignHOL (a-b) = a-b))

-- block32
example : observe (12 : BitVec 32) 4 =
    (8, true, true, true) := by decide

-- wrap32
example : observe (0 : BitVec 32) 4 =
    (4294967292, true, true, true) := by decide

-- zero32
example : observe (4 : BitVec 32) 4 =
    (0, true, true, true) := by decide

-- unaligned32
example : observe (5 : BitVec 32) 4 =
    (1, false, true, false) := by decide

-- block64
example : observe (24 : BitVec 64) 8 =
    (16, true, true, true) := by decide

-- wrap64
example : observe (0 : BitVec 64) 8 =
    (18446744073709551608, true, true, true) := by decide

-- zero64
example : observe (8 : BitVec 64) 8 =
    (0, true, true, true) := by decide

-- unaligned64
example : observe (9 : BitVec 64) 8 =
    (1, false, true, false) := by decide

