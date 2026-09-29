import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.Semantics.PanSemStateEval

/-!
Source-model evaluator for the underspecified HOL `LOG2 0` case.

HOL `byte_align_def` asks for `LOG2 (dimindex DIV 8)`.  At widths below 8,
the argument is zero and the source definition does not choose a value.  The
natural completion parameter `log2Zero` below denotes that one global value;
it is threaded unchanged through recursive expression evaluation.  This is
an untagged model family, not a claim that the production evaluator uses every
completion (or that Lean's `Nat.log2 0 = 0` is HOL's choice).
-/

namespace Flapjack

def panByteAlignHOLLog2Zero {width : Nat} (log2Zero : Nat)
    (address : RiscV.Word width) : RiscV.Word width :=
  let bytes := width / 8
  let exponent := if bytes = 0 then log2Zero else Nat.log2 bytes
  let alignment := 2 ^ exponent
  BitVec.ofNat width ((address.toNat / alignment) * alignment)

theorem panByteAlignHOLLog2Zero_eq_panByteAlignHOL {width : Nat}
    (hwidth : 8 ≤ width) (log2Zero : Nat) (address : RiscV.Word width) :
    panByteAlignHOLLog2Zero log2Zero address = panByteAlignHOL address := by
  have hbytes : width / 8 ≠ 0 := by omega
  simp [panByteAlignHOLLog2Zero, panByteAlignHOL, hbytes]

noncomputable def panMemLoadByteHOLLog2Zero {width : Nat} [NeZero width]
    (log2Zero : Nat)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop)
    (bigEndian : Bool) (address : RiscV.Word width) : Option UInt8 := by
  classical
  exact
    let aligned := panByteAlignHOLLog2Zero log2Zero address
    match memory aligned with
    | .word value =>
        if domain aligned then some (panGetByteHOL address value bigEndian) else none

noncomputable def panMemLoad32HOLLog2Zero {width : Nat} [NeZero width]
    (log2Zero : Nat)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop)
    (bigEndian : Bool) (address : RiscV.Word width) : Option (RiscV.Word 32) := by
  classical
  exact
    if address.toNat % 4 = 0 then
      let aligned := panByteAlignHOLLog2Zero log2Zero address
      match memory aligned with
      | .word value =>
          if domain aligned then
            let getByte := fun currentAddress =>
              BitVec.ofNat width (panGetByteHOL currentAddress value bigEndian).toNat
            let bytes := [getByte address, getByte (address + 1),
              getByte (address + 2), getByte (address + 3)]
            some (RiscV.panRiscVWordOfBytes (width := 32) bigEndian
              (bytes.map fun byte => BitVec.ofNat 32 byte.toNat))
          else none
    else none

theorem panMemLoadByteHOLLog2Zero_eq_panMemLoadByteHOL {width : Nat}
    [NeZero width] (hwidth : 8 ≤ width) (log2Zero : Nat)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) :
    panMemLoadByteHOLLog2Zero log2Zero memory domain bigEndian address =
      panMemLoadByteHOL memory domain bigEndian address := by
  simp [panMemLoadByteHOLLog2Zero, panMemLoadByteHOL,
    panByteAlignHOLLog2Zero_eq_panByteAlignHOL hwidth log2Zero address]

theorem panMemLoad32HOLLog2Zero_eq_panMemLoad32HOL {width : Nat}
    [NeZero width] (hwidth : 8 ≤ width) (log2Zero : Nat)
    (memory : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) :
    panMemLoad32HOLLog2Zero log2Zero memory domain bigEndian address =
      panMemLoad32HOL memory domain bigEndian address := by
  simp [panMemLoad32HOLLog2Zero, panMemLoad32HOL,
    panByteAlignHOLLog2Zero_eq_panByteAlignHOL hwidth log2Zero address]

/-- Recursive `eval_def` model with one shared completion for every byte
alignment reached while evaluating the expression.  The full Option result
and memory-domain behavior are retained. -/
noncomputable def evalCrepSemHOLExpLog2Zero {width : Nat} [NeZero width]
    {ffiState : Type} (log2Zero : Nat)
    (state : CrepSemHOLState width ffiState) :
    CrepExpHOL width → Option (HolWordLab width) := by
  classical
  exact fun
    | .const value => some (.word value)
    | .var name => state.locals.lookup name
    | .load address => do
        let address ← evalCrepSemHOLExpLog2Zero log2Zero state address
        match address with
        | .word word =>
            if state.memaddrs word then some (state.memory word) else none
    | .load32 address => do
        let address ← evalCrepSemHOLExpLog2Zero log2Zero state address
        match address with
        | .word word =>
            (panMemLoad32HOLLog2Zero log2Zero state.memory state.memaddrs
              state.be word).map (fun value => .word (BitVec.ofNat width value.toNat))
    | .loadByte address => do
        let address ← evalCrepSemHOLExpLog2Zero log2Zero state address
        match address with
        | .word word =>
            (panMemLoadByteHOLLog2Zero log2Zero state.memory state.memaddrs
              state.be word).map (fun value =>
                .word (BitVec.ofNat width value.toNat))
    | .loadGlob address => state.globals.lookup address
    | .op operator args => do
        let values ← args.mapM (evalCrepSemHOLExpLog2Zero log2Zero state)
        (wordOpHOL operator (values.map fun value =>
          match value with | .word word => word)).map HolWordLab.word
    | .crepOp operator args => do
        let values ← args.mapM (evalCrepSemHOLExpLog2Zero log2Zero state)
        (crepOpCrepWord operator (values.map fun value =>
          match value with | .word word => word)).map HolWordLab.word
    | .cmp operator left right => do
        let left ← evalCrepSemHOLExpLog2Zero log2Zero state left
        let right ← evalCrepSemHOLExpLog2Zero log2Zero state right
        match left, right with
        | .word left, .word right =>
            some (.word (Compiler.Encoders.Asm.wordCmpResultHOL operator left right))
    | .shift operator left right => do
        let left ← evalCrepSemHOLExpLog2Zero log2Zero state left
        let right ← evalCrepSemHOLExpLog2Zero log2Zero state right
        match left, right with
        | .word left, .word right =>
            (wordShiftHOL operator left right.toNat).map HolWordLab.word
    | .baseAddr => some (.word state.baseAddr)
    | .topAddr => some (.word state.topAddr)

theorem evalCrepSemHOLExpLog2Zero_loadByte {width : Nat} [NeZero width]
    {ffiState : Type} (log2Zero : Nat)
    (state : CrepSemHOLState width ffiState) (address : CrepExpHOL width) :
    evalCrepSemHOLExpLog2Zero log2Zero state (.loadByte address) = (do
      let address ← evalCrepSemHOLExpLog2Zero log2Zero state address
      match address with
      | .word word =>
          (panMemLoadByteHOLLog2Zero log2Zero state.memory state.memaddrs
            state.be word).map (fun value => .word (BitVec.ofNat width value.toNat))) := by
  classical
  simp only [evalCrepSemHOLExpLog2Zero]

theorem evalCrepSemHOLExpLog2Zero_load32 {width : Nat} [NeZero width]
    {ffiState : Type} (log2Zero : Nat)
    (state : CrepSemHOLState width ffiState) (address : CrepExpHOL width) :
    evalCrepSemHOLExpLog2Zero log2Zero state (.load32 address) = (do
      let address ← evalCrepSemHOLExpLog2Zero log2Zero state address
      match address with
      | .word word =>
          (panMemLoad32HOLLog2Zero log2Zero state.memory state.memaddrs
            state.be word).map (fun value => .word (BitVec.ofNat width value.toNat))) := by
  classical
  simp only [evalCrepSemHOLExpLog2Zero]

theorem evalCrepSemHOLExpLog2Zero_eq_evalCrepSemHOLExp
    {width : Nat} [NeZero width] (hwidth : 8 ≤ width) {ffiState : Type}
    (log2Zero : Nat) (state : CrepSemHOLState width ffiState)
    (expression : CrepExpHOL width) :
    evalCrepSemHOLExpLog2Zero log2Zero state expression =
      evalCrepSemHOLExp state expression := by
  classical
  induction expression using evalCrepSemHOLExpLog2Zero.induct with
  | case1 value => simp [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp]
  | case2 name => simp [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp]
  | case3 address ih => simp [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp, ih]
  | case4 address ih =>
      simp [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp, ih,
        panMemLoad32HOLLog2Zero_eq_panMemLoad32HOL hwidth log2Zero]
  | case5 address ih =>
      simp [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp, ih,
        panMemLoadByteHOLLog2Zero_eq_panMemLoadByteHOL hwidth log2Zero]
  | case6 address => simp [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp]
  | case7 operator expressions ih =>
      simp only [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp]
      have hmap : expressions.mapM (evalCrepSemHOLExpLog2Zero log2Zero state) =
          expressions.mapM (evalCrepSemHOLExp state) := by
        induction expressions with
        | nil => simp
        | cons x xs ihxs =>
            have htail : xs.mapM (evalCrepSemHOLExpLog2Zero log2Zero state) =
                xs.mapM (evalCrepSemHOLExp state) :=
              ihxs (fun y hy => ih y (by simp [hy]))
            simp only [List.mapM_cons, ih x (by simp), htail]
      rw [hmap]
  | case8 operator expressions ih =>
      simp only [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp]
      have hmap : expressions.mapM (evalCrepSemHOLExpLog2Zero log2Zero state) =
          expressions.mapM (evalCrepSemHOLExp state) := by
        induction expressions with
        | nil => simp
        | cons x xs ihxs =>
            have htail : xs.mapM (evalCrepSemHOLExpLog2Zero log2Zero state) =
                xs.mapM (evalCrepSemHOLExp state) :=
              ihxs (fun y hy => ih y (by simp [hy]))
            simp only [List.mapM_cons, ih x (by simp), htail]
      rw [hmap]
  | case9 operator left right ihl ihr =>
      simp [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp, ihl, ihr]
  | case10 operator left right ihl ihr =>
      simp [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp, ihl, ihr]
  | case11 => simp [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp]
  | case12 => simp [evalCrepSemHOLExpLog2Zero, evalCrepSemHOLExp]

end Flapjack

namespace Flapjack

/-- Distinct permitted completions visibly distinguish the one-bit
    byte-alignment result.  The direct HOL EVAL observation for this same
    source expression is retained at
    `scripts/hol-probes/pan_fixed_load_probe.out:50`; it still contains
    `LOG2 0` rather than choosing either result. -/
example : panByteAlignHOLLog2Zero (width := 1) 0 (BitVec.ofNat 1 1) =
    BitVec.ofNat 1 1 := by decide

example : panByteAlignHOLLog2Zero (width := 1) 1 (BitVec.ofNat 1 1) =
    BitVec.ofNat 1 0 := by decide

end Flapjack
