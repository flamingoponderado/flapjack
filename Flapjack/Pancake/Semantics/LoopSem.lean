module

public import Flapjack.LoopStateResult
public import Flapjack.LoopCallEnv
public import Flapjack.LoopFindCode
public import Flapjack.LoopGetVarImm
public import Flapjack.LoopSetVars
public import Flapjack.LoopArith
public import Flapjack.Compiler.Backend.BackendCommon
public import Flapjack.Pancake.Semantics.CrepRuntimeTarget

@[expose] public section

/-!
# Byte, memory and `get_var_imm` helpers from `loopSem`/`wordSem`

HOL-shaped helpers used by the Loop, Word, Stack and Lab semantics and their
proofs: `read_bytearray`, the byte/word codecs, the `mem_load`/`mem_store`
families (two of them tagged ports) and `get_var_imm`.

This module used to hold Flapjack's production Loop evaluator `evaluateLoop`
(a hook-parametric rendering of `loopSem$evaluate` over the production
`LoopMachineState`) with its hooks and machine adapters. No theorem or
executed path used it: the ported Loop pass theorems are stated over the exact
`LoopSemStateFiniteExact.evaluate` (`LoopSemStateExact.lean`), so it was
removed together with the production/exact bridge layer; it remains in the
git history.
-/

namespace Flapjack

/-- Flapjack byte-array reader with the recursive equation and argument order
    of HOL `read_bytearray_def` (`miscScript.sml:113`). It fixes the result
    element to `UInt8`; HOL leaves the `get_byte` result word type polymorphic,
    and the Crep call site specializes it to HOL `word8` (`BitVec 8`). Since
    `UInt8` is a different Lean carrier and no qualifier is approved for this
    translation, this declaration remains untagged. The exact positive-width
    helper is `readBytearrayWordHOL`; its `UInt8` projection is proved in
    `PanSem/ExtCallExact.lean`. -/
def readBytearrayHOL {width : Nat} (address : RiscV.Word width) (length : Nat)
    (getByte : RiscV.Word width → Option UInt8) : Option (List UInt8) :=
  match length with
  | 0 => some []
  | length + 1 => do
      let byte ← getByte address
      let rest ← readBytearrayHOL (address + 1) length getByte
      pure (byte :: rest)

/-- Exact positive-word specialization family of HOL `read_bytearray_def`
    (`cakeml/misc/miscScript.sml:113`): both the address word and returned
    byte word retain their independent HOL dimensions. The zero/successor
    recursion and failure propagation match the two HOL equations directly.
    HOL's `get_byte` result word type is polymorphic (see the comment above
    `read_bytearray_def`), so the independent `byteWidth` parameter is faithful.
    `(words_as_type_indexed_bitvec)` is inapplicable here because the
    declaration binds two independent dimension parameters (both guarded by
    `[NeZero]`); the checker rejects the qualifier in that case. -/
@[hol "cakeml/misc/miscScript.sml" "read_bytearray_def"]
def readBytearrayWordHOL {width byteWidth : Nat} [NeZero width] [NeZero byteWidth]
    (address : RiscV.Word width) (length : Nat)
    (getByte : RiscV.Word width → Option (BitVec byteWidth)) :
    Option (List (BitVec byteWidth)) :=
  match length with
  | 0 => some []
  | length + 1 => do
      let byte ← getByte address
      let rest ← readBytearrayWordHOL (address + 1) length getByte
      pure (byte :: rest)

/-- Flapjack-only support lemma: a successful `readBytearrayWordHOL` returns a
    list whose length is the requested length. HOL analogue:
    `read_bytearray_LENGTH` (`cakeml/misc/miscScript.sml:124`), whose statement
    is `(read_bytearray a n f = SOME x) ==> (LENGTH x = n)` for a fixed
    `word8`-valued reader `f : 'a word -> word8 option`. This lemma is NOT
    tagged as an exact port of that declaration because `readBytearrayWordHOL`
    generalizes HOL's fixed byte carrier to a parameterized `byteWidth` and an
    arbitrary `getByte : Word width -> BitVec byteWidth option`; the length
    fact is proved over that generalized interface rather than HOL's fixed one. -/
theorem readBytearrayWordHOL_length {width byteWidth : Nat} [NeZero width] [NeZero byteWidth]
    (address : RiscV.Word width) (length : Nat)
    (getByte : RiscV.Word width → Option (BitVec byteWidth))
    (bytes : List (BitVec byteWidth))
    (h : readBytearrayWordHOL (byteWidth := byteWidth) address length getByte = some bytes) :
    bytes.length = length := by
  induction length generalizing address bytes with
  | zero =>
      simp only [readBytearrayWordHOL] at h
      injection h with hb
      rw [← hb]; rfl
  | succ length ih =>
      simp only [readBytearrayWordHOL] at h
      cases hb : getByte address with
      | none => simp [hb] at h
      | some byte =>
          simp only [hb] at h
          cases hr : readBytearrayWordHOL (byteWidth := byteWidth) (address+1) length getByte with
          | none => rw [hr] at h; simp at h
          | some rest =>
              simp only [hr] at h
              injection h with hbytes
              rw [← hbytes, List.length_cons, ih (address+1) rest hr]

/-- Width-generic port of HOL `byte$get_byte` (`src/n-bit/byteScript.sml:21`).
    That script is part of the HOL standard library rather than the CakeML
    submodule, so this declaration carries no HOL tag.  The byte shift is
    `8 * (w2n address MOD (dimindex DIV 8))`, reversed for big-endian words. -/
def riscvGetByteHOL {width : Nat} [NeZero width] (bigEndian : Bool)
    (address value : RiscV.Word width) : UInt8 :=
  let bytesInWord := width / 8
  let shift :=
    if bigEndian then 8 * ((bytesInWord - 1) - (address.toNat % bytesInWord))
    else 8 * (address.toNat % bytesInWord)
  UInt8.ofNat ((value >>> shift).toNat % 256)

/-- Width-generic port of HOL `byte$byte_align` (`src/n-bit/alignmentScript.sml:23`):
    `byte_align (w : 'a word) = align (LOG2 (dimindex(:'a) DIV 8)) w`, i.e. the
    low `LOG2 (width DIV 8)` bits of the address are cleared.  That script is
    part of the HOL standard library rather than the CakeML submodule, so this
    declaration carries no HOL tag.  Note that this is *not* division by
    `width / 8`: it agrees with `RiscV.panRiscVByteAlign (width / 8)` only when
    `width / 8` is a power of two (e.g. width 64).  For width 24, HOL clears one
    low bit and aligns by 2, whereas dividing by 3 would align by 3. -/
def riscvByteAlignHOL {width : Nat} [NeZero width] (address : RiscV.Word width) :
    RiscV.Word width :=
  let bits := Nat.log2 (width / 8)
  (address >>> bits) <<< bits

/-- Flapjack byte-loader helper following HOL `mem_load_byte_aux_def`
    (`wordSemScript.sml:159`). As in HOL, `memory` is a total
    `'a word -> 'a word_loc` map (Lean `LoopValue` is the `word_loc`
    counterpart) and `domain` is the address set `dm`. Its result carrier is
    `UInt8`, while HOL returns `word8` (`BitVec 8`); this unqualified carrier
    difference prevents an exact tag. The faithful byte-carrier replacement is
    tracked by `flapjack-4ac.5.16.5.4`. -/
def memLoadByteAuxHOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → LoopValue (RiscV.Word width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) : Option UInt8 :=
  let aligned := riscvByteAlignHOL address
  match memory aligned with
  | .loc _ _ => none
  | .word value =>
      if domain aligned then some (riscvGetByteHOL bigEndian address value) else none

/-- Width-generic port of HOL `byte$set_byte` (`src/n-bit/byteScript.sml:28`).
    That script is part of the HOL standard library rather than the CakeML
    submodule, so this declaration carries no HOL tag.  It replaces the byte at
    `byte_index address bigEndian` by `byte`. -/
def riscvSetByteHOL {width : Nat} [NeZero width] (bigEndian : Bool)
    (address value : RiscV.Word width) (byte : UInt8) : RiscV.Word width :=
  let bytesInWord := width / 8
  let index :=
    if bigEndian then 8 * ((bytesInWord - 1) - (address.toNat % bytesInWord))
    else 8 * (address.toNat % bytesInWord)
  let mask := ~~~((BitVec.ofNat width 0xFF) <<< index)
  (value &&& mask) ||| ((BitVec.ofNat width byte.toNat) <<< index)

/-- Flapjack byte-store helper following HOL `mem_store_byte_aux_def`
    (`wordSemScript.sml:171`). As in HOL, `memory` is a total
    `'a word -> 'a word_loc` map and `domain` is the address set `dm`. Its byte
    argument is `UInt8`, while HOL's is `word8` (`BitVec 8`); this declaration is
    untagged pending the faithful carrier replacement tracked by
    `flapjack-4ac.5.16.5.4`. -/
def memStoreByteAuxHOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → LoopValue (RiscV.Word width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool)
    (address : RiscV.Word width) (byte : UInt8) :
    Option (RiscV.Word width → LoopValue (RiscV.Word width)) :=
  let aligned := riscvByteAlignHOL address
  match memory aligned with
  | .word value =>
      if domain aligned then
        let updated := riscvSetByteHOL bigEndian address value byte
        some (fun current => if current = aligned then .word updated else memory current)
      else none
  | _ => none

/-- Flapjack byte-array writer following HOL `write_bytearray_def`
    (`wordSemScript.sml:178`). The argument order and failed-store behavior
    match HOL `write_bytearray a bs m dm be`, but its bytes are `List UInt8`
    rather than HOL `word8 list` (`List (BitVec 8)`). It remains untagged until
    the faithful carrier replacement tracked by `flapjack-4ac.5.16.5.4`. -/
def writeBytearrayHOL {width : Nat} [NeZero width]
    (address : RiscV.Word width) (bytes : List UInt8)
    (memory : RiscV.Word width → LoopValue (RiscV.Word width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) : RiscV.Word width → LoopValue (RiscV.Word width) :=
  match bytes with
  | [] => memory
  | byte :: rest =>
      match memStoreByteAuxHOL
          (writeBytearrayHOL (address + 1) rest memory domain bigEndian)
          domain bigEndian address byte with
      | some updated => updated
      | none => memory

/-- Width-generic port of HOL `byte$word_to_bytes`
    (`src/n-bit/byteScript.sml:450`):
    `word_to_bytes w be = word_to_bytes_aux (dimindex DIV 8) w be`, i.e. the
    `get_byte` of each increasing index.  That script is part of the HOL
    standard library rather than the CakeML submodule, so this declaration
    carries no HOL tag. -/
def riscvWordToBytesHOL {width : Nat} [NeZero width]
    (value : RiscV.Word width) (bigEndian : Bool) : List UInt8 :=
  (List.range (width / 8)).map
    (fun index => riscvGetByteHOL bigEndian (BitVec.ofNat width index) value)

/-- Width-generic port of HOL `byte$word_of_bytes`
    (`src/n-bit/byteScript.sml:197`): fold `set_byte` over the bytes starting at
    `address` and incrementing by one.  HOL standard library, so no HOL tag. -/
def riscvWordOfBytesHOL {width : Nat} [NeZero width]
    (bigEndian : Bool) (address : RiscV.Word width) :
    List UInt8 → RiscV.Word width
  | [] => 0
  | byte :: rest =>
      riscvSetByteHOL bigEndian address
        (riscvWordOfBytesHOL bigEndian (address + 1) rest) byte

/-! FLAPJACK-SPECIFIC (not an exact HOL port).  Runtime helper for CakeML
    `mem_load_def` (`cakeml/pancake/semantics/loopSemScript.sml:64-69`).  HOL
    takes the whole `('a,'ffi) loopSem$state` (`mem_load addr s`) and reads
    `s.memory`/`s.mdomain` (a set), while this helper splits the total memory map
    and the `address -> Prop` domain out as arguments.  Exact whole-state port
    tracked by `flapjack-s6a.3.2.2.1`. -/
def memLoadHOL {width : Nat}
    (memory : RiscV.Word width → LoopValue (RiscV.Word width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (address : RiscV.Word width) : Option (LoopValue (RiscV.Word width)) :=
  if domain address then some (memory address) else none

/-! FLAPJACK-SPECIFIC (not an exact HOL port).  Runtime helper for CakeML
    `mem_store_def` (`cakeml/pancake/semantics/loopSemScript.sml:57-62`).  HOL
    takes and returns the whole `('a,'ffi) loopSem$state`, whereas this helper
    splits memory/domain out and returns the updated total memory map (not the
    state).  Exact whole-state port tracked by `flapjack-s6a.3.2.2.1`. -/
def memStoreHOL {width : Nat}
    (memory : RiscV.Word width → LoopValue (RiscV.Word width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (address : RiscV.Word width) (value : LoopValue (RiscV.Word width)) :
    Option (RiscV.Word width → LoopValue (RiscV.Word width)) :=
  if domain address then
    some (fun current => if current = address then value else memory current)
  else none

/-- Width-generic port of HOL `alignment$aligned` (`src/n-bit/alignmentScript.sml:20`):
    `aligned p w = (align p w = w)`, where `align` clears the low `p` bits, so
    `aligned p w` holds exactly when those low bits are already zero.  HOL
    standard library, so no HOL tag. -/
def riscvAlignedHOL {width : Nat} (p : Nat) (address : RiscV.Word width) : Bool :=
  (address >>> p) <<< p = address

/-- Width-generic exact port of HOL `mem_load_32_def`
    (`cakeml/compiler/backend/semantics/wordSemScript.sml:70-81`).  When the
    address is `aligned 2`, the four bytes at `w`, `w+1`, `w+2`, `w+3` of the
    word stored at `byte_align w` are reassembled into a 32-bit word; `Loc` and
    out-of-domain addresses yield `NONE`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_load_32_def"]
def memLoad32HOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → LoopValue (RiscV.Word width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) : Option (RiscV.Word 32) :=
  if riscvAlignedHOL 2 address then
    let aligned := riscvByteAlignHOL address
    match memory aligned with
    | .loc _ _ => none
    | .word value =>
        if domain aligned then
          some (riscvWordOfBytesHOL bigEndian (0 : RiscV.Word 32)
            [riscvGetByteHOL bigEndian address value,
             riscvGetByteHOL bigEndian (address + 1) value,
             riscvGetByteHOL bigEndian (address + 2) value,
             riscvGetByteHOL bigEndian (address + 3) value])
        else none
  else none

/-- Width-generic exact port of HOL `mem_store_32_def`
    (`cakeml/compiler/backend/semantics/wordSemScript.sml:84-97`).  When the
    address is `aligned 2`, the four bytes of the 32-bit `value` are written at
    `w`, `w+1`, `w+2`, `w+3` of the stored word, leaving every other address
    unchanged; `Loc` and out-of-domain addresses yield `NONE`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "mem_store_32_def"]
def memStore32HOL {width : Nat} [NeZero width]
    (memory : RiscV.Word width → LoopValue (RiscV.Word width))
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width) (value : RiscV.Word 32) :
    Option (RiscV.Word width → LoopValue (RiscV.Word width)) :=
  if riscvAlignedHOL 2 address then
    let aligned := riscvByteAlignHOL address
    match memory aligned with
    | .loc _ _ => none
    | .word stored =>
        if domain aligned then
          let v0 := riscvSetByteHOL bigEndian address stored
            (riscvGetByteHOL bigEndian (0 : RiscV.Word 32) value)
          let v1 := riscvSetByteHOL bigEndian (address + 1) v0
            (riscvGetByteHOL bigEndian (1 : RiscV.Word 32) value)
          let v2 := riscvSetByteHOL bigEndian (address + 2) v1
            (riscvGetByteHOL bigEndian (2 : RiscV.Word 32) value)
          let v3 := riscvSetByteHOL bigEndian (address + 3) v2
            (riscvGetByteHOL bigEndian (3 : RiscV.Word 32) value)
          some (fun current => if current = aligned then .word v3 else memory current)
        else none
  else none

/-! ## `loopSem.get_var_imm` support (untagged)

HOL `get_var_imm_def` (`cakeml/pancake/semantics/loopSemScript.sml:165-167`) is
the two-clause `get_var_imm (Reg n) s = sptree$lookup n s.locals` /
`get_var_imm (Imm w) s = SOME (Word w)` at `'a word_loc` values, with the
operand argument FIRST and the state second. The untagged wrappers below keep
that HOL argument order; the production executable helper `getVarImm`
(`Flapjack/LoopGetVarImm.lean`) is word-carrier polymorphic and state-first, so
the rfl bridge maps between the two orders.

PRECISE STATE-CARRIER GAP (why no `@[hol]` tag): HOL `get_var_imm` quantifies
over the full `loopSem$state` (`loopSemScript.sml:13-27`), whose fields are an
`sptree$num_map` code and locals, a finite-map `5 word |-> word_loc` globals, a
TOTAL `'a word -> 'a word_loc` memory, `mdomain`/`sh_mdomain` sets, and the HOL
FFI state. The Lean carrier `LoopMachineState` represents `code` as an
association list, `memory` as `Option`-valued, `globals`/`locals` as functions,
and `mdomain`/`shMdomain` as Boolean maps, so it is not the exact HOL state
carrier and a whole-state signature over it cannot carry the exact tag. The
exact width-indexed `loopSem$state` carrier and its observational bridge are
tracked in bead `flapjack-pxn.18.5.17.1` (assigned to flapjack-deepseek). These
declarations stay untagged until that carrier exists. -/
def getVarImmHOL {width : Nat} [NeZero width]
    (operand : RegImm (BitVec width)) (state : LoopMachineState (BitVec width) F) :
    Option (LoopValue (BitVec width)) :=
  getVarImm state operand

@[simp] theorem getVarImmHOL_reg {width : Nat} [NeZero width]
    (name : Nat) (state : LoopMachineState (BitVec width) F) :
    getVarImmHOL (.reg name) state = state.locals name := rfl

@[simp] theorem getVarImmHOL_imm {width : Nat} [NeZero width]
    (value : BitVec width) (state : LoopMachineState (BitVec width) F) :
    getVarImmHOL (.imm value) state = some (.word value) := rfl

theorem getVarImmHOL_eq_getVarImm {width : Nat} [NeZero width]
    (operand : RegImm (BitVec width)) (state : LoopMachineState (BitVec width) F) :
    getVarImmHOL operand state = getVarImm state operand := rfl

end Flapjack
