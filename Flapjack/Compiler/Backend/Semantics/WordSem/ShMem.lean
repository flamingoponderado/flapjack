import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Pancake.Semantics.PanSem.ShMemExact
import Flapjack.Pancake.Semantics.LoopSem

/-!
# Exact HOL `wordSem` shared-memory helpers

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml:374-470`
(bead `flapjack-h29l.3`).  It covers `sh_mem_store`, `sh_mem_load`,
`sh_mem_store_byte`, `sh_mem_store16`, `sh_mem_store32`, `sh_mem_load_byte`,
`sh_mem_load16`, `sh_mem_load32`, `sh_mem_set_var`, and `share_inst`.  These
are over the tagged `WordSemStateFiniteExact` and the exact FFI carrier: the
tagged `callFFIHOL` (`call_FFI_def`) and the `asm$memop` carrier
`WordMemOp`.  The carrier translations are those of the `state` port.
HOL types the results of `sh_mem_store*`, `sh_mem_set_var` and `share_inst`
as `'d result option`, with `'d` independent of the state's word type `'a`
(no clause returns a word in the result).  Here that is a separate result
width `rw` with `[NeZero rw]`.

The HOL standard-library byte helpers are the untagged renderings used by the
panSem/loopSem shared-memory ports:
* `word_to_bytes` is `panWordToBytesHOL`;
* `word_of_bytes` is `panWordOfBytesHOL`;
* `byte_align` is `riscvByteAlignHOL`;
* `get_byte` is `getByteHOL8`.
-/

namespace Flapjack

namespace WordSemShMemSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged state helpers of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemShMemSupport

namespace WordSemStateFiniteExact

/-- Exact HOL `sh_mem_store_def` (`wordSemScript.sml:374-382`).  If `a IN
    s.sh_mdomain`, call `call_FFI s.ffi (SharedMem MappedWrite) [0w]
    (word_to_bytes w F ++ word_to_bytes a F)`.  `FFI_final` gives
    `(SOME (FinalFFI outcome), flush_state T s)`, and `FFI_return` installs
    the new FFI state.  Outside the domain the result is `(SOME Error, s)`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shMemStore {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type}
    (a w : BitVec width) (s : WordSemStateFiniteExact width C F) :
    Option (WordSemResult rw) × WordSemStateFiniteExact width C F :=
  if s.shMdomain a then
    match callFFIHOL s.ffi (.sharedMem .mappedWrite) [0]
        (panWordToBytesHOL w false ++ panWordToBytesHOL a false) with
    | .final outcome => (some (.finalFfi outcome), flushState true s)
    | .ret newFfi _ => (none, { s with ffi := newFfi })
  else (some .error, s)

/-- Exact HOL `sh_mem_load_def` (`wordSemScript.sml:384-390`): `SOME (call_FFI
    s.ffi (SharedMem MappedRead) [0w] (word_to_bytes a F))` when `a IN
    s.sh_mdomain`, else `NONE`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shMemLoad {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : BitVec width) (s : WordSemStateFiniteExact width C F) : Option (HolFfiResult F) :=
  if s.shMdomain a then
    some (callFFIHOL s.ffi (.sharedMem .mappedRead) [0] (panWordToBytesHOL a false))
  else none

/-- Exact HOL `sh_mem_store_byte_def` (`wordSemScript.sml:392-400`).  The domain
    test is on `byte_align a`, the configuration is `[1w]`, and the payload is
    `[get_byte 0w w F] ++ word_to_bytes a F`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shMemStoreByte {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type}
    (a w : BitVec width) (s : WordSemStateFiniteExact width C F) :
    Option (WordSemResult rw) × WordSemStateFiniteExact width C F :=
  if s.shMdomain (riscvByteAlignHOL a) then
    match callFFIHOL s.ffi (.sharedMem .mappedWrite) [1]
        ([getByteHOL8 0 w false] ++ panWordToBytesHOL a false) with
    | .final outcome => (some (.finalFfi outcome), flushState true s)
    | .ret newFfi _ => (none, { s with ffi := newFfi })
  else (some .error, s)

/-- Exact HOL `sh_mem_store16_def` (`wordSemScript.sml:402-410`).  The domain
    test is on `byte_align a`, the configuration is `[2w]`, and the payload is
    `TAKE 2 (word_to_bytes w F) ++ word_to_bytes a F`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shMemStore16 {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type}
    (a w : BitVec width) (s : WordSemStateFiniteExact width C F) :
    Option (WordSemResult rw) × WordSemStateFiniteExact width C F :=
  if s.shMdomain (riscvByteAlignHOL a) then
    match callFFIHOL s.ffi (.sharedMem .mappedWrite) [2]
        ((panWordToBytesHOL w false).take 2 ++ panWordToBytesHOL a false) with
    | .final outcome => (some (.finalFfi outcome), flushState true s)
    | .ret newFfi _ => (none, { s with ffi := newFfi })
  else (some .error, s)

/-- Exact HOL `sh_mem_store32_def` (`wordSemScript.sml:412-420`).  The domain
    test is on `byte_align a`, the configuration is `[4w]`, and the payload is
    `TAKE 4 (word_to_bytes w F) ++ word_to_bytes a F`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shMemStore32 {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type}
    (a w : BitVec width) (s : WordSemStateFiniteExact width C F) :
    Option (WordSemResult rw) × WordSemStateFiniteExact width C F :=
  if s.shMdomain (riscvByteAlignHOL a) then
    match callFFIHOL s.ffi (.sharedMem .mappedWrite) [4]
        ((panWordToBytesHOL w false).take 4 ++ panWordToBytesHOL a false) with
    | .final outcome => (some (.finalFfi outcome), flushState true s)
    | .ret newFfi _ => (none, { s with ffi := newFfi })
  else (some .error, s)

/-- Exact HOL `sh_mem_load_byte_def` (`wordSemScript.sml:422-428`): as
    `sh_mem_load`, with the domain test on `byte_align a` and configuration
    `[1w]`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shMemLoadByte {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : BitVec width) (s : WordSemStateFiniteExact width C F) : Option (HolFfiResult F) :=
  if s.shMdomain (riscvByteAlignHOL a) then
    some (callFFIHOL s.ffi (.sharedMem .mappedRead) [1] (panWordToBytesHOL a false))
  else none

/-- Exact HOL `sh_mem_load16_def` (`wordSemScript.sml:430-436`): as
    `sh_mem_load`, with the domain test on `byte_align a` and configuration
    `[2w]`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shMemLoad16 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : BitVec width) (s : WordSemStateFiniteExact width C F) : Option (HolFfiResult F) :=
  if s.shMdomain (riscvByteAlignHOL a) then
    some (callFFIHOL s.ffi (.sharedMem .mappedRead) [2] (panWordToBytesHOL a false))
  else none

/-- Exact HOL `sh_mem_load32_def` (`wordSemScript.sml:438-444`): as
    `sh_mem_load`, with the domain test on `byte_align a` and configuration
    `[4w]`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shMemLoad32 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (a : BitVec width) (s : WordSemStateFiniteExact width C F) : Option (HolFfiResult F) :=
  if s.shMdomain (riscvByteAlignHOL a) then
    some (callFFIHOL s.ffi (.sharedMem .mappedRead) [4] (panWordToBytesHOL a false))
  else none

/-- Exact HOL `sh_mem_set_var_def` (`wordSemScript.sml:447-451`).
    * `SOME (FFI_final outcome)` gives `(SOME (FinalFFI outcome), flush_state T
      s)`.
    * `SOME (FFI_return new_ffi new_bytes)` gives `(NONE, set_var v (Word
      (word_of_bytes F 0w new_bytes)) (s with ffi := new_ffi))`.
    * `NONE` gives `(SOME Error, s)`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shMemSetVar {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type} :
    Option (HolFfiResult F) → Nat → WordSemStateFiniteExact width C F →
      Option (WordSemResult rw) × WordSemStateFiniteExact width C F
  | some (.final outcome), _, s => (some (.finalFfi outcome), flushState true s)
  | some (.ret newFfi newBytes), v, s =>
      (none, setVar v (.word (panWordOfBytesHOL false 0 newBytes)) { s with ffi := newFfi })
  | none, _, s => (some .error, s)

/-- Exact HOL `share_inst_def` (`wordSemScript.sml:453-470`).  The loads pass
    the matching `sh_mem_load*` result to `sh_mem_set_var v`.  The stores
    require `get_var v s = SOME (Word v)` and call the matching
    `sh_mem_store*`, and give `(SOME Error, s)` otherwise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def shareInst {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type} :
    WordMemOp → Nat → BitVec width → WordSemStateFiniteExact width C F →
      Option (WordSemResult rw) × WordSemStateFiniteExact width C F
  | .load, v, ad, s => shMemSetVar (shMemLoad ad s) v s
  | .load8, v, ad, s => shMemSetVar (shMemLoadByte ad s) v s
  | .load16, v, ad, s => shMemSetVar (shMemLoad16 ad s) v s
  | .load32, v, ad, s => shMemSetVar (shMemLoad32 ad s) v s
  | .store, v, ad, s =>
      match getVar v s with
      | some (.word w) => shMemStore ad w s
      | _ => (some .error, s)
  | .store8, v, ad, s =>
      match getVar v s with
      | some (.word w) => shMemStoreByte ad w s
      | _ => (some .error, s)
  | .store16, v, ad, s =>
      match getVar v s with
      | some (.word w) => shMemStore16 ad w s
      | _ => (some .error, s)
  | .store32, v, ad, s =>
      match getVar v s with
      | some (.word w) => shMemStore32 ad w s
      | _ => (some .error, s)

end WordSemStateFiniteExact

end Flapjack
