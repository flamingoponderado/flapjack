import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.WordSem.ShMem

/-!
# Exact HOL StackSem shared-memory helpers

Counterpart of `cakeml/compiler/backend/semantics/stackSemScript.sml:194-308`.
It covers `sh_mem_store`, `sh_mem_load`, `sh_mem_store_byte`, `sh_mem_store16`,
`sh_mem_store32`, `sh_mem_load_byte`, `sh_mem_load16`, `sh_mem_load32`, and the
`sh_mem_op` dispatch over the tagged `StackSemStateFiniteExact` and the exact
FFI carrier (`callFFIHOL`/`HolFfiState`/`HolFfiResult`) and the shared memop
carrier `WordMemOp` (tagged `memop`).

The stackSem helpers differ from the wordSem ones: each takes a register `r`,
reads it with `get_var`, and installs a successful load into `s.regs` with
`word_of_bytes` instead of returning the FFI result. Stores encode the register
word with `word_to_bytes`; the sized forms guard on `byte_align a` and send
`[get_byte 0w w F] ++ word_to_bytes a F` (byte) or the `TAKE nb` prefix (16/32).
A terminal `FFI_final` leaves the state unchanged (no `flush_state`).

The HOL standard-library byte helpers are the untagged renderings shared with
the reviewed panSem/loopSem/wordSem shared-memory ports:
* `word_to_bytes` is `panWordToBytesHOL`;
* `word_of_bytes` is `panWordOfBytesHOL`;
* `byte_align` is `riscvByteAlignHOL`;
* `get_byte` is `getByteHOL8`.
-/

namespace Flapjack

namespace StackSemShMemSupport

/-- Same-module canonical finite-support witness for the `regs`/`fpRegs`/`store`
    fields named by the tagged state helpers of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

end StackSemShMemSupport

namespace StackSemShMem

open StackSemStateOps

/-- Exact HOL `sh_mem_store_def` (`stackSemScript.sml:194-205`).  The named
    register must hold a word; if `a IN s.sh_mdomain`, call
    `call_FFI s.ffi (SharedMem MappedWrite) [0w] (word_to_bytes w F ++
    word_to_bytes a F)`.  `FFI_final` gives `(SOME (FinalFFI outcome), s)`
    (state unchanged), `FFI_return` installs only the new FFI state, and a
    domain miss or non-word register gives `(SOME Error, s)`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_store_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def shMemStore {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r : Nat) (address : BitVec width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match getVar r s with
  | some (.word w) =>
      if s.shMdomain address then
        match callFFIHOL s.ffi (.sharedMem .mappedWrite) [0]
            (panWordToBytesHOL w false ++ panWordToBytesHOL address false) with
        | .final outcome => (some (.finalFFI outcome), s)
        | .ret newFfi _ => (none, { s with ffi := newFfi })
      else (some .error, s)
  | _ => (some .error, s)

/-- Exact HOL `sh_mem_load_def` (`stackSemScript.sml:207-219`).  If
    `a IN s.sh_mdomain`, call `call_FFI s.ffi (SharedMem MappedRead) [0w]
    (word_to_bytes a F)`.  `FFI_final` gives `(SOME (FinalFFI outcome), s)`;
    `FFI_return` installs `word_of_bytes F 0w new_bytes` into `r` and the new
    FFI state; a domain miss gives `(SOME Error, s)`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_load_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def shMemLoad {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r : Nat) (address : BitVec width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if s.shMdomain address then
    match callFFIHOL s.ffi (.sharedMem .mappedRead) [0] (panWordToBytesHOL address false) with
    | .final outcome => (some (.finalFFI outcome), s)
    | .ret newFfi newBytes =>
        (none, { s with
                  regs := s.regs.updateEq (r, .word (panWordOfBytesHOL false 0 newBytes))
                  ffi := newFfi })
  else (some .error, s)

/-- Exact HOL `sh_mem_store_byte_def` (`stackSemScript.sml:221-232`).  The
    domain test is on `byte_align a`, the configuration is `[1w]`, and the
    payload is `[get_byte 0w w F] ++ word_to_bytes a F`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_store_byte_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def shMemStoreByte {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r : Nat) (address : BitVec width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match getVar r s with
  | some (.word w) =>
      if s.shMdomain (riscvByteAlignHOL address) then
        match callFFIHOL s.ffi (.sharedMem .mappedWrite) [1]
            ([getByteHOL8 0 w false] ++ panWordToBytesHOL address false) with
        | .final outcome => (some (.finalFFI outcome), s)
        | .ret newFfi _ => (none, { s with ffi := newFfi })
      else (some .error, s)
  | _ => (some .error, s)

/-- Exact HOL `sh_mem_store16_def` (`stackSemScript.sml:234-245`).  The domain
    test is on `byte_align a`, the configuration is `[2w]`, and the payload is
    `TAKE 2 (word_to_bytes w F) ++ word_to_bytes a F`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_store16_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def shMemStore16 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r : Nat) (address : BitVec width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match getVar r s with
  | some (.word w) =>
      if s.shMdomain (riscvByteAlignHOL address) then
        match callFFIHOL s.ffi (.sharedMem .mappedWrite) [2]
            ((panWordToBytesHOL w false).take 2 ++ panWordToBytesHOL address false) with
        | .final outcome => (some (.finalFFI outcome), s)
        | .ret newFfi _ => (none, { s with ffi := newFfi })
      else (some .error, s)
  | _ => (some .error, s)

/-- Exact HOL `sh_mem_store32_def` (`stackSemScript.sml:247-258`).  The domain
    test is on `byte_align a`, the configuration is `[4w]`, and the payload is
    `TAKE 4 (word_to_bytes w F) ++ word_to_bytes a F`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_store32_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def shMemStore32 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r : Nat) (address : BitVec width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match getVar r s with
  | some (.word w) =>
      if s.shMdomain (riscvByteAlignHOL address) then
        match callFFIHOL s.ffi (.sharedMem .mappedWrite) [4]
            ((panWordToBytesHOL w false).take 4 ++ panWordToBytesHOL address false) with
        | .final outcome => (some (.finalFFI outcome), s)
        | .ret newFfi _ => (none, { s with ffi := newFfi })
      else (some .error, s)
  | _ => (some .error, s)

/-- Exact HOL `sh_mem_load_byte_def` (`stackSemScript.sml:260-271`): as
    `sh_mem_load`, with the domain test on `byte_align a` and configuration
    `[1w]`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_load_byte_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def shMemLoadByte {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r : Nat) (address : BitVec width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if s.shMdomain (riscvByteAlignHOL address) then
    match callFFIHOL s.ffi (.sharedMem .mappedRead) [1] (panWordToBytesHOL address false) with
    | .final outcome => (some (.finalFFI outcome), s)
    | .ret newFfi newBytes =>
        (none, { s with
                  regs := s.regs.updateEq (r, .word (panWordOfBytesHOL false 0 newBytes))
                  ffi := newFfi })
  else (some .error, s)

/-- Exact HOL `sh_mem_load16_def` (`stackSemScript.sml:273-284`): as
    `sh_mem_load`, with the domain test on `byte_align a` and configuration
    `[2w]`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_load16_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def shMemLoad16 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r : Nat) (address : BitVec width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if s.shMdomain (riscvByteAlignHOL address) then
    match callFFIHOL s.ffi (.sharedMem .mappedRead) [2] (panWordToBytesHOL address false) with
    | .final outcome => (some (.finalFFI outcome), s)
    | .ret newFfi newBytes =>
        (none, { s with
                  regs := s.regs.updateEq (r, .word (panWordOfBytesHOL false 0 newBytes))
                  ffi := newFfi })
  else (some .error, s)

/-- Exact HOL `sh_mem_load32_def` (`stackSemScript.sml:286-297`): as
    `sh_mem_load`, with the domain test on `byte_align a` and configuration
    `[4w]`. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_load32_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def shMemLoad32 {width : Nat} [NeZero width] {C : Type} {F : Type}
    (r : Nat) (address : BitVec width) (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  if s.shMdomain (riscvByteAlignHOL address) then
    match callFFIHOL s.ffi (.sharedMem .mappedRead) [4] (panWordToBytesHOL address false) with
    | .final outcome => (some (.finalFFI outcome), s)
    | .ret newFfi newBytes =>
        (none, { s with
                  regs := s.regs.updateEq (r, .word (panWordOfBytesHOL false 0 newBytes))
                  ffi := newFfi })
  else (some .error, s)

/-- Exact HOL `sh_mem_op_def` (`stackSemScript.sml:299-308`): dispatch the eight
    shared-memory operators to `sh_mem_load`/`sh_mem_store` and their sized
    forms, clause for clause. -/
@[hol "cakeml/compiler/backend/semantics/stackSemScript.sml" "sh_mem_op_def"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
def shMemOp {width : Nat} [NeZero width] {C : Type} {F : Type}
    (operator : WordMemOp) (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    Option (StackSemResult width) × StackSemStateFiniteExact width C F :=
  match operator with
  | .load => shMemLoad r address s
  | .store => shMemStore r address s
  | .load8 => shMemLoadByte r address s
  | .store8 => shMemStoreByte r address s
  | .load16 => shMemLoad16 r address s
  | .store16 => shMemStore16 r address s
  | .load32 => shMemLoad32 r address s
  | .store32 => shMemStore32 r address s

end StackSemShMem

end Flapjack
