import Flapjack.Pancake.Semantics.LoopSemStateExact
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.Pancake.Semantics.PanSem.ShMemExact

/-!
# Exact loopSem shared-memory helpers

HOL `sh_mem_load_def`, `sh_mem_store_def` and `sh_mem_op_def`
(`cakeml/pancake/semantics/loopSemScript.sml:198-264`) over
`LoopSemStateFiniteExact` and the exact FFI carrier (`callFFIHOL`, tagged
`call_FFI_def`).  Direct HOL rows are checked by
`Flapjack.Test.LoopSemShMemExactParity` (`flapjack-pxgp.4`).
-/

namespace Flapjack
namespace LoopSemStateFiniteExact

namespace LoopShMemFiniteSupport

/-- Local same-module witness for the canonical finite-support
`LoopSemStateFiniteExact` carrier used by the qualified shared-memory ports in
this module. It re-exports the checked roundtrip witness from the owning
carrier module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopShMemFiniteSupport

/-- Exact HOL `sh_mem_load_def` (`loopSemScript.sml:198-215`).  For `nb = 0` the
    address itself, otherwise its `byte_align`, must be in `sh_mdomain`; then
    `call_FFI s.ffi (SharedMem MappedRead) [n2w nb] (word_to_bytes addr F)`:
    `FFI_final` gives `FinalFFI` with `call_env []`, `FFI_return` writes
    `Word (word_of_bytes F 0w new_bytes)` to `v` and installs the new FFI state.
    Outside the domain the result is `Error`.  The HOL standard-library byte
    helpers are the untagged renderings `panWordToBytesHOL`, `panWordOfBytesHOL`
    and `riscvByteAlignHOL`. The full state carrier's sole `|->` field,
    `globals`, is recorded by the finite-support qualifier and local canonical
    witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "sh_mem_load_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
def shMemLoad {width : Nat} [NeZero width] {F : Type}
    (v : Nat) (addr : BitVec width) (nb : Nat) (s : LoopSemStateFiniteExact width F) :
    Option (LoopResultExact width) × LoopSemStateFiniteExact width F :=
  if nb = 0 then
    (if s.shMdomain addr then
      (match callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL addr false) with
       | .final outcome => (some (.finalFfi outcome), callEnv [] s)
       | .ret newFfi newBytes =>
           (none, { setVar v (.word (panWordOfBytesHOL false 0 newBytes)) s with ffi := newFfi }))
     else (some .error, s))
  else
    (if s.shMdomain (riscvByteAlignHOL addr) then
      (match callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb]
          (panWordToBytesHOL addr false) with
       | .final outcome => (some (.finalFfi outcome), callEnv [] s)
       | .ret newFfi newBytes =>
           (none, { setVar v (.word (panWordOfBytesHOL false 0 newBytes)) s with ffi := newFfi }))
     else (some .error, s))

/-- Exact HOL `sh_mem_store_def` (`loopSemScript.sml:217-240`).  `v` must hold a
    `Word w`; the domain test is as for `sh_mem_load`; the payload is
    `word_to_bytes w F ++ word_to_bytes addr F` for `nb = 0` and
    `TAKE nb (word_to_bytes w F) ++ word_to_bytes addr F` otherwise, sent with
    `SharedMem MappedWrite`; `FFI_return` installs only the new FFI state. The
    full state carrier's `globals` `|->` field is recorded by the finite-support
    qualifier and local canonical witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "sh_mem_store_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
def shMemStore {width : Nat} [NeZero width] {F : Type}
    (v : Nat) (addr : BitVec width) (nb : Nat) (s : LoopSemStateFiniteExact width F) :
    Option (LoopResultExact width) × LoopSemStateFiniteExact width F :=
  match sptLookup v s.locals with
  | some (.word w) =>
      if nb = 0 then
        (if s.shMdomain addr then
          (match callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
              (panWordToBytesHOL w false ++ panWordToBytesHOL addr false) with
           | .final outcome => (some (.finalFfi outcome), callEnv [] s)
           | .ret newFfi _ => (none, { s with ffi := newFfi }))
         else (some .error, s))
      else
        (if s.shMdomain (riscvByteAlignHOL addr) then
          (match callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
              ((panWordToBytesHOL w false).take nb ++ panWordToBytesHOL addr false) with
           | .final outcome => (some (.finalFfi outcome), callEnv [] s)
           | .ret newFfi _ => (none, { s with ffi := newFfi }))
         else (some .error, s))
  | _ => (some .error, s)

/-- Exact HOL `sh_mem_op_def` (`loopSemScript.sml:255-264`): `Load`/`Store` use
    byte count `0`, `Load8`/`Store8` `1`, `Load16`/`Store16` `2`,
    `Load32`/`Store32` `4`. The full state carrier's `globals` `|->` field is
    recorded by the finite-support qualifier and local canonical witness. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "sh_mem_op_def"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
def shMemOp {width : Nat} [NeZero width] {F : Type} :
    WordMemOp → Nat → BitVec width → LoopSemStateFiniteExact width F →
      Option (LoopResultExact width) × LoopSemStateFiniteExact width F
  | .load, r, ad, s => shMemLoad r ad 0 s
  | .store, r, ad, s => shMemStore r ad 0 s
  | .load8, r, ad, s => shMemLoad r ad 1 s
  | .store8, r, ad, s => shMemStore r ad 1 s
  | .load16, r, ad, s => shMemLoad r ad 2 s
  | .store16, r, ad, s => shMemStore r ad 2 s
  | .load32, r, ad, s => shMemLoad r ad 4 s
  | .store32, r, ad, s => shMemStore r ad 4 s

end LoopSemStateFiniteExact
end Flapjack
