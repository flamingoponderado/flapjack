import Flapjack.Compiler.Backend.Semantics.StackSem.StateOps
import Flapjack.Compiler.Backend.Semantics.WordSem
import Flapjack.Pancake.Semantics.LoopSem
import Flapjack.FfiHOL

/-! Source-matched `evaluate_def` FFI clause fragment over the exact StackSem
state/result carriers. It is deliberately untagged: this partial dispatch helper
is not the total HOL `evaluate_def` definition, and because no total recursive
`evaluate` exists yet the outer `NONE` means this module does not handle the
constructor, so it never substitutes `Error` for an unported clause. The FFI
clause does not recurse, so no recursive-evaluation parameter is needed. The
assembled evaluator route is tracked by `flapjack-y19g`
(bead `flapjack-y19g.14.4`).

Counterpart of `cakeml/compiler/backend/semantics/stackSemScript.sml:951-971`.
The four word registers are read in HOL order, both byte arrays are read with
the exact `read_bytearray`/`mem_load_byte_aux` ports, and the exact
`call_FFI` port decides the branch: `FFI_final` returns
`(SOME (FinalFFI outcome), s)` with the state unchanged, while `FFI_return`
writes the returned bytes back with the exact `write_bytearray` port, restricts
`s.regs` with HOL `DRESTRICT s.regs s.ffi_save_regs`, empties `fp_regs`, and
installs the new FFI state. The `returnAddress` field is unused by the HOL
clause. -/

namespace Flapjack.StackSemFfi

open StackSemStateOps Compiler.Backend.StackLang

/-- Flapjack-only helper for HOL `DRESTRICT fm keep`
(`finite_mapScript.sml:715`): `DRESTRICT` keeps exactly the keys in its set
argument, so a key survives when the membership predicate holds and is dropped
otherwise. This is not a tagged HOL declaration; it renders the finite-map
restriction `s.regs` uses to install HOL `DRESTRICT s.regs s.ffi_save_regs`. The
support of the result is a subset of the source support, so the original
witness still covers it. -/
def restrictIn {α β : Type} (m : HolFiniteMapExact α β) (keep : α → Bool) :
    HolFiniteMapExact α β where
  lookup key := if keep key then m.lookup key else none
  finiteSupport := by
    obtain ⟨keys, hkeys⟩ := m.finiteSupport
    refine ⟨keys, ?_⟩
    intro key hkey
    apply hkeys key
    by_cases h : keep key
    · simpa [h] using hkey
    · simp [h] at hkey

/-- The HOL `evaluate (FFI ffi_index ptr len ptr2 len2 ret, s)` branch
(`cakeml/compiler/backend/semantics/stackSemScript.sml:951-971`; the Lean
constructor is `.ffi function configuration configurationLength array
arrayLength returnAddress`). It reads `configurationLength`, `configuration`,
`arrayLength`, and `array` in that HOL order; all four must be `Word`, else
`(SOME Error, s)`. It reads the two byte arrays with the exact `read_bytearray`
port over `mem_load_byte_aux`; a read miss gives `(SOME Error, s)`. The exact
`call_FFI` port then decides: `FFI_final` gives `(SOME (FinalFFI outcome), s)`,
`FFI_return` gives `(NONE, s with memory := write_bytearray array new_bytes ...,
regs := DRESTRICT s.regs s.ffi_save_regs, fp_regs := FEMPTY, ffi := new_ffi)`. -/
def evaluateFfi {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) :
    Option (Option (StackSemResult width) × StackSemStateFiniteExact width C F) :=
  match program with
  | .ffi function configuration configurationLength array arrayLength _returnAddress =>
      some (match getVar configurationLength s, getVar configuration s,
                   getVar arrayLength s, getVar array s with
        | some (.word w), some (.word w2), some (.word w3), some (.word w4) =>
            match readBytearrayWordHOL w2 w.toNat (memLoadByteAuxExact s.memory s.mdomain s.be),
                  readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
            | some bytes, some bytes2 =>
                match callFFIHOL s.ffi (.extCall function) bytes bytes2 with
                | .final outcome => (some (.finalFFI outcome), s)
                | .ret newFfi newBytes =>
                    (none, { s with
                      memory := writeBytearrayExact w4 newBytes s.memory s.mdomain s.be
                      regs := restrictIn s.regs s.ffiSaveRegs
                      fpRegs := HolFiniteMapExact.empty
                      ffi := newFfi })
            | _, _ => (some .error, s)
        | _, _, _, _ => (some .error, s))
  | _ => none

/-- Flapjack assembly equation for the source FFI clause, exposing the exact
register reads, the two byte-array reads, the `call_FFI` dispatch, and both
return shapes. -/
theorem evaluateFfi_ffi {width : Nat} [NeZero width] {C F : Type}
    (function : Flapjack.Basis.Pure.MlString.MlString)
    (configuration configurationLength array arrayLength returnAddress : Nat)
    (s : StackSemStateFiniteExact width C F) :
    evaluateFfi (.ffi function configuration configurationLength array arrayLength returnAddress) s =
      some (match getVar configurationLength s, getVar configuration s,
                   getVar arrayLength s, getVar array s with
        | some (.word w), some (.word w2), some (.word w3), some (.word w4) =>
            match readBytearrayWordHOL w2 w.toNat (memLoadByteAuxExact s.memory s.mdomain s.be),
                  readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
            | some bytes, some bytes2 =>
                match callFFIHOL s.ffi (.extCall function) bytes bytes2 with
                | .final outcome => (some (.finalFFI outcome), s)
                | .ret newFfi newBytes =>
                    (none, { s with
                      memory := writeBytearrayExact w4 newBytes s.memory s.mdomain s.be
                      regs := restrictIn s.regs s.ffiSaveRegs
                      fpRegs := HolFiniteMapExact.empty
                      ffi := newFfi })
            | _, _ => (some .error, s)
        | _, _, _, _ => (some .error, s)) := rfl

end Flapjack.StackSemFfi
