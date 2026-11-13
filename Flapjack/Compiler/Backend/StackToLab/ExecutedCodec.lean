module

public import Flapjack.Lab
public import Flapjack.Compiler.Backend.StackToLab.Native
public import Flapjack.Basis.Pure.MlString

@[expose] public section
/-!
# Supported native Lab output at the executable boundary

Flapjack-specific interface infrastructure for bead oie1, a prerequisite of
52bq.1. None of these codecs or recovery theorems has a HOL original: they
connect the reviewed native Stack-to-Lab output carriers to the independent
executable `Flapjack.Lab` carriers, without asserting pass or target semantics.

Every successful conversion has an independently defined inverse that recovers
the entire native input. Register/operand order, word values and widths, labels,
byte caches, lengths, section numbers, and byte-string names are preserved.
HOL `asmSemScript.sml:95-100` gives AddCarry r1 r2 r3 r4 its positional meaning
(sum into r1, carry into r4); the codec uses those same positions in the executed
cakeAddCarry constructor rather than permuting descriptive native field names.

The production arithmetic carrier represents all eight native arithmetic
constructors, including AddOverflow/SubOverflow with their positional flag
register. Native FP and direct word-valued Jump/JumpCmp/Call/Loc still have no
executed counterpart, and those conversions return none.
Native symbolic LabAsm constructors all have counterparts, but their native
position word has no executed field: nonzero positions are rejected, never
silently dropped. The emitted Stack-to-Lab definitions set that field to zero.
Inverse codecs accept canonical images and reject unrelated executed extensions.

MlString names are decoded character by character from exact 8-bit bytes, using
the reviewed MlString functions. The reverse checks every character is below
256 before conversion, so it cannot truncate a non-byte character. Native names
roundtrip unconditionally; a successful String decode also roundtrips, and the
forward name map is injective. Current executed FFI service/index lookup uses
String equality only (RiscV/Ffi.lean:26-38), with no UTF-8 serialization here.
This is a carrier correspondence, not an FFI transition-equivalence theorem.

The runtime-image native removal/section boundary and machine-word CSE key
routes now use these supported codecs. Source-input coverage and source/target
semantic preservation remain separately tracked on 52bq.1 and the production
inventory beads. No performance exception or full compiler correctness claim
is made by this module.
-/

namespace Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem

-- Flapjack-only interface infrastructure: these codecs have no HOL original.
-- Preserve the source constructor's positional operands, regardless of the
-- descriptive local field names. HOL AddCarry r1 r2 r3 r4 updates r1 and r4.

-- Native Skip is retained as the executed tick payload; constants remain words.

def refToExecuted : Lab → LabRef
  | .lab sectionId label => ⟨sectionId, label⟩
def refFromExecuted (reference : LabRef) : Lab :=
  .lab reference.sectionId reference.label
/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
@[simp] theorem ref_recover (native : Lab) :
    refFromExecuted (refToExecuted native) = native := by
  cases native <;> rfl

-- Both directions expose their byte boundary; the reverse never truncates a character.
def nameToExecuted (native : Basis.Pure.MlString.MlString) : String :=
  Basis.Pure.MlString.toStringOfBytes native

def nameFromExecuted? (executed : String) : Option Basis.Pure.MlString.MlString :=
  if executed.toList.all (fun c => decide (c.toNat < 256)) then
    some (Basis.Pure.MlString.ofString executed)
  else none

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem nameToExecuted_byte_range (native : Basis.Pure.MlString.MlString) :
    (nameToExecuted native).toList.all (fun c => decide (c.toNat < 256)) = true := by
  rw [List.all_eq_true]
  intro character member
  simp only [nameToExecuted, Basis.Pure.MlString.toStringOfBytes,
    String.toList_ofList, List.mem_map] at member
  rcases member with ⟨byte, _, rfl⟩
  simpa only [Basis.Pure.MlString.ofNat_toNat_char, decide_eq_true_eq] using byte.isLt

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem name_recover (native : Basis.Pure.MlString.MlString) :
    nameFromExecuted? (nameToExecuted native) = some native := by
  rw [nameFromExecuted?, nameToExecuted_byte_range]
  simp [nameToExecuted, Basis.Pure.MlString.ofString_toStringOfBytes]

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem name_from_recover (executed : String) (native : Basis.Pure.MlString.MlString)
    (decoded : nameFromExecuted? executed = some native) :
    nameToExecuted native = executed := by
  by_cases ranged : executed.toList.all (fun c => decide (c.toNat < 256)) = true
  · simp only [nameFromExecuted?, ite_eq_left ranged, Option.some.injEq] at decoded
    subst native
    have bytes : ∀ c ∈ executed.toList, c.toNat < 256 := by
      intro character member
      simpa only [decide_eq_true_eq] using (List.all_eq_true.mp ranged character member)
    exact Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes executed bytes
  · simp only [nameFromExecuted?, ite_eq_right ranged] at decoded
    cases decoded

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem nameToExecuted_injective : Function.Injective nameToExecuted := by
  intro first second equal
  have recovered := congrArg nameFromExecuted? equal
  simpa only [name_recover, Option.some.injEq] using recovered

def labAsmToExecuted {width : Nat} [NeZero width] :
    AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString →
      LabAsm (BitVec width)
  | .jump target => .jump (refToExecuted target)
  | .jumpCmp op register right target =>
      .jumpCmp op register right.toWordRegImm (refToExecuted target)
  | .call target => .call (refToExecuted target)
  | .locValue register target => .locValue register (refToExecuted target)
  | .callFFI name => .callFfi (nameToExecuted name)
  | .install => .install
  | .halt => .halt

def labAsmFromExecuted? {width : Nat} [NeZero width] :
    LabAsm (BitVec width) →
      Option (AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString)
  | .jump target => some (.jump (refFromExecuted target))
  | .jumpCmp op register right target =>
      some (.jumpCmp op register (HolRegImm.ofWordRegImm right) (refFromExecuted target))
  | .call target => some (.call (refFromExecuted target))
  | .locValue register target => some (.locValue register (refFromExecuted target))
  | .callFfi name => (nameFromExecuted? name).map AsmWithLab.callFFI
  | .install => some .install
  | .halt => some .halt
  | .linkValue _ | .return _ | .heapAlloc _ => none

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem labAsm_recover {width : Nat} [NeZero width]
    (native : AsmWithLab HolCmp (HolRegImm width) Basis.Pure.MlString.MlString) :
    labAsmFromExecuted? (labAsmToExecuted native) = some native := by
  cases native <;> simp [labAsmToExecuted, labAsmFromExecuted?,
    name_recover]

end Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
