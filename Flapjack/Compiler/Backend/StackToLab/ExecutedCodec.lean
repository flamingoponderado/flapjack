import Flapjack.Lab
import Flapjack.Compiler.Backend.StackToLab.Native
import Flapjack.Basis.Pure.MlString
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
def arithToExecuted? {width : Nat} [NeZero width] :
    HolArith width → Option (WordArith (BitVec width))
  | .binop op d l r => some (.binOp op d l r.toWordRegImm)
  | .shift op d l r => some (.shift op d l r.toWordRegImm)
  | .div d l r => some (.div d l r)
  | .longMul d1 d2 l r => some (.longMul d1 d2 l r)
  | .longDiv d1 d2 l r q => some (.longDiv d1 d2 l r q)
  | .addCarry r1 r2 r3 r4 => some (.cakeAddCarry r1 r2 r3 r4)
  | .addOverflow d l r flag => some (.addOverflow d l r flag)
  | .subOverflow d l r flag => some (.subOverflow d l r flag)

def arithFromExecuted? {width : Nat} [NeZero width] :
    WordArith (BitVec width) → Option (HolArith width)
  | .binOp op d l r => some (.binop op d l (HolRegImm.ofWordRegImm r))
  | .shift op d l r => some (.shift op d l (HolRegImm.ofWordRegImm r))
  | .div d l r => some (.div d l r)
  | .longMul d1 d2 l r => some (.longMul d1 d2 l r)
  | .longDiv d1 d2 l r q => some (.longDiv d1 d2 l r q)
  | .cakeAddCarry r1 r2 r3 r4 => some (.addCarry r1 r2 r3 r4)
  | .addOverflow d l r flag => some (.addOverflow d l r flag)
  | .subOverflow d l r flag => some (.subOverflow d l r flag)
  | .addCarry _ _ _ _ _ => none

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem arith_recover {width : Nat} [NeZero width]
    (native : HolArith width) (executed : WordArith (BitVec width))
    (encoded : arithToExecuted? native = some executed) :
    arithFromExecuted? executed = some native := by
  cases native <;> simp [arithToExecuted?] at encoded
  all_goals
    subst executed
    simp [arithFromExecuted?]

-- Native Skip is retained as the executed tick payload; constants remain words.
def instToExecuted? {width : Nat} [NeZero width] :
    HolInst width → Option (LabPlain (BitVec width))
  | .skip => some .tick
  | .const r w => some (.word (.const r w))
  | .arith op => (arithToExecuted? op).map (fun a => .word (.arith a))
  | .mem op r (.addr base offset) => some (.word (.memOffset op r base offset))

def instFromExecuted? {width : Nat} [NeZero width] :
    LabPlain (BitVec width) → Option (HolInst width)
  | .tick => some .skip
  | .word (.const r w) => some (.const r w)
  | .word (.arith a) => (arithFromExecuted? a).map HolInst.arith
  | .word (.memOffset op r base offset) => some (.mem op r (.addr base offset))
  | _ => none

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem inst_recover {width : Nat} [NeZero width]
    (native : HolInst width) (executed : LabPlain (BitVec width))
    (encoded : instToExecuted? native = some executed) :
    instFromExecuted? executed = some native := by
  cases native with
  | skip =>
    simp [instToExecuted?] at encoded
    subst executed
    rfl
  | const r w =>
    simp [instToExecuted?] at encoded
    subst executed
    rfl
  | arith op =>
    cases converted : arithToExecuted? op with
    | none => simp [instToExecuted?, converted] at encoded
    | some operation =>
      simp [instToExecuted?, converted] at encoded
      subst executed
      simp [instFromExecuted?, arith_recover op operation converted]
  | mem op r address =>
    cases address with
    | addr base offset =>
      simp [instToExecuted?] at encoded
      subst executed
      rfl


def refToExecuted : Lab → LabRef
  | .lab sectionId label => ⟨sectionId, label⟩
def refFromExecuted (reference : LabRef) : Lab :=
  .lab reference.sectionId reference.label
/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
@[simp] theorem ref_recover (native : Lab) :
    refFromExecuted (refToExecuted native) = native := by
  cases native <;> rfl

def asmToExecuted? {width : Nat} [NeZero width] :
    HolAsm width → Option (LabPlain (BitVec width))
  | .inst instruction => instToExecuted? instruction
  | .jumpReg register => some (.jumpReg register)
  | .jump _ | .jumpCmp _ _ _ _ | .call _ | .loc _ _ => none

def asmFromExecuted? {width : Nat} [NeZero width]
    (plain : LabPlain (BitVec width)) : Option (HolAsm width) :=
  match instFromExecuted? plain with
  | some instruction => some (.inst instruction)
  | none => match plain with
    | .jumpReg register => some (.jumpReg register)
    | _ => none

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem asm_recover {width : Nat} [NeZero width]
    (native : HolAsm width) (executed : LabPlain (BitVec width))
    (encoded : asmToExecuted? native = some executed) :
    asmFromExecuted? executed = some native := by
  cases native with
  | inst instruction =>
    have recovered := inst_recover instruction executed encoded
    simp [asmFromExecuted?, recovered]
  | jumpReg register =>
    simp [asmToExecuted?] at encoded
    subst executed
    rfl
  | jump target => simp [asmToExecuted?] at encoded
  | jumpCmp op r right target => simp [asmToExecuted?] at encoded
  | call target => simp [asmToExecuted?] at encoded
  | loc r offset => simp [asmToExecuted?] at encoded

def plainToExecuted? {width : Nat} [NeZero width] :
    AsmOrCbw (HolAsm width) HolMemop (HolAddr width) →
      Option (LabPlain (BitVec width))
  | .asmi instruction => asmToExecuted? instruction
  | .cbw address value => some (.codeBufferWrite address value)
  | .shareMem op register (.addr base offset) =>
      some (.shareMemOffset op register base offset)

def plainFromExecuted? {width : Nat} [NeZero width]
    (plain : LabPlain (BitVec width)) :
      Option (AsmOrCbw (HolAsm width) HolMemop (HolAddr width)) :=
  match asmFromExecuted? plain with
  | some instruction => some (.asmi instruction)
  | none => match plain with
    | .codeBufferWrite address value => some (.cbw address value)
    | .shareMemOffset op register base offset =>
        some (.shareMem op register (.addr base offset))
    | _ => none

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem plain_recover {width : Nat} [NeZero width]
    (native : AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (executed : LabPlain (BitVec width))
    (encoded : plainToExecuted? native = some executed) :
    plainFromExecuted? executed = some native := by
  cases native with
  | asmi instruction =>
    have recovered := asm_recover instruction executed encoded
    simp [plainFromExecuted?, recovered]
  | cbw address value =>
    simp [plainToExecuted?] at encoded
    subst executed
    rfl
  | shareMem op register address =>
    cases address with
    | addr base offset =>
      simp [plainToExecuted?] at encoded
      subst executed
      rfl

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
  · simp only [nameFromExecuted?, if_pos ranged, Option.some.injEq] at decoded
    subst native
    have bytes : ∀ c ∈ executed.toList, c.toNat < 256 := by
      intro character member
      simpa only [decide_eq_true_eq] using (List.all_eq_true.mp ranged character member)
    exact Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes executed bytes
  · simp only [nameFromExecuted?, if_neg ranged] at decoded
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

def lineToExecuted? {width : Nat} [NeZero width] :
    LabLineHOL width → Option (LabLine (BitVec width))
  | .label sectionId label length => some (.label sectionId label length)
  | .asm instruction bytes length =>
      (plainToExecuted? instruction).map (fun op => .asm op bytes length)
  | .labAsm instruction position bytes length =>
      if position = 0 then some (.labAsm (labAsmToExecuted instruction) bytes length)
      else none

def lineFromExecuted? {width : Nat} [NeZero width] :
    LabLine (BitVec width) → Option (LabLineHOL width)
  | .label sectionId label length => some (.label sectionId label length)
  | .asm instruction bytes length =>
      (plainFromExecuted? instruction).map (fun op => .asm op bytes length)
  | .labAsm instruction bytes length =>
      (labAsmFromExecuted? instruction).map (fun op => .labAsm op 0 bytes length)

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem line_recover {width : Nat} [NeZero width]
    (native : LabLineHOL width) (executed : LabLine (BitVec width))
    (encoded : lineToExecuted? native = some executed) :
    lineFromExecuted? executed = some native := by
  cases native with
  | label sectionId label length =>
    simp [lineToExecuted?] at encoded
    subst executed
    rfl
  | asm instruction bytes length =>
    cases converted : plainToExecuted? instruction with
    | none => simp [lineToExecuted?, converted] at encoded
    | some operation =>
      simp [lineToExecuted?, converted] at encoded
      subst executed
      simp [lineFromExecuted?, plain_recover instruction operation converted]
  | labAsm instruction position bytes length =>
    by_cases zero : position = 0
    · simp only [lineToExecuted?, if_pos zero, Option.some.injEq] at encoded
      subst executed
      subst position
      simp only [lineFromExecuted?, labAsm_recover, Option.map_some]
    · simp only [lineToExecuted?, if_neg zero] at encoded
      cases encoded

-- Generic finite-list codec, with a genuine element recovery hypothesis.
def mapCodec? {α β : Type} (encode : α → Option β) : List α → Option (List β)
  | [] => some []
  | first :: rest => do
      let head ← encode first
      let tail ← mapCodec? encode rest
      pure (head :: tail)

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem mapCodec_recover {α β : Type} (encode : α → Option β) (decode : β → Option α)
    (recover : ∀ native executed, encode native = some executed → decode executed = some native)
    (native : List α) (executed : List β) (encoded : mapCodec? encode native = some executed) :
    mapCodec? decode executed = some native := by
  induction native generalizing executed with
  | nil =>
    simp [mapCodec?] at encoded
    subst executed
    rfl
  | cons first rest ih =>
    cases headResult : encode first with
    | none => simp [mapCodec?, headResult] at encoded
    | some head =>
      cases tailResult : mapCodec? encode rest with
      | none => simp [mapCodec?, headResult, tailResult] at encoded
      | some tail =>
        simp [mapCodec?, headResult, tailResult] at encoded
        subst executed
        simp [mapCodec?, recover first head headResult, ih tail tailResult]

def sectionToExecuted? {width : Nat} [NeZero width]
    (native : Section (LabLineHOL width)) : Option (LabSection (BitVec width)) :=
  (mapCodec? lineToExecuted? native.lines).map (fun lines => ⟨native.sectionId, lines⟩)

def sectionFromExecuted? {width : Nat} [NeZero width]
    (executed : LabSection (BitVec width)) : Option (Section (LabLineHOL width)) :=
  (mapCodec? lineFromExecuted? executed.lines).map (fun lines => ⟨executed.name, lines⟩)

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem section_recover {width : Nat} [NeZero width]
    (native : Section (LabLineHOL width)) (executed : LabSection (BitVec width))
    (encoded : sectionToExecuted? native = some executed) :
    sectionFromExecuted? executed = some native := by
  cases native with
  | mk sectionId lines =>
    cases converted : mapCodec? lineToExecuted? lines with
    | none => simp [sectionToExecuted?, converted] at encoded
    | some decoded =>
      simp [sectionToExecuted?, converted] at encoded
      subst executed
      simp [sectionFromExecuted?, mapCodec_recover lineToExecuted? lineFromExecuted?
        line_recover lines decoded converted]

def programToExecuted? {width : Nat} [NeZero width] :
    List (Section (LabLineHOL width)) → Option (LabProgram (BitVec width)) :=
  mapCodec? sectionToExecuted?
def programFromExecuted? {width : Nat} [NeZero width] :
    LabProgram (BitVec width) → Option (List (Section (LabLineHOL width))) :=
  mapCodec? sectionFromExecuted?

/-- Flapjack-specific exact codec recovery or boundary fact; no HOL original. -/
theorem program_recover {width : Nat} [NeZero width]
    (native : List (Section (LabLineHOL width))) (executed : LabProgram (BitVec width))
    (encoded : programToExecuted? native = some executed) :
    programFromExecuted? executed = some native :=
  mapCodec_recover sectionToExecuted? sectionFromExecuted? section_recover native executed encoded

end Flapjack.Compiler.Backend.StackToLab.ExecutedCodec
