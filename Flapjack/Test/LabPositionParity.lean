import Flapjack.RiscV.Lab

namespace Flapjack.RiscV

/-! CakeML's `lab_to_target` indexes CallFFI targets from the original
    `ffi_names` order while the exported prefix emits those blocks reversed.
    These two-service guards exercise the position base and prefix ordering;
    the one-service case cannot distinguish the two conventions. -/

example :
    labFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "first" 64 =
      some (0 - BitVec.ofNat 64 112) := by
  decide

example :
    labFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "second" 64 =
      some (0 - BitVec.ofNat 64 128) := by
  decide

/-! A leading retained label has no preceding Asm/LabAsm, so Cake's
    `pad_section` leaves the section physically unchanged.  Consecutive
    retained labels still apply `add_nop` to that same nearest predecessor. -/
example :
    labLinkedFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "first" 96 =
      some (0 - BitVec.ofNat 64 80) := by
  decide

example :
    labLinkedFfiStubOffset (width := 64)
      { services := [("first", 7), ("second", 8)] } "second" 96 =
      some (0 - BitVec.ofNat 64 96) := by
  decide

/-! `labLookupProgramPosition` used to scan the label list linearly and take
    the first match.  The `LabLabelIndex` sptree analogue must agree with that
    scan on every key, including the duplicate entries the fixpoint sweep
    produces, where the *earlier* entry wins. -/

/-- The linear first-match scan the index replaced. -/
def labLookupProgramPositionLinear (sectionId label : Nat)
    (entries : List (Nat × Nat × Nat)) : Option Nat :=
  match entries with
  | [] => none
  | (s, l, position) :: rest =>
      if s == sectionId && l == label then some position
      else labLookupProgramPositionLinear sectionId label rest

def labIndexSampleEntries : List (Nat × Nat × Nat) :=
  [(3, 0, 1000), (3, 1, 1016), (4, 0, 1032),
   /- a stale duplicate from an earlier sweep: the first entry must win -/
   (3, 1, 9999), (4, 2, 1048), (0, 0, 812)]

def labIndexAgreesWithLinear : Bool :=
  let index := labLabelIndexOf labIndexSampleEntries
  (List.range 6).all fun sectionId =>
    (List.range 4).all fun label =>
      labLookupProgramPosition sectionId label index ==
        labLookupProgramPositionLinear sectionId label labIndexSampleEntries

#guard labIndexAgreesWithLinear

/-! Duplicate keys: the earlier entry wins, matching the first-match scan. -/
#guard labLookupProgramPosition 3 1 (labLabelIndexOf labIndexSampleEntries) ==
  some 1016

/-! A known section with an unknown label is `none`, not the section's other
    position -- the two-level tree must not collapse the label dimension. -/
#guard labLookupProgramPosition 3 2 (labLabelIndexOf labIndexSampleEntries) ==
  none

/-! An unknown section is `none`. -/
#guard labLookupProgramPosition 7 0 (labLabelIndexOf labIndexSampleEntries) ==
  none

/-! The index retains the entry list verbatim, so passes that re-emit the
    collected labels are unaffected by the change of carrier. -/
#guard (labLabelIndexOf labIndexSampleEntries).entries == labIndexSampleEntries

end Flapjack.RiscV
