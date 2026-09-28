import Flapjack.Pancake.Proofs.CrepInline

/-!
Lean replays of direct HOL rows in
`scripts/hol-probes/crep_inline_relations_probe.out` for
`state_rel_def` and `locals_rel_def` from `crep_inlineProofScript.sml:12-29`.
-/

namespace Flapjack.Test.CrepInlineRelationsExactParity

open Flapjack

private def word8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n
private def ffi : HolFfiState Unit :=
  { oracle := fun _ state _ _ => .ret state []
    ffiState := ()
    ioEvents := [] }

private def leftLocals : HolFiniteMapExact Nat (HolWordLab 8) :=
  (HolFiniteMapExact.empty.updateEq (1, .word (word8 7)))

private def extendedLocals : HolFiniteMapExact Nat (HolWordLab 8) :=
  leftLocals.updateEq (2, .word (word8 9))

private def missingLocals : HolFiniteMapExact Nat (HolWordLab 8) :=
  HolFiniteMapExact.empty.updateEq (2, .word (word8 9))

private def conflictingLocals : HolFiniteMapExact Nat (HolWordLab 8) :=
  HolFiniteMapExact.empty.updateEq (1, .word (word8 8))

private def emptyCode : HolFiniteMapExact MlString (List Nat × CrepProgHOL 8) :=
  HolFiniteMapExact.empty

private def state (locals : HolFiniteMapExact Nat (HolWordLab 8))
    (clock : Nat := 5) : CrepSemHOLState 8 Unit where
  locals := locals
  globals := HolFiniteMapExact.empty
  code := emptyCode
  memory := fun _ => .word (word8 0)
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := clock
  be := false
  ffi := ffi
  baseAddr := word8 0
  topAddr := word8 100

private theorem localsExtension :
    CrepInlineExact.crepInlineLocalsRelExact
      (state leftLocals) (state extendedLocals) := by
  change ∀ key value, leftLocals.lookup key = some value →
    extendedLocals.lookup key = some value
  intro key value h
  by_cases h2 : key = 2
  · subst key
    simp [leftLocals, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at h
  · by_cases h1 : key = 1
    · subst key
      simp [leftLocals, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at h
      simpa [leftLocals, extendedLocals, HolFiniteMapExact.lookup_updateEq,
        FUPDATE_HOL] using h
    · simp [leftLocals, h1, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at h

private theorem localsMissingKey :
    ¬ CrepInlineExact.crepInlineLocalsRelExact
      (state leftLocals) (state missingLocals) := by
  intro h
  have h1 := h 1 (.word (word8 7))
  change leftLocals.lookup 1 = some (.word (word8 7)) →
    missingLocals.lookup 1 = some (.word (word8 7)) at h1
  simp [leftLocals, missingLocals, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL] at h1

private theorem localsConflictingValue :
    ¬ CrepInlineExact.crepInlineLocalsRelExact
      (state leftLocals) (state conflictingLocals) := by
  intro h
  have h1 := h 1 (.word (word8 7))
  change leftLocals.lookup 1 = some (.word (word8 7)) →
    conflictingLocals.lookup 1 = some (.word (word8 7)) at h1
  simp [leftLocals, conflictingLocals, HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL] at h1
  exact absurd h1 (by decide)

private theorem stateRelationIgnoresLocals :
    CrepInlineExact.crepInlineStateRelExact
      (state leftLocals) (state extendedLocals) := by
  simp [CrepInlineExact.crepInlineStateRelExact, state]

private theorem stateRelationChecksClock :
    ¬ CrepInlineExact.crepInlineStateRelExact
      (state leftLocals) (state leftLocals 6) := by
  intro h
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ (5 : Nat) = 6 ∧ _ ∧ _ ∧ _ ∧ _ at h
  have hclock := h.2.2.2.2.2.1
  exact (by decide : ¬ (5 : Nat) = 6) hclock

private def finiteMapRowsMatchOracle : Bool :=
  leftLocals.lookup 1 == some (.word (word8 7)) &&
    extendedLocals.lookup 1 == some (.word (word8 7)) &&
    extendedLocals.lookup 2 == some (.word (word8 9)) &&
    missingLocals.lookup 1 == none &&
    conflictingLocals.lookup 1 == some (.word (word8 8))

def runChecks : IO Bool := pure finiteMapRowsMatchOracle

end Flapjack.Test.CrepInlineRelationsExactParity
