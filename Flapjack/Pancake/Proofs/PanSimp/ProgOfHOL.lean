import Flapjack.Pancake.PanSimp

/-!
Flapjack-specific representation bridges for the exact HOL `pan_simp` pass.

These results connect the `ProgHOL` ports to the production `Prog` helpers.
They are not HOL declarations themselves and therefore carry no `@[hol]`
tag.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Decode of the exact HOL `SmartSeq_def` agrees with production `smartSeq`.
This is Flapjack-specific codec infrastructure: HOL defines `SmartSeq` on
`ProgHOL`, but has no separate theorem about the Lean `progOfHOL` decoder. -/
theorem progOfHOL_smartSeqHOL {width : Nat} [NeZero width]
    (pre program : ProgHOL width) :
    progOfHOL (smartSeqHOL pre program) =
      smartSeq (progOfHOL pre) (progOfHOL program) := by
  cases pre <;> simp [smartSeqHOL, smartSeq, progOfHOL]
  case call info name args =>
    cases info with
    | none => simp [progOfHOL.eq_13]
    | some info =>
      obtain ⟨kind, handler⟩ := info
      cases handler with
      | none => simp [progOfHOL.eq_14]
      | some handler =>
        obtain ⟨eid, vname, body⟩ := handler
        simp [progOfHOL.eq_15]

end Flapjack
