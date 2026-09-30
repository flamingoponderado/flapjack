import Flapjack.Pancake.CrepLang.GeneratedSize

/-!
# Generated `crepLang` datatype size parity

Replays the rows of `scripts/hol-probes/crep_lang_size_probe.out`, printed from
the real CakeML `crepLangTheory` by
`scripts/hol-probes/crep_lang_size_probeScript.sml`, against the untagged
transcriptions in `Flapjack.Pancake.CrepLang.GeneratedSize`.  Clause shapes are
checked definitionally and the concrete `EVAL` rows by `#guard`.
-/

namespace Flapjack.Test.CrepLangGeneratedSizeParity

open Flapjack Flapjack.CrepLangGeneratedSize

abbrev ml (s : String) : Flapjack.Basis.Pure.MlString.MlString :=
  Flapjack.Basis.Pure.MlString.ofString s

section
variable {width : Nat} [NeZero width] {α : Type} (f : α → Nat)

example (a : CrepProgHOL width) (b : CrepProgHOL width) :
    crepProgSizeHOL f (.seq a b) = 1 + (crepProgSizeHOL f a + crepProgSizeHOL f b) := by
  simp [crepProgSizeHOL]

example : crepProgSizeHOL f (.skip : CrepProgHOL width) = 0 := by simp [crepProgSizeHOL]

example : crepProgSizeHOL f (.tick : CrepProgHOL width) = 0 := by simp [crepProgSizeHOL]

example (e : BitVec width) (p : CrepProgHOL width) :
    crepProg4SizeHOL f (e, p) = 1 + (e.toNat + crepProgSizeHOL f p) := by
  simp [crepProg4SizeHOL]
end

/-- Probe rows `prog_size_seq`, `prog_size_call`, `prog_size_dec`,
    `prog_size_ext` and `prog_size_raise` (words of width 8, `f = K 0`). -/
def probeGuard : Bool :=
  let f : Nat → Nat := fun _ => 0
  crepProgSizeHOL (width := 8) f
      (.seq (.assign 1 (.const 7)) (.return [.var 2])) == 16 &&
  crepProgSizeHOL (width := 8) f
      (.call (some ([1], some (3, .break 0))) (ml "f") [.var 1]) == 16 &&
  crepProgSizeHOL (width := 8) f
      (.dec 4 (.op .add [.var 1, .const 2]) (.while (.var 4) .tick)) == 19 &&
  crepProgSizeHOL (width := 8) f (.extCall (ml "g") 1 2 3 4) == 13 &&
  crepProgSizeHOL (width := 8) f (.raise 5) == 6

#guard probeGuard

def runChecks : IO Bool := do
  if probeGuard then
    IO.println "PASS generated crepLang prog_size matches real crepLangTheory probe"
    pure true
  else
    IO.println "FAIL generated crepLang prog_size matches real crepLangTheory probe"
    pure false

end Flapjack.Test.CrepLangGeneratedSizeParity
