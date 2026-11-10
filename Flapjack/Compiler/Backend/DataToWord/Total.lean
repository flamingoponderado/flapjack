module

public import Flapjack.Compiler.Backend.DataToWord.Control

@[expose] public section

/-! Totality of the existing data-to-word traversal. -/
namespace Flapjack.Compiler.Backend.DataToWord

/-- The checked traversal always returns a result. This Flapjack-specific
invariant discharges the option wrapper around the executable traversal; it
does not by itself establish correspondence with HOL's `comp`. -/
theorem compileControl_exists {width : Nat} [NeZero width] (conf : Config) (secn l : Nat)
    (program : DataLang.Prog) :
    ∃ result, compileControl? (width := width) conf secn l program = some result := by
  fun_induction compileControl? (width := width) conf secn l program <;> simp_all
  case case6 l x y ihx ihy =>
    obtain ⟨a, b, ha⟩ := ihx
    obtain ⟨c, d, hc⟩ := ihy b
    simp [ha, hc]
  case case7 l n x y ihx ihy =>
    obtain ⟨a, b, ha⟩ := ihx
    obtain ⟨c, d, hc⟩ := ihy b
    simp [ha, hc]
  case case138 l ns names target args n handler ih =>
    obtain ⟨a, b, ha⟩ := ih
    simp [ha]

/-- The traversal exposed as a total function, with failure ruled out by
`compileControl_exists`. Source-level comparison with HOL remains open. -/
def compileControl {width : Nat} [NeZero width] (conf : Config) (secn l : Nat)
    (program : DataLang.Prog) : WordLangProgHOL (BitVec width) × Nat :=
  (compileControl? conf secn l program).get (by
    obtain ⟨result, h⟩ := compileControl_exists (width := width) conf secn l program
    simp [h])

/-- The total operation returns exactly the result of the existing traversal.
This Flapjack-specific equation supports replacing option-valued calls. -/
theorem compileControl_option {width : Nat} [NeZero width] (conf : Config) (secn l : Nat)
    (program : DataLang.Prog) :
    compileControl? (width := width) conf secn l program = some (compileControl conf secn l program) := by
  obtain ⟨result, h⟩ := compileControl_exists (width := width) conf secn l program
  simp [compileControl, h]

end Flapjack.Compiler.Backend.DataToWord
