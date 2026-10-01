import Flapjack.Pancake.WordConvs.NameMonotonicity
namespace Flapjack.Test.WordConvsNameMonoParity
private def nm_empty : WordLangCutsetsHOL := (.ln, .ln)
example : everyNameHOL (fun x => decide (x ≤ 0)) nm_empty = true ∧
    everyNameHOL (fun x => decide (x ≤ 0)) nm_empty = true := by
  have hp : everyNameHOL (fun x => decide (x ≤ 0)) nm_empty = true := by decide +kernel
  exact ⟨hp, everyNameMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
private def nm_single : WordLangCutsetsHOL := (.ls (), .ln)
example : everyNameHOL (fun x => decide (x ≤ 0)) nm_single = true ∧
    everyNameHOL (fun x => decide (x ≤ 3)) nm_single = true := by
  have hp : everyNameHOL (fun x => decide (x ≤ 0)) nm_single = true := by decide +kernel
  exact ⟨hp, everyNameMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
private def nm_both : WordLangCutsetsHOL := (.bs (.ls ()) () (.ls ()), .ls ())
example : everyNameHOL (fun x => decide (x ≤ 2)) nm_both = true ∧
    everyNameHOL (fun x => decide (x ≤ 9)) nm_both = true := by
  have hp : everyNameHOL (fun x => decide (x ≤ 2)) nm_both = true := by decide +kernel
  exact ⟨hp, everyNameMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
private def nm_invalid : WordLangCutsetsHOL := (.bn .ln .ln, .bs .ln () .ln)
example : everyNameHOL (fun x => decide (x ≤ 0)) nm_invalid = true ∧
    everyNameHOL (fun x => decide (x ≤ 1)) nm_invalid = true := by
  have hp : everyNameHOL (fun x => decide (x ≤ 0)) nm_invalid = true := by decide +kernel
  exact ⟨hp, everyNameMono _ _ _ ⟨by intro x hx; simp_all <;> omega, hp⟩⟩
example : everyNameHOL (fun x => decide (x ≤ 0)) (.ls (), .ln) = true ∧
    everyNameHOL (fun _ => false) (.ls (), .ln) = false := by decide +kernel
end Flapjack.Test.WordConvsNameMonoParity
