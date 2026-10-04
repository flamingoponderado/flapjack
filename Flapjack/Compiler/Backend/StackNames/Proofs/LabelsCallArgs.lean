import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.StackProps.OrderedLabels
import Flapjack.Compiler.Backend.StackProps.CallArgs

/-!
# stack_namesProof: `stack_names_lab_pres` and `stack_names_call_args`

Ports of `cakeml/compiler/backend/proofs/stack_namesProofScript.sml` lines 589-596 and
668-685: renaming registers preserves the ordered continuation labels, and maps the fixed
`call_args` registers through `find_name`.
-/

namespace Flapjack.Compiler.Backend.StackNames

open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.StackPropsCodeLabels

/-- Exact HOL `stack_names_lab_pres` (`stack_namesProofScript.sml:589-596`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesLabPres {width : Nat} [NeZero width] :
    ∀ (f : Spt Nat) (p : HolProg width), extractLabels p = extractLabels (progCompHOL f p) := by
  intro f p
  induction p using progCompHOL.induct <;>
    try simp_all [progCompHOL, extractLabels]
  rename_i rh _ hd ih2 ih1
  rcases rh with _ | ⟨rp, lr, l1, l2⟩ <;> rcases hd with _ | ⟨hp, h1, h2⟩ <;>
    simp_all [progCompHOL, extractLabels]

/-- `call_args` through `comp` (Flapjack infrastructure; the `comp_ind` induction of HOL's
`stack_names_call_args` proof). -/
theorem callArgs_progCompHOL {width : Nat} [NeZero width] (f : Spt Nat) (p : HolProg width) :
    ∀ ptr len ptr2 len2 ret, callArgs p ptr len ptr2 len2 ret →
      callArgs (progCompHOL f p) (findNameSpt f ptr) (findNameSpt f len) (findNameSpt f ptr2)
        (findNameSpt f len2) (findNameSpt f ret) := by
  induction p using progCompHOL.induct <;>
    try simp_all [progCompHOL, callArgs]
  rename_i rh _ hd ih2 ih1
  rcases rh with _ | ⟨rp, lr, l1, l2⟩ <;> rcases hd with _ | ⟨hp, h1, h2⟩ <;>
    simp_all [progCompHOL, callArgs]

/-- Exact HOL `stack_names_call_args` (`stack_namesProofScript.sml:668-685`). HOL's free `f`,
`p` and `p'` are the implicit binders; `EVERY P l` is `∀ q ∈ l, P q`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem stackNamesCallArgs {width : Nat} [NeZero width] {f : Spt Nat}
    {p p' : List (Nat × HolProg width)} :
    compileHOL f p = p' ∧ (∀ q ∈ p.map Prod.snd, callArgs q 1 2 3 4 0) →
      ∀ q ∈ p'.map Prod.snd, callArgs q (findNameSpt f 1) (findNameSpt f 2)
        (findNameSpt f 3) (findNameSpt f 4) (findNameSpt f 0) := by
  rintro ⟨rfl, h⟩ q hq
  simp only [compileHOL, List.map_map, List.mem_map, Function.comp, progCompEntryHOL] at hq
  obtain ⟨e, he, rfl⟩ := hq
  exact callArgs_progCompHOL f e.2 _ _ _ _ _ (h e.2 (List.mem_map.mpr ⟨e, he, rfl⟩))

end Flapjack.Compiler.Backend.StackNames
