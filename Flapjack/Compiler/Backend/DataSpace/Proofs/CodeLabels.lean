module

public import Flapjack.Compiler.Backend.DataSpace.Compile
public import Flapjack.Compiler.Backend.Semantics.DataProps.CodeLabels

@[expose] public section

/-! Code-reference preservation by the reservation pass. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Restoring a deferred reservation does not introduce code references. -/
theorem getCodeLabels_pMakeSpace (result : Sum DataLang.Prog (Nat × NumSet × DataLang.Prog)) :
    getCodeLabels (pMakeSpace result) =
      match result with
      | .inl body => getCodeLabels body
      | .inr (_, _, body) => getCodeLabels body := by
  cases result with
  | inl body => rfl
  | inr payload => obtain ⟨amount, names, body⟩ := payload; simp [pMakeSpace, getCodeLabels]

/-- Both forms of the reservation pass retain the original code labels. -/
@[hol "cakeml/compiler/backend/proofs/data_spaceProofScript.sml" "get_code_labels_space"]
theorem getCodeLabels_space (program result : DataLang.Prog) (amount : Nat)
    (names : NumSet) (body : DataLang.Prog) :
    (space program = .inl result → getCodeLabels result = getCodeLabels program) ∧
      (space program = .inr (amount, names, body) → getCodeLabels body = getCodeLabels program) := by
  have labels (p : DataLang.Prog) :
      match space p with
      | .inl result => getCodeLabels result = getCodeLabels p
      | .inr (_, _, result) => getCodeLabels result = getCodeLabels p := by
    fun_induction space p <;>
      simp_all (config := { zetaDelta := true }) [space, getCodeLabels, getCodeLabels_pMakeSpace]
    all_goals repeat' (split at * <;> simp_all)
  constructor
  · intro h
    simpa [h] using labels program
  · intro h
    simpa [h] using labels program

/-- Restoring a deferred reservation leaves its referenced code labels intact. -/
@[hol "cakeml/compiler/backend/proofs/data_spaceProofScript.sml" "get_code_labels_compile"]
theorem getCodeLabels_compile (program : DataLang.Prog) :
    getCodeLabels (compile program) = getCodeLabels program := by
  cases found : space program with
  | inl result =>
    simpa [compile, pMakeSpace, found] using
      (getCodeLabels_space program result 0 .ln .skip).1 found
  | inr payload =>
    obtain ⟨amount, names, result⟩ := payload
    simpa [compile, pMakeSpace, getCodeLabels, found] using
      (getCodeLabels_space program .skip amount names result).2 found

end Flapjack.Compiler.Backend.DataSpace
