import Flapjack.Compiler.Backend.DataSpace.Compile
import Flapjack.Compiler.Backend.Semantics.DataProps.CodeLabels

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
theorem getCodeLabels_space (program : DataLang.Prog) :
    match space program with
    | .inl result => getCodeLabels result = getCodeLabels program
    | .inr (_, _, result) => getCodeLabels result = getCodeLabels program := by
  fun_induction space program <;>
    simp_all (config := { zetaDelta := true }) [space, getCodeLabels, getCodeLabels_pMakeSpace]
  all_goals repeat' (split at * <;> simp_all)

/-- Restoring a deferred reservation leaves its referenced code labels intact. -/
@[hol "cakeml/compiler/backend/proofs/data_spaceProofScript.sml" "get_code_labels_compile"]
theorem getCodeLabels_compile (program : DataLang.Prog) :
    getCodeLabels (compile program) = getCodeLabels program := by
  have labels := getCodeLabels_space program
  cases found : space program with
  | inl result => simpa [compile, pMakeSpace, found] using labels
  | inr payload =>
    obtain ⟨amount, names, result⟩ := payload
    simpa [compile, pMakeSpace, getCodeLabels, found] using labels

end Flapjack.Compiler.Backend.DataSpace
