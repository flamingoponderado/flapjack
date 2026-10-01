import Flapjack.Compiler.Backend.Parmove.Permutation

namespace Flapjack.Compiler.Backend.Parmove

/-- The empty parallel move list is the identity on the entire environment,
with independent register and value carriers. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "parsem_nil"]
theorem parsem_nil {α β : Type} [DecidableEq α] :
    parsem (β := β) ([] : List (α × α)) = id := by
  rfl

/-- Extract a move to the head without changing the full parallel semantics.
Only HOL's windmill and list-decomposition premises are assumed; destinations
need not be numeric and the value carrier is independent. -/
@[hol "cakeml/compiler/backend/reg_alloc/parmoveScript.sml" "independence"]
theorem independence {α β : Type} [DecidableEq α]
    (before : List (α × α)) (source destination : α)
    (suffix moves : List (α × α)) :
    windmill moves ∧ moves = before ++ [(destination, source)] ++ suffix →
    parsem (β := β) moves = parsem ([(destination, source)] ++ before ++ suffix) := by
  rintro ⟨valid, rfl⟩
  apply parsem_perm
  refine ⟨valid, ?_⟩
  exact (List.perm_append_comm.append_right suffix)

end Flapjack.Compiler.Backend.Parmove
