module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.StackRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.OddInter

@[expose] public section

/-! Joining source locals with their adjusted word-local entries. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- Join the source locals with the word locals whose names are adjusted source
names. The `Nonempty` instance is passed to `joinEnv` for HOL's total `THE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "join_env_locals_def"
  (total_function_inhabitants := [α])]
noncomputable def joinEnvLocals {α β : Type} [Nonempty α] (sl : Spt α) (tl : Spt β) : List (α × β) :=
  joinEnv sl (sptToAList (sptInter tl (adjustSet sl)))

/-- Inserting an odd word-local key does not change the joined locals. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "join_env_locals_insert_odd"
  (total_function_inhabitants := [α]), simp]
theorem joinEnvLocals_insertOdd {α β : Type} [Nonempty α] (n : Nat) (sl : Spt α) (v : β) (ls : Spt β)
    (odd : n % 2 = 1) : joinEnvLocals sl (sptInsert n v ls) = joinEnvLocals sl ls := by
  simp only [joinEnvLocals, inter_insertOdd_adjustSet n v ls sl odd]

/-- An odd insertion also disappears beneath a destination insertion. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "join_env_locals_insert_dest_odd"
  (total_function_inhabitants := [α]), simp]
theorem joinEnvLocals_insertDestOdd {α β : Type} [Nonempty α] (n : Nat) (sl : Spt α)
    (dest : Nat) (w v : β) (ls : Spt β) (odd : n % 2 = 1) :
    joinEnvLocals sl (sptInsert (adjustVar dest) w (sptInsert n v ls)) =
      joinEnvLocals sl (sptInsert (adjustVar dest) w ls) := by
  simp only [joinEnvLocals, inter_insertOdd_adjustSet_dest n dest w v ls sl odd]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
