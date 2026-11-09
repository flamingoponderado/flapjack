module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Control
public import Flapjack.Misc.Sptree.SizeDelete

@[expose] public section

/-! Timestamped mutable-constructor finalization. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack

/-- Finalize mutable constructor chains, temporarily deleting each visited
reference and assigning a fresh timestamp to every resulting block. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "finalise_cons_def"]
def finaliseCons (value : Value) (refs : Spt (BvlSem.Ref Value)) (timestamp : Option Nat) :
    Option (Value × Spt (BvlSem.Ref Value) × Option Nat) :=
  match value with
  | .refPtr bit ptr =>
      match _found : sptLookup ptr refs with
      | some (.mutBlock tag finalised left child right) =>
          if finalised then none else
            match finaliseCons child (sptDelete ptr refs) timestamp with
            | none => none
            | some (result, rest, nextTimestamp) =>
                some (.block (nextTimestamp.getD 0) tag (left ++ [result] ++ right),
                  sptInsert ptr (.mutBlock tag true left child right) rest, nextTimestamp.map (· + 1))
      | some _ => some (.refPtr bit ptr, refs, timestamp)
      | none => none
  | other => some (other, refs, timestamp)
termination_by sptSize refs
decreasing_by
  apply sptSize_delete_lt
  simp [_found]

end Flapjack.Compiler.Backend.DataSem
