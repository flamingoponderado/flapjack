import Flapjack.Compiler.Backend.StackRemove

/-! Native storage addressing from stack_removeScript.sml:37–53.
Production replacement remains dependency-linked on 36ez.3.
-/
namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang

-- Constructor equality, including the original fixed-width Temp payload.
deriving instance DecidableEq for StoreName

/-- Flapjack infrastructure implementing INDEX_FIND's first-match index and
payload; no standalone HOL declaration is claimed. Equality is constructor
and fixed-width Temp equality on the reviewed native StoreName. -/
private def findStoreIndex (name : StoreName) : Nat → List StoreName → Option (Nat × StoreName)
  | _, [] => none
  | index, current :: rest =>
      if current = name then some (index, current)
      else findStoreIndex name (index + 1) rest

/-- Exact first-index search, with zero reserved for names absent from store_list. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "store_pos_def"]
def storePos (name : StoreName) : Nat :=
  match findStoreIndex name 0 storeList with
  | none => 0
  | some (index, _) => index + 1

/-- Original modular negative byte offset at the native word dimension. -/
@[hol "cakeml/compiler/backend/stack_removeScript.sml" "store_offset_def"
  (words_as_type_indexed_bitvec)]
def storeOffset {width : Nat} [NeZero width] (name : StoreName) : BitVec width :=
  0 - wordOffset (storePos name)

end Flapjack.Compiler.Backend.StackRemove
