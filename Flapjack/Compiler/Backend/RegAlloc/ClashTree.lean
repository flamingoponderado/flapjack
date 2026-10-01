import Flapjack.Misc.Sptree

namespace Flapjack.RegAlloc

/-- Literal clash-tree carrier. Lists and num_sets retain their source carriers. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "clash_tree"]
inductive ClashTree where
  | delta (writes reads : List Nat)
  | set (live : NumSet)
  | branch (live : Option NumSet) (left right : ClashTree)
  | seq (left right : ClashTree)
  deriving Repr, DecidableEq

/-- Source left-to-right deletion; this proof-side port is not wired into the
executed allocator yet. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "numset_list_delete_def"]
def numsetListDelete {α : Type} : List Nat → Spt α → Spt α
  | [], tree => tree
  | name :: names, tree => numsetListDelete names (sptDelete name tree)

/-- Reject duplicate colours before constructing the source-shaped coloured set. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "check_col_def"]
def checkCol (f : Nat → Nat) (tree : NumSet) : Option (NumSet × NumSet) :=
  let names := (sptToAList tree).map (fun entry => f entry.1)
  if names.Pairwise (· ≠ ·) then
    some (tree, sptFromAList (names.map (fun name => (name, ()))))
  else none

/-- Existing live names are skipped; a new name whose colour is already live
fails before either map is changed. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "check_partial_col_def"]
def checkPartialCol (f : Nat → Nat) : List Nat → NumSet → NumSet →
    Option (NumSet × NumSet)
  | [], tree, coloured => some (tree, coloured)
  | name :: names, tree, coloured =>
    match sptLookup name tree with
    | some () => checkPartialCol f names tree coloured
    | none =>
      match sptLookup (f name) coloured with
      | none => checkPartialCol f names (sptInsert name () tree)
          (sptInsert (f name) () coloured)
      | some () => none

/-- Literal oracle checker. Delta checks writes then discards that check's
result, deleting writes from the incoming sets before adding reads. Branch
checks both children from the same incoming sets; Seq checks right first.
Production allocator migration remains separate work. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "check_clash_tree_def"]
def checkClashTree (f : Nat → Nat) : ClashTree → NumSet → NumSet →
    Option (NumSet × NumSet)
  | .delta writes reads, live, coloured =>
    match checkPartialCol f writes live coloured with
    | none => none
    | some _ => checkPartialCol f reads (numsetListDelete writes live)
        (numsetListDelete (writes.map f) coloured)
  | .set tree, _, _ => checkCol f tree
  | .branch fixed left right, live, coloured =>
    match checkClashTree f left live coloured with
    | none => none
    | some (leftOut, leftColoured) =>
      match checkClashTree f right live coloured with
      | none => none
      | some (rightOut, _) =>
        match fixed with
        | none => checkPartialCol f
            ((sptToAList (sptDifference rightOut leftOut)).map Prod.fst)
            leftOut leftColoured
        | some tree => checkCol f tree
  | .seq left right, live, coloured =>
    match checkClashTree f right live coloured with
    | none => none
    | some (rightOut, rightColoured) => checkClashTree f left rightOut rightColoured

end Flapjack.RegAlloc
