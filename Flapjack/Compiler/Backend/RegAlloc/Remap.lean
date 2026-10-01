import Flapjack.Compiler.Backend.RegAlloc.ClashTree

namespace Flapjack.RegAlloc

/-- Literal fresh-name remapping on the native Spt carrier. Repeated names
retain their first allocation, including when the initial maps are arbitrary. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "list_remap_def"]
def listRemap : List Nat → Spt Nat × Spt Nat × Nat → Spt Nat × Spt Nat × Nat
  | [], state => state
  | name :: names, (toAllocator, fromAllocator, next) =>
    match sptLookup name toAllocator with
    | some _ => listRemap names (toAllocator, fromAllocator, next)
    | none => listRemap names
        (sptInsert name next toAllocator, sptInsert next name fromAllocator, next + 1)

/-- Literal clash-tree traversal for fresh-name remapping. Delta reads first,
Branch visits left first, and Seq visits right first. No tree validity premise
or fuel bound is introduced. The production allocator route is separate work. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "mk_bij_aux_def"]
def mkBijAux : ClashTree → Spt Nat × Spt Nat × Nat → Spt Nat × Spt Nat × Nat
  | .delta writes reads, state => listRemap writes (listRemap reads state)
  | .set tree, state => listRemap ((sptToAList tree).map Prod.fst) state
  | .branch fixed left right, state =>
    let state' := mkBijAux right (mkBijAux left state)
    match fixed with
    | none => state'
    | some tree => listRemap ((sptToAList tree).map Prod.fst) state'
  | .seq left right, state => mkBijAux left (mkBijAux right state)

/-- Literal initial empty-map instance of the native remapping traversal. -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "mk_bij_def"]
def mkBij (tree : ClashTree) : Spt Nat × Spt Nat × Nat :=
  let (toAllocator, fromAllocator, next) := mkBijAux tree (.ln, .ln, 0)
  (toAllocator, fromAllocator, next)

end Flapjack.RegAlloc
