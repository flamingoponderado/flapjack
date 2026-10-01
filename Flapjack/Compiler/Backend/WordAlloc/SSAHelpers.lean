import Flapjack.Compiler.Backend.WordAlloc.SSAFixInconsistencies
import Flapjack.Compiler.Backend.WordAlloc.SSASetup

/-!
# word_alloc SSA renaming helpers

Literal ports of `word_allocScript.sml:285-345`: `list_next_var_rename_move`,
`force_rename`, `mk_prio`, `ssa_reconcile` and `loop_setup`, over native
`WordLangProgHOL (BitVec width)` (positive width) and `Spt` maps. HOL `ZIP` is
`List.zip`; every `ZIP` here pairs two lists of equal length (a list and its
renaming), where HOL's `ZIP` is specified. `Move0` is `Move 0`. HOL `el = Skip`
is a match on `.skip`. Proof-side ports: the executed list-state SSA pass is not
routed through them.
-/

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Literal `list_next_var_rename_move` (`word_allocScript.sml:285-290`). -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "list_next_var_rename_move_def"
  (words_as_type_indexed_bitvec)]
def listNextVarRenameMove {width : Nat} [NeZero width] (ssa : Spt Nat) (n : Nat)
    (ls : List Nat) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
  let curLs := ls.map (optionLookup ssa)
  let (newLs, ssa', n') := listNextVarRename ls ssa n
  (.move 0 (newLs.zip curLs), ssa', n')

/-- Literal `force_rename` (`word_allocScript.sml:294-298`). -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "force_rename_def"]
def forceRename {α : Type} : List (Nat × α) → Spt α → Spt α
  | [], ssa => ssa
  | (x, y) :: xs, ssa => forceRename xs (sptInsert x y ssa)

/-- Literal `mk_prio` (`word_allocScript.sml:300-305`): prefer the branch that
is literally `Skip`. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "mk_prio_def"
  (words_as_type_indexed_bitvec)]
def mkPrio {width : Nat} [NeZero width] (el er : WordLangProgHOL (BitVec width)) :
    Option (Unit ⊕ Unit) :=
  match el with
  | .skip => some (.inl ())
  | _ =>
    match er with
    | .skip => some (.inr ())
    | _ => none

/-- Literal `ssa_reconcile` (`word_allocScript.sml:318-326`): moves from the
current to the target renaming for the keys of `ns` present in the current map,
dropping identity moves. The key set's payload type is arbitrary, as in HOL. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "ssa_reconcile_def"
  (words_as_type_indexed_bitvec)]
def ssaReconcile {width : Nat} [NeZero width] {β : Type} (curSsa tgtSsa : Spt Nat)
    (ns : Spt β) : WordLangProgHOL (BitVec width) :=
  let vars := (sptToAList ns).map Prod.fst
  let moves := ((vars.map fun v =>
      match sptLookup v curSsa with
      | none => []
      | some curV => [(optionLookup tgtSsa v, curV)]).flatten).filter
    (fun (a, b) => decide (a ≠ b))
  if moves = [] then .skip else .move 1 moves

/-- Literal `loop_setup` (`word_allocScript.sml:332-345`). -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "loop_setup_def"
  (words_as_type_indexed_bitvec)]
def loopSetup {width : Nat} [NeZero width] (names exitNames : Spt Unit) (ssa : Spt Nat)
    (na : Nat) : WordLangProgHOL (BitVec width) × Spt Nat × Nat :=
  let allVarsLs := (sptToAList (sptUnion names exitNames)).map Prod.fst
  let extendLs := allVarsLs.filter fun v => (sptLookup v ssa).isNone
  let refreshLs := allVarsLs.filter fun v => (sptLookup v ssa).isSome
  let (freshPosLs, ssaExt, naExt) := listNextVarRename extendLs ssa na
  let fakeProg := (freshPosLs.map fun r => fakeMove r).foldr .seq .skip
  let (refreshMov, ssaRefreshed, naRefreshed) :=
    listNextVarRenameMove ssaExt naExt refreshLs
  (.seq fakeProg refreshMov, ssaRefreshed, naRefreshed)

end Flapjack.Compiler.Backend.WordAlloc
