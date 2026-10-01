import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Carriers
import Flapjack.Compiler.Backend.RegAlloc.Exceptions
import Flapjack.Translator.Monadic.MonadBase.Arrays

/-!
# reg_alloc generated state accessors

The accessors that `ml_monadBaseLib` generates for `ra_state` in `reg_allocScript.sml`.
`define_monad_access_funs ``:ra_state``` (line 83) gives `get_F`/`set_F` for each of the
twelve fields: `get_F = λstate. (M_success state.F, state)` and
`set_F x = λstate. (M_success (), state with F := x)`, polymorphic in the exception type
as in HOL. `define_MFarray_manip_funs` (lines 113-115) gives, for the five array fields,
`F_length = Marray_length (λstate. state.F)` (exception type also polymorphic),
`F_sub = Marray_sub (λstate. state.F) Subscript`, and
`update_F = Marray_update (λstate. state.F) (λx state. state with F := x) Subscript`.
The generated names are recognized by `scripts/hol_sml_declarations.py`
`monad_accessor_declarations`. These are proof-side ports: the executed allocator
is not routed through them.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- Generated `get_adj_ls` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_adj_ls_def"]
def getAdjLs {γ : Type} : M State (List (List Nat)) γ :=
  fun state => (.success state.adj_ls, state)
/-- Generated `set_adj_ls` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_adj_ls_def"]
def setAdjLs {γ : Type} (x : List (List Nat)) : M State Unit γ :=
  fun state => (.success (), { state with adj_ls := x })

/-- Generated `get_node_tag` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_node_tag_def"]
def getNodeTag {γ : Type} : M State (List Tag) γ :=
  fun state => (.success state.node_tag, state)
/-- Generated `set_node_tag` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_node_tag_def"]
def setNodeTag {γ : Type} (x : List Tag) : M State Unit γ :=
  fun state => (.success (), { state with node_tag := x })

/-- Generated `get_degrees` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_degrees_def"]
def getDegrees {γ : Type} : M State (List Nat) γ :=
  fun state => (.success state.degrees, state)
/-- Generated `set_degrees` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_degrees_def"]
def setDegrees {γ : Type} (x : List Nat) : M State Unit γ :=
  fun state => (.success (), { state with degrees := x })

/-- Generated `get_dim` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_dim_def"]
def getDim {γ : Type} : M State (Nat) γ :=
  fun state => (.success state.dim, state)
/-- Generated `set_dim` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_dim_def"]
def setDim {γ : Type} (x : Nat) : M State Unit γ :=
  fun state => (.success (), { state with dim := x })

/-- Generated `get_simp_wl` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_simp_wl_def"]
def getSimpWl {γ : Type} : M State (List Nat) γ :=
  fun state => (.success state.simp_wl, state)
/-- Generated `set_simp_wl` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_simp_wl_def"]
def setSimpWl {γ : Type} (x : List Nat) : M State Unit γ :=
  fun state => (.success (), { state with simp_wl := x })

/-- Generated `get_spill_wl` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_spill_wl_def"]
def getSpillWl {γ : Type} : M State (List Nat) γ :=
  fun state => (.success state.spill_wl, state)
/-- Generated `set_spill_wl` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_spill_wl_def"]
def setSpillWl {γ : Type} (x : List Nat) : M State Unit γ :=
  fun state => (.success (), { state with spill_wl := x })

/-- Generated `get_freeze_wl` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_freeze_wl_def"]
def getFreezeWl {γ : Type} : M State (List Nat) γ :=
  fun state => (.success state.freeze_wl, state)
/-- Generated `set_freeze_wl` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_freeze_wl_def"]
def setFreezeWl {γ : Type} (x : List Nat) : M State Unit γ :=
  fun state => (.success (), { state with freeze_wl := x })

/-- Generated `get_avail_moves_wl` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_avail_moves_wl_def"]
def getAvailMovesWl {γ : Type} : M State (List (Nat × (Nat × Nat))) γ :=
  fun state => (.success state.avail_moves_wl, state)
/-- Generated `set_avail_moves_wl` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_avail_moves_wl_def"]
def setAvailMovesWl {γ : Type} (x : List (Nat × (Nat × Nat))) : M State Unit γ :=
  fun state => (.success (), { state with avail_moves_wl := x })

/-- Generated `get_unavail_moves_wl` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_unavail_moves_wl_def"]
def getUnavailMovesWl {γ : Type} : M State (List (Nat × (Nat × Nat))) γ :=
  fun state => (.success state.unavail_moves_wl, state)
/-- Generated `set_unavail_moves_wl` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_unavail_moves_wl_def"]
def setUnavailMovesWl {γ : Type} (x : List (Nat × (Nat × Nat))) : M State Unit γ :=
  fun state => (.success (), { state with unavail_moves_wl := x })

/-- Generated `get_coalesced` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_coalesced_def"]
def getCoalesced {γ : Type} : M State (List Nat) γ :=
  fun state => (.success state.coalesced, state)
/-- Generated `set_coalesced` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_coalesced_def"]
def setCoalesced {γ : Type} (x : List Nat) : M State Unit γ :=
  fun state => (.success (), { state with coalesced := x })

/-- Generated `get_move_related` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_move_related_def"]
def getMoveRelated {γ : Type} : M State (List Bool) γ :=
  fun state => (.success state.move_related, state)
/-- Generated `set_move_related` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_move_related_def"]
def setMoveRelated {γ : Type} (x : List Bool) : M State Unit γ :=
  fun state => (.success (), { state with move_related := x })

/-- Generated `get_stack` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "get_stack_def"]
def getStack {γ : Type} : M State (List Nat) γ :=
  fun state => (.success state.stack, state)
/-- Generated `set_stack` (`reg_allocScript.sml:83`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "set_stack_def"]
def setStack {γ : Type} (x : List Nat) : M State Unit γ :=
  fun state => (.success (), { state with stack := x })

/-- Generated `adj_ls_length` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "adj_ls_length_def"]
def adjLsLength {γ : Type} : M State Nat γ := arrayLength (fun state => state.adj_ls)
/-- Generated `adj_ls_sub` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "adj_ls_sub_def"]
def adjLsSub : Nat → M State (List Nat) StateException :=
  arraySub (fun state => state.adj_ls) .Subscript
/-- Generated `update_adj_ls` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "update_adj_ls_def"]
def updateAdjLs : Nat → List Nat → M State Unit StateException :=
  arrayUpdate (fun state => state.adj_ls) (fun x state => { state with adj_ls := x })
    .Subscript

/-- Generated `node_tag_length` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "node_tag_length_def"]
def nodeTagLength {γ : Type} : M State Nat γ := arrayLength (fun state => state.node_tag)
/-- Generated `node_tag_sub` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "node_tag_sub_def"]
def nodeTagSub : Nat → M State (Tag) StateException :=
  arraySub (fun state => state.node_tag) .Subscript
/-- Generated `update_node_tag` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "update_node_tag_def"]
def updateNodeTag : Nat → Tag → M State Unit StateException :=
  arrayUpdate (fun state => state.node_tag) (fun x state => { state with node_tag := x })
    .Subscript

/-- Generated `degrees_length` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "degrees_length_def"]
def degreesLength {γ : Type} : M State Nat γ := arrayLength (fun state => state.degrees)
/-- Generated `degrees_sub` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "degrees_sub_def"]
def degreesSub : Nat → M State (Nat) StateException :=
  arraySub (fun state => state.degrees) .Subscript
/-- Generated `update_degrees` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "update_degrees_def"]
def updateDegrees : Nat → Nat → M State Unit StateException :=
  arrayUpdate (fun state => state.degrees) (fun x state => { state with degrees := x })
    .Subscript

/-- Generated `coalesced_length` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "coalesced_length_def"]
def coalescedLength {γ : Type} : M State Nat γ := arrayLength (fun state => state.coalesced)
/-- Generated `coalesced_sub` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "coalesced_sub_def"]
def coalescedSub : Nat → M State (Nat) StateException :=
  arraySub (fun state => state.coalesced) .Subscript
/-- Generated `update_coalesced` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "update_coalesced_def"]
def updateCoalesced : Nat → Nat → M State Unit StateException :=
  arrayUpdate (fun state => state.coalesced) (fun x state => { state with coalesced := x })
    .Subscript

/-- Generated `move_related_length` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "move_related_length_def"]
def moveRelatedLength {γ : Type} : M State Nat γ := arrayLength (fun state => state.move_related)
/-- Generated `move_related_sub` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "move_related_sub_def"]
def moveRelatedSub : Nat → M State (Bool) StateException :=
  arraySub (fun state => state.move_related) .Subscript
/-- Generated `update_move_related` (`reg_allocScript.sml:113-115`). -/
@[hol "cakeml/compiler/backend/reg_alloc/reg_allocScript.sml" "update_move_related_def"]
def updateMoveRelated : Nat → Bool → M State Unit StateException :=
  arrayUpdate (fun state => state.move_related) (fun x state => { state with move_related := x })
    .Subscript

end Flapjack.RegAlloc
