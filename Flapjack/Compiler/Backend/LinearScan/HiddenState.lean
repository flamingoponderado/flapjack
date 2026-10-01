import Flapjack.HolRef
import Flapjack.Compiler.Backend.LinearScan
import Flapjack.Compiler.Backend.RegAlloc.Exceptions
import Flapjack.Translator.Monadic.MonadBase.Arrays

/-!
# linear_scan state and interval monad

Ports of `linear_scanScript.sml:314-495`: the colouring state, the hidden
fixed-array state of the state-exception monad, the array accessors generated
by `define_MFarray_manip_funs` (`colors_sub` etc., fetched at
`linear_scanScript.sml:382-400`), and the monadic interval computation.

The generated accessors are `Marray_length`/`Marray_sub`/`Marray_update` on
the field getter `\s. s.f` and setter `\x s. s with f := x`, with the reg_alloc
`state_exn` constructor `Subscript` for out-of-range indices. HOL's monad
`do` blocks are `st_ex_bind`/`st_ex_ignore_bind`/`st_ex_return`; a pattern
binder `(a, b) <- m` is a pattern-matching lambda. These are proof-side ports:
the executed allocator is not routed through them.
-/

namespace Flapjack.LinearScan

open Flapjack.RegAlloc Flapjack.Translator.Monadic.MonadBase

/-- HOL `linear_scan_state` (`linear_scanScript.sml:314-323`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_scan_state"]
structure LinearScanState where
  active : List (Int × Nat)
  colorpool : List Nat
  phyregs : NumSet
  colornum : Nat
  colormax : Nat
  stacknum : Nat
  deriving Repr, DecidableEq

/-- HOL `linear_scan_hidden_state` (`linear_scanScript.sml:325-333`); each
field is a HOL list used as a fixed array. -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "linear_scan_hidden_state"]
structure LinearScanHiddenState where
  colors : List Nat
  int_beg : List Int
  int_end : List Int
  sorted_regs : List Nat
  sorted_moves : List (Nat × (Nat × Nat))
  deriving Repr, DecidableEq

/-- The linear-scan state-exception monad over the hidden state. -/
abbrev LsM (value : Type) := M LinearScanHiddenState value StateException

/-- Generated `colors_length` (`linear_scanScript.sml:382`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "colors_length_def"]
def colorsLength : LsM Nat := arrayLength (fun s => s.colors)
/-- Generated `colors_sub` (`linear_scanScript.sml:383`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "colors_sub_def"]
def colorsSub : Nat → LsM Nat := arraySub (fun s => s.colors) .Subscript
/-- Generated `update_colors` (`linear_scanScript.sml:384`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "update_colors_def"]
def updateColors : Nat → Nat → LsM Unit :=
  arrayUpdate (fun s => s.colors) (fun x s => { s with colors := x }) .Subscript

/-- Generated `int_beg_length` (`linear_scanScript.sml:386`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "int_beg_length_def"]
def intBegLength : LsM Nat := arrayLength (fun s => s.int_beg)
/-- Generated `int_beg_sub` (`linear_scanScript.sml:387`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "int_beg_sub_def"]
def intBegSub : Nat → LsM Int := arraySub (fun s => s.int_beg) .Subscript
/-- Generated `update_int_beg` (`linear_scanScript.sml:388`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "update_int_beg_def"]
def updateIntBeg : Nat → Int → LsM Unit :=
  arrayUpdate (fun s => s.int_beg) (fun x s => { s with int_beg := x }) .Subscript

/-- Generated `int_end_length` (`linear_scanScript.sml:390`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "int_end_length_def"]
def intEndLength : LsM Nat := arrayLength (fun s => s.int_end)
/-- Generated `int_end_sub` (`linear_scanScript.sml:391`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "int_end_sub_def"]
def intEndSub : Nat → LsM Int := arraySub (fun s => s.int_end) .Subscript
/-- Generated `update_int_end` (`linear_scanScript.sml:392`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "update_int_end_def"]
def updateIntEnd : Nat → Int → LsM Unit :=
  arrayUpdate (fun s => s.int_end) (fun x s => { s with int_end := x }) .Subscript

/-- Generated `sorted_regs_length` (`linear_scanScript.sml:394`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sorted_regs_length_def"]
def sortedRegsLength : LsM Nat := arrayLength (fun s => s.sorted_regs)
/-- Generated `sorted_regs_sub` (`linear_scanScript.sml:395`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sorted_regs_sub_def"]
def sortedRegsSub : Nat → LsM Nat := arraySub (fun s => s.sorted_regs) .Subscript
/-- Generated `update_sorted_regs` (`linear_scanScript.sml:396`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "update_sorted_regs_def"]
def updateSortedRegs : Nat → Nat → LsM Unit :=
  arrayUpdate (fun s => s.sorted_regs) (fun x s => { s with sorted_regs := x }) .Subscript

/-- Generated `sorted_moves_length` (`linear_scanScript.sml:398`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sorted_moves_length_def"]
def sortedMovesLength : LsM Nat := arrayLength (fun s => s.sorted_moves)
/-- Generated `sorted_moves_sub` (`linear_scanScript.sml:399`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "sorted_moves_sub_def"]
def sortedMovesSub : Nat → LsM (Nat × (Nat × Nat)) :=
  arraySub (fun s => s.sorted_moves) .Subscript
/-- Generated `update_sorted_moves` (`linear_scanScript.sml:400`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "update_sorted_moves_def"]
def updateSortedMoves : Nat → (Nat × (Nat × Nat)) → LsM Unit :=
  arrayUpdate (fun s => s.sorted_moves) (fun x s => { s with sorted_moves := x }) .Subscript

/-- Monadic `numset_list_add_if_lt` over the `int_beg` array
(`linear_scanScript.sml:402-424`); note the source's `0 < begr` test
(unset beginnings are initialised to 1). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "numset_list_add_if_lt_monad_def"]
def numsetListAddIfLtMonad : List Nat → Int → LsM Unit
  | [], _v => ret ()
  | r :: rs, v =>
      bind (intBegSub r) fun begr =>
        if 0 < begr then
          ignoreBind (updateIntBeg r v) (numsetListAddIfLtMonad rs v)
        else if v ≤ begr then
          ignoreBind (updateIntBeg r v) (numsetListAddIfLtMonad rs v)
        else numsetListAddIfLtMonad rs v

/-- Monadic `numset_list_add_if_gt` over the `int_end` array
(`linear_scanScript.sml:426-448`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "numset_list_add_if_gt_monad_def"]
def numsetListAddIfGtMonad : List Nat → Int → LsM Unit
  | [], _v => ret ()
  | r :: rs, v =>
      bind (intEndSub r) fun begr =>
        if 0 < begr then
          ignoreBind (updateIntEnd r v) (numsetListAddIfGtMonad rs v)
        else if begr ≤ v then
          ignoreBind (updateIntEnd r v) (numsetListAddIfGtMonad rs v)
        else numsetListAddIfGtMonad rs v

/-- Monadic `get_intervals_ct_aux` (`linear_scanScript.sml:450-485`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml"
  "get_intervals_ct_monad_aux_def"]
def getIntervalsCtMonadAux : ClashTree → Int → NumSet → LsM (Int × NumSet)
  | .delta wr rd, n, live =>
      ignoreBind (numsetListAddIfLtMonad wr n)
        (ignoreBind (numsetListAddIfGtMonad wr n)
          (ignoreBind (numsetListAddIfGtMonad rd (n - 1))
            (ret (n - 2, numsetListInsert rd (numsetListDelete wr live)))))
  | .set cutset, n, live =>
      ignoreBind (numsetListAddIfGtMonad ((sptToAList cutset).map Prod.fst) n)
        (ret (n - 1, sptUnion cutset live))
  | .branch optcutset ct1 ct2, n, live =>
      bind (getIntervalsCtMonadAux ct2 n live) fun (n2, live2) =>
        bind (getIntervalsCtMonadAux ct1 n2 live) fun (n1, live1) =>
          match optcutset with
          | none => ret (n1, sptUnion live1 live2)
          | some cutset =>
              ignoreBind (numsetListAddIfGtMonad ((sptToAList cutset).map Prod.fst) n1)
                (ret (n1 - 1, sptUnion cutset (sptUnion live1 live2)))
  | .seq ct1 ct2, n, live =>
      bind (getIntervalsCtMonadAux ct2 n live) fun (n2, live2) =>
        getIntervalsCtMonadAux ct1 n2 live2

/-- Monadic `get_intervals_ct` (`linear_scanScript.sml:487-495`). -/
@[hol "cakeml/compiler/backend/reg_alloc/linear_scanScript.sml" "get_intervals_ct_monad_def"]
def getIntervalsCtMonad (ct : ClashTree) : LsM Int :=
  bind (getIntervalsCtMonadAux ct 0 .ln) fun (n, live) =>
    ignoreBind (numsetListAddIfLtMonad ((sptToAList live).map Prod.fst) n)
      (ignoreBind (numsetListAddIfGtMonad ((sptToAList live).map Prod.fst) n)
        (ret (n - 1)))

end Flapjack.LinearScan
