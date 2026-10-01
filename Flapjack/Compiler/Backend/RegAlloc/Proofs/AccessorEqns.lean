import Flapjack.HolRef
import Flapjack.Compiler.Backend.RegAlloc.Accessors
import Flapjack.Compiler.Backend.RegAlloc.StateMap
import Flapjack.Misc.ListEl

/-!
# reg_allocProof accessor rewriting lemmas

The case-distribution and array accessor equations of
`reg_allocProofScript.sml:95-292`. HOL `LUPDATE x n l` is `l.set n x`.

The `Msub`/`*_sub` and `st_ex_MAP *_sub` equations read HOL `EL`, rendered by the
exact tagged `Flapjack.holEl` (HOL `listScript.sml` `EL_def`, pinned HOL submodule,
provenance bead flapjack-pxn.18.5.15.3.38.1); they were re-reviewed individually after
that approval (bead flapjack-pxn.18.5.15.3.38.2). The `EL`-free `Mupdate`/`update_*`
and case equations are exact. HOL's
`case_eq_thms` (line 95), an SML-assembled list of `TypeBase.case_eq_of`
conjuncts used only as a simp set, is not ported.
-/

namespace Flapjack.RegAlloc

open Flapjack.Translator.Monadic.MonadBase

/-- `tag` is inhabited, so HOL `EL` over `tag list` is defined (Flapjack
infrastructure, no HOL counterpart). -/
instance tagNonempty : Nonempty Tag := ⟨.Atemp⟩

/-- Exact HOL `tag_case_st` (`reg_allocProofScript.sml:100-105`): a `tag` case of
functions applied to `f` is the case of the applied branches. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "tag_case_st"]
theorem tagCaseSt {α β : Type} (a : Nat → α → β) (b c : α → β) (f : α) :
    ∀ t : Tag,
      (match t with
        | .Fixed n => a n
        | .Atemp => b
        | .Stemp => c) f =
      (match t with
        | .Fixed n => a n f
        | .Atemp => b f
        | .Stemp => c f)
  | .Fixed _ => rfl
  | .Atemp => rfl
  | .Stemp => rfl

/-- Exact HOL `list_case_st` (`reg_allocProofScript.sml:107-112`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "list_case_st"]
theorem listCaseSt {α β γ : Type} (a : α → β) (b : γ → List γ → α → β) (f : α) :
    ∀ t : List γ,
      (match t with
        | [] => a
        | x :: y => b x y) f =
      (match t with
        | [] => a f
        | x :: y => b x y f)
  | [] => rfl
  | _ :: _ => rfl

/-- Exact HOL `Msub_eqn` (`reg_allocProofScript.sml:125-136`).
HOL's unused `v` binder is omitted. -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "Msub_eqn"]
theorem msubEqn {α ε : Type} [Nonempty α] :
    ∀ (e : ε) (n : Nat) (ls : List α),
      mSub e n ls = if n < ls.length then .success (holEl n ls) else .failure e := by
  intro e n ls
  induction ls generalizing n with
  | nil => simp [mSub]
  | cons x xs ih =>
      cases n with
      | zero => simp [mSub, holEl, holHd]
      | succ n =>
          simp only [mSub, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, ih,
            List.length_cons, Nat.add_lt_add_iff_right, holEl_cons_succ]

/-- Exact HOL `Mupdate_eqn` (`reg_allocProofScript.sml:192-205`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "Mupdate_eqn"]
theorem mupdateEqn {α ε : Type} :
    ∀ (e : ε) (x : α) (n : Nat) (ls : List α),
      mUpdate e x n ls = if n < ls.length then .success (ls.set n x) else .failure e := by
  intro e x n ls
  induction ls generalizing n with
  | nil => simp [mUpdate]
  | cons y ys ih =>
      cases n with
      | zero => simp [mUpdate]
      | succ n =>
          simp only [mUpdate, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, ih,
            List.length_cons, Nat.add_lt_add_iff_right]
          by_cases h : n < ys.length <;> simp [h]

/-- The generated `update_F` accessor over the `mUpdate` equation (Flapjack
infrastructure for the five exact `update_*_eqn` cases). -/
private theorem arrayUpdateEqn {σ α : Type} (get : σ → List α) (set : List α → σ → σ)
    (n : Nat) (t : α) (s : σ) :
    arrayUpdate get set StateException.Subscript n t s =
      if n < (get s).length then (.success (), set ((get s).set n t) s)
      else (.failure .Subscript, s) := by
  unfold arrayUpdate
  rw [mupdateEqn]
  by_cases h : n < (get s).length <;> simp [h]

/-- Exact HOL `update_adj_ls_eqn` (`reg_allocProofScript.sml:207-216`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "update_adj_ls_eqn"]
theorem updateAdjLsEqn (n : Nat) (t : List Nat) (s : State) :
    updateAdjLs n t s =
      if n < s.adj_ls.length then (.success (), { s with adj_ls := s.adj_ls.set n t })
      else (.failure .Subscript, s) :=
  arrayUpdateEqn _ _ n t s

/-- Exact HOL `update_node_tag_eqn` (`reg_allocProofScript.sml:218-227`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "update_node_tag_eqn"]
theorem updateNodeTagEqn (n : Nat) (t : Tag) (s : State) :
    updateNodeTag n t s =
      if n < s.node_tag.length then (.success (), { s with node_tag := s.node_tag.set n t })
      else (.failure .Subscript, s) :=
  arrayUpdateEqn _ _ n t s

/-- Exact HOL `update_degrees_eqn` (`reg_allocProofScript.sml:229-238`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "update_degrees_eqn"]
theorem updateDegreesEqn (n : Nat) (t : Nat) (s : State) :
    updateDegrees n t s =
      if n < s.degrees.length then (.success (), { s with degrees := s.degrees.set n t })
      else (.failure .Subscript, s) :=
  arrayUpdateEqn _ _ n t s

/-- Exact HOL `update_coalesced_eqn` (`reg_allocProofScript.sml:240-249`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "update_coalesced_eqn"]
theorem updateCoalescedEqn (n : Nat) (t : Nat) (s : State) :
    updateCoalesced n t s =
      if n < s.coalesced.length then (.success (), { s with coalesced := s.coalesced.set n t })
      else (.failure .Subscript, s) :=
  arrayUpdateEqn _ _ n t s

/-- Exact HOL `update_move_related_eqn` (`reg_allocProofScript.sml:251-260`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml"
  "update_move_related_eqn"]
theorem updateMoveRelatedEqn (n : Nat) (t : Bool) (s : State) :
    updateMoveRelated n t s =
      if n < s.move_related.length then
        (.success (), { s with move_related := s.move_related.set n t })
      else (.failure .Subscript, s) :=
  arrayUpdateEqn _ _ n t s

/-- The generated `F_sub` accessor over the `Msub` equation (Flapjack
infrastructure for the `*_sub_eqn` cases). -/
private theorem arraySubEqn {σ α : Type} [Nonempty α] (get : σ → List α) (n : Nat) (s : σ) :
    arraySub get StateException.Subscript n s =
      if n < (get s).length then (.success (holEl n (get s)), s)
      else (.failure .Subscript, s) := by
  unfold arraySub
  rw [msubEqn]
  by_cases h : n < (get s).length <;> simp [h]

/-- Exact HOL `adj_ls_sub_eqn` (`reg_allocProofScript.sml:138-147`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "adj_ls_sub_eqn"]
theorem adjLsSubEqn (n : Nat) (s : State) :
    adjLsSub n s =
      if n < s.adj_ls.length then (.success (holEl n s.adj_ls), s)
      else (.failure .Subscript, s) :=
  arraySubEqn _ n s

/-- Exact HOL `node_tag_sub_eqn` (`reg_allocProofScript.sml:149-158`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "node_tag_sub_eqn"]
theorem nodeTagSubEqn (n : Nat) (s : State) :
    nodeTagSub n s =
      if n < s.node_tag.length then (.success (holEl n s.node_tag), s)
      else (.failure .Subscript, s) :=
  arraySubEqn _ n s

/-- Exact HOL `degrees_sub_eqn` (`reg_allocProofScript.sml:160-169`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "degrees_sub_eqn"]
theorem degreesSubEqn (n : Nat) (s : State) :
    degreesSub n s =
      if n < s.degrees.length then (.success (holEl n s.degrees), s)
      else (.failure .Subscript, s) :=
  arraySubEqn _ n s

/-- Exact HOL `coalesced_sub` (`reg_allocProofScript.sml:171-179`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "coalesced_sub"]
theorem coalescedSubEqn (n : Nat) (s : State) :
    coalescedSub n s =
      if n < s.coalesced.length then (.success (holEl n s.coalesced), s)
      else (.failure .Subscript, s) :=
  arraySubEqn _ n s

/-- Exact HOL `move_related_sub` (`reg_allocProofScript.sml:181-189`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "move_related_sub"]
theorem moveRelatedSubEqn (n : Nat) (s : State) :
    moveRelatedSub n s =
      if n < s.move_related.length then (.success (holEl n s.move_related), s)
      else (.failure .Subscript, s) :=
  arraySubEqn _ n s

/-- `st_ex_MAP` of an array `sub` over in-range indices (Flapjack infrastructure for
the three `st_ex_MAP_*_sub` cases). -/
private theorem stExMapArraySub {α : Type} [Nonempty α] (get : State → List α) :
    ∀ (ls : List Nat) (s : State), (∀ v ∈ ls, v < (get s).length) →
      stExMap (arraySub get StateException.Subscript) ls s =
        (.success (ls.map fun i => holEl i (get s)), s)
  | [], s, _ => rfl
  | v :: ls, s, h => by
      have hv : v < (get s).length := h v List.mem_cons_self
      have ih := stExMapArraySub get ls s (fun w hw => h w (List.mem_cons_of_mem _ hw))
      simp only [stExMap, Flapjack.Translator.Monadic.MonadBase.bind,
        Flapjack.Translator.Monadic.MonadBase.ret, arraySubEqn, hv, if_true, ih, List.map_cons]

/-- Exact HOL `st_ex_MAP_node_tag_sub` (`reg_allocProofScript.sml:269-275`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_MAP_node_tag_sub"]
theorem stExMapNodeTagSub :
    ∀ (ls : List Nat) (s : State), (∀ v ∈ ls, v < s.node_tag.length) →
      stExMap nodeTagSub ls s = (.success (ls.map fun i => holEl i s.node_tag), s) :=
  stExMapArraySub (fun s => s.node_tag)

/-- Exact HOL `st_ex_MAP_adj_ls_sub` (`reg_allocProofScript.sml:277-283`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_MAP_adj_ls_sub"]
theorem stExMapAdjLsSub :
    ∀ (ls : List Nat) (s : State), (∀ v ∈ ls, v < s.adj_ls.length) →
      stExMap adjLsSub ls s = (.success (ls.map fun i => holEl i s.adj_ls), s) :=
  stExMapArraySub (fun s => s.adj_ls)

/-- Exact HOL `st_ex_MAP_degrees_sub` (`reg_allocProofScript.sml:285-291`). -/
@[hol "cakeml/compiler/backend/reg_alloc/proofs/reg_allocProofScript.sml" "st_ex_MAP_degrees_sub"]
theorem stExMapDegreesSub :
    ∀ (ls : List Nat) (s : State), (∀ v ∈ ls, v < s.degrees.length) →
      stExMap degreesSub ls s = (.success (ls.map fun i => holEl i s.degrees), s) :=
  stExMapArraySub (fun s => s.degrees)

end Flapjack.RegAlloc
