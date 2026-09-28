/-
Untagged Flapjack infrastructure: preservation of the globals shape map through
the exact shared-memory step helpers.

HOL `evaluate_global_shape_invariant` (`cakeml/pancake/semantics/panPropsScript.sml:1183`)
proves that evaluation preserves, for every global name, the shape of its value.
The exact shared-memory helpers are the only nonrecursive steps that write a
`kvar` (and none of them writes a global except `sh_mem_load`, whose evaluate
clause guards the destination with `lookup_kvar = SOME (ValWord _)`); this file
records the broad (`PanSemStateExact`) shape preservation used by the faithful
port of that HOL theorem.  No `@[hol]` tag: this is carrier/bookkeeping
infrastructure, not a standalone HOL declaration.
-/
import Flapjack.Pancake.Semantics.PanSem.TickShMemExact

open Flapjack.Pancake.PanLang

namespace Flapjack

/-- Shape map of a broad exact state's globals table. -/
def globalsShapesExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) : MlS → Option ShapeHOL :=
  fun name => (state.globals name).map shapeOfHOLExact

@[simp] theorem globalsShapesExact_emptyLocalsHOLExact {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) :
    globalsShapesExact (emptyLocalsHOLExact state) = globalsShapesExact state := rfl

/-- `shape_of (Val _) = One`, local copy of `shapeOfHOLExact_val` (not importable
    from this module because `PanProps` is downstream). -/
theorem shapeOfHOLExact_val_local {width : Nat} [NeZero width] (value : HolWordLab width) :
    shapeOfHOLExact (.val value : ValueHOL width) = ShapeHOL.one := by
  simp [shapeOfHOLExact]

/-- A successful `isValidValueHOLExact` for a global records the shape of the
    existing value. -/
theorem isValidValueHOLExact_global_shape {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (name : MlS) (value : ValueHOL width)
    (h : isValidValueHOLExact state .global name value = true) :
    (state.globals name).map shapeOfHOLExact = some (shapeOfHOLExact value) := by
  have h' : (match state.globals name with
      | some existing => shapeEqHOL (shapeOfHOLExact value) (shapeOfHOLExact existing)
      | none => false) = true := h
  cases hg : state.globals name with
  | none => simp [hg] at h'
  | some existing =>
      simp only [hg] at h'
      have hs : shapeOfHOLExact value = shapeOfHOLExact existing :=
        (shapeEqHOL_eq_true _ _).mp h'
      simp only [Option.map_some]
      exact congrArg some hs.symm

/-- The broad assign step preserves the globals shape map. -/
theorem assignStepHOLExact_globalsShapesExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (kind : VarKind) (name : MlS)
    (source : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    globalsShapesExact (assignStepHOLExact state kind name source evalExpression).2 =
      globalsShapesExact state := by
  unfold assignStepHOLExact
  split
  · rename_i value heval
    split
    · rename_i hvalid
      cases kind
      · rfl
      · funext key
        have hshape := isValidValueHOLExact_global_shape state name value hvalid
        by_cases hk : key = name
        · subst hk
          simp only [globalsShapesExact, setKvarHOLExact, if_true, Option.map_some]
          exact hshape.symm
        · simp only [globalsShapesExact, setKvarHOLExact, if_neg hk]
    · rfl
  · rfl

/-- The broad shared-memory load helper preserves the globals shape map whenever
    its destination already holds a word (the guard the HOL evaluate clause
    imposes before calling `sh_mem_load`). -/
theorem shMemLoadHOLExact_globalsShapesExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (kind : VarKind) (name : MlS) (address : RiscV.Word width) (nb : Nat)
    (word : RiscV.Word width)
    (hlocal : lookupKvarHOLExact kind name state = some (.val (.word word))) :
    globalsShapesExact (shMemLoadHOLExact state kind name address nb).2 =
      globalsShapesExact state := by
  unfold shMemLoadHOLExact
  by_cases hzero : nb = 0
  · rw [if_pos hzero]
    by_cases hdomain : state.shMemaddrs address
    · rw [if_pos hdomain]
      generalize hffi : callFFIHOL state.ffi (.sharedMem .mappedRead)
          [BitVec.ofNat 8 nb] (panWordToBytesHOL address false) = ffiResult
      cases ffiResult with
      | final event => simp
      | ret newFfi newBytes =>
          cases kind
          · rfl
          · funext key
            by_cases hk : key = name
            · subst hk
              simp only [lookupKvarHOLExact] at hlocal
              simp only [globalsShapesExact, setKvarHOLExact, if_true, hlocal,
                Option.map_some, shapeOfHOLExact_val_local]
            · simp only [globalsShapesExact, setKvarHOLExact, if_neg hk]
    · rw [if_neg hdomain]
  · rw [if_neg hzero]
    by_cases hdomain : state.shMemaddrs (panByteAlignHOL address)
    · rw [if_pos hdomain]
      generalize hffi : callFFIHOL state.ffi (.sharedMem .mappedRead)
          [BitVec.ofNat 8 nb] (panWordToBytesHOL address false) = ffiResult
      cases ffiResult with
      | final event => simp
      | ret newFfi newBytes =>
          cases kind
          · rfl
          · funext key
            by_cases hk : key = name
            · subst hk
              simp only [lookupKvarHOLExact] at hlocal
              simp only [globalsShapesExact, setKvarHOLExact, if_true, hlocal,
                Option.map_some, shapeOfHOLExact_val_local]
            · simp only [globalsShapesExact, setKvarHOLExact, if_neg hk]
    · rw [if_neg hdomain]

/-- The broad shared-memory store helper never writes a global. -/
theorem shMemStoreHOLExact_globalsShapesExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (word address : RiscV.Word width) (nb : Nat) :
    globalsShapesExact (shMemStoreHOLExact state word address nb).2 =
      globalsShapesExact state := by
  unfold shMemStoreHOLExact
  repeat (first | split | rfl)

/-- Broad `ShMemLoad` clause preserves the globals shape map. -/
theorem shMemLoadClauseHOLExact_globalsShapesExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    globalsShapesExact
        (shMemLoadClauseHOLExact state operator kind name address evalExpression).2 =
      globalsShapesExact state := by
  unfold shMemLoadClauseHOLExact
  split
  · rename_i addr haddr
    split
    · rename_i word hlocal
      exact shMemLoadHOLExact_globalsShapesExact state kind name addr (nbOpHOL operator)
        word hlocal
    · rfl
  · rfl

/-- Broad `ShMemStore` clause preserves the globals shape map. -/
theorem shMemStoreClauseHOLExact_globalsShapesExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.shMemaddrs]
    (operator : OpSize) (address value : ExpHOL width)
    (evalExpression : PanSemStateExact width σ → ExpHOL width → Option (ValueHOL width)) :
    globalsShapesExact
        (shMemStoreClauseHOLExact state operator address value evalExpression).2 =
      globalsShapesExact state := by
  unfold shMemStoreClauseHOLExact shMemStoreHOLExact
  repeat (first | split | rfl)

end Flapjack
