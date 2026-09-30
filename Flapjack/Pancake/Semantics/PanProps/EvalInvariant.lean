import Flapjack.HolRef
import Flapjack.FiniteMap.Basic
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Semantics.PanSem.StateExactFinite
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanSem.EvalExact
import Flapjack.Pancake.Semantics.PanSem.EvaluateDeclsExact
import Flapjack.Pancake.Semantics.PanSem.DecCallExact
import Flapjack.Pancake.Semantics.PanSem.FiniteSupportStep
import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
import Flapjack.Pancake.Semantics.PanSem.EvaluateInd

/-!
Finite-map carrier and expression invariant for the HOL `eval_is_wf_shape_v`
prerequisite to `evaluate_is_wf_shape_invariant`. This submodule sits under
the `panPropsScript.sml` counterpart; its carrier owns the map fields named by
the representation qualifier and is invertibly related to `PanSemStateExact`.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
  (MlS StructContextExact ProgHOL ExpHOL ShapeHOL DeclHOL FunDeclHOL isWfShapeExactHOL varExpHOL
   functionsHOL exceptionsHOL isFunctionHOL isNameHOL isExnDeclHOL)

/-! ## Clearing `locals` under the exact broad evaluator

The HOL theorem `panProps$eval_empty_locals_IMP`
(`cakeml/pancake/semantics/panPropsScript.sml:1584`) reads the exact `eval`
(`eval_def`). The final tagged port below lives over the reviewed finite-map
carrier `PanPropsEvalStateFiniteExact` (whose `evalHOL` delegates to
`evalHOLExact` through the canonical translation). The broad-carrier proof
support in this section is untagged because `PanSemStateExact` represents the
HOL finite-map fields by unrestricted lookup functions.

`evalHOLExact_emptyLocalsHOLExact` is the untagged broad analogue: evaluation
that succeeds after `locals` is cleared to `FEMPTY` also succeeds in the
original state with the same value. It is proved by the mutual induction
`evalHOLExact.induct` with the list transfer rendered through the tagged
`opt_mmap_eq_some_helper` (`List.mapM` is the repository's `OPT_MMAP`). -/

/-- Decidability of the address set is inherited from the underlying state when
    only `locals` is cleared, so the empty-locals state needs no new decision
    procedure. -/
instance emptyLocalsHOLExactDecidablePred {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
    DecidablePred (emptyLocalsHOLExact state).memaddrs :=
  (inferInstance : DecidablePred state.memaddrs)

@[simp] theorem emptyLocalsHOLExact_structs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).structs = state.structs := rfl

@[simp] theorem emptyLocalsHOLExact_memaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).memaddrs = state.memaddrs := rfl

@[simp] theorem emptyLocalsHOLExact_memory {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).memory = state.memory := rfl

@[simp] theorem emptyLocalsHOLExact_be {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).be = state.be := rfl

@[simp] theorem emptyLocalsHOLExact_baseAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).baseAddr = state.baseAddr := rfl

@[simp] theorem emptyLocalsHOLExact_topAddr {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) :
    (emptyLocalsHOLExact state).topAddr = state.topAddr := rfl

/-- The exact `OPT_MMAP eval` list step is `List.mapM`. -/
private theorem evalListHOLExact_eq_mapM {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (expressions : List (ExpHOL width)) :
    evalListHOLExact state expressions = expressions.mapM (evalHOLExact state) := by
  induction expressions with
  | nil => rfl
  | cons expression rest ih =>
      rw [List.mapM_cons, ← ih]
      simp only [evalListHOLExact]
      cases hx : evalHOLExact state expression with
      | none => simp
      | some value => cases hr : evalListHOLExact state rest with
                      | none => simp
                      | some values => simp

/-- The exact named-struct field-expression step is `List.mapM` with the field
    name reattached. -/
private theorem evalListFieldsHOLExact_eq_mapM {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (fields : List (MlS × ExpHOL width)) :
    evalListFieldsHOLExact state fields =
      fields.mapM (fun pair => (evalHOLExact state pair.2).map (fun value => (pair.1, value))) := by
  induction fields with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨name, expression⟩ := pair
      rw [List.mapM_cons, ← ih]
      simp only [evalListFieldsHOLExact]
      cases hx : evalHOLExact state expression with
      | none => simp
      | some value => cases hr : evalListFieldsHOLExact state rest with
                      | none => simp
                      | some values => simp

/-- Pointwise transfer of an `OPT_MMAP eval` success from the empty-locals state
    to the original state, via `opt_mmap_eq_some_helper`. -/
private theorem evalListHOLExact_transfer_of_pointwise {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (expressions : List (ExpHOL width)) (values : List (ValueHOL width))
    (hpoint : ∀ x ∈ expressions, ∀ y,
      evalHOLExact (emptyLocalsHOLExact state) x = some y → evalHOLExact state x = some y)
    (h : evalListHOLExact (emptyLocalsHOLExact state) expressions = some values) :
    evalListHOLExact state expressions = some values := by
  rw [evalListHOLExact_eq_mapM] at h ⊢
  exact optMmapEqSomeHelper _ _ expressions values h hpoint

/-- Pointwise transfer of a named-struct field-list success from the
    empty-locals state to the original state. -/
private theorem evalListFieldsHOLExact_transfer_of_pointwise {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (fields : List (MlS × ExpHOL width)) (values : List (MlS × ValueHOL width))
    (hpoint : ∀ x ∈ fields.map Prod.snd, ∀ y,
      evalHOLExact (emptyLocalsHOLExact state) x = some y → evalHOLExact state x = some y)
    (h : evalListFieldsHOLExact (emptyLocalsHOLExact state) fields = some values) :
    evalListFieldsHOLExact state fields = some values := by
  rw [evalListFieldsHOLExact_eq_mapM] at h ⊢
  refine optMmapEqSomeHelper _ _ fields values h ?_
  rintro ⟨name, x⟩ hpair y hy
  simp only [Option.map_eq_some_iff] at hy
  obtain ⟨w, hx, rfl⟩ := hy
  have hmem : x ∈ fields.map Prod.snd := List.mem_map.mpr ⟨(name, x), hpair, rfl⟩
  rw [hpoint x hmem w hx]
  rfl

/-- Untagged broad-carrier analogue of HOL `panProps$eval_empty_locals_IMP`
    (`cakeml/pancake/semantics/panPropsScript.sml:1584`): if the exact broad
    evaluator succeeds after clearing `locals` to `FEMPTY`, it succeeds with the
    same value in the original state. The statement reads the raw-function
    `PanSemStateExact`, so it carries no `@[hol]` tag; the tagged finite-map port
    is `PanPropsEvalStateFiniteExact.evalEmptyLocalsHOLFinite` below. -/
theorem evalHOLExact_emptyLocalsHOLExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs] :
    ∀ (expression : ExpHOL width) (value : ValueHOL width),
      evalHOLExact (emptyLocalsHOLExact state) expression = some value →
        evalHOLExact state expression = some value := by
  intro expression
  induction expression using evalHOLExact.induct (state := state)
    (motive_2 := fun fields => ∀ x ∈ fields.map Prod.snd, ∀ y,
      evalHOLExact (emptyLocalsHOLExact state) x = some y → evalHOLExact state x = some y)
    (motive_3 := fun expressions => ∀ x ∈ expressions, ∀ y,
      evalHOLExact (emptyLocalsHOLExact state) x = some y → evalHOLExact state x = some y)
  case case1 => intro v h; simpa [evalHOLExact] using h
  case case2 => intro v h
                simp only [evalHOLExact, emptyLocalsHOLExact_locals] at h; cases h
  case case3 => intro v h
                simpa [evalHOLExact, emptyLocalsHOLExact_globals] using h
  case case4 =>
    rename_i fields ih3
    intro v h
    cases hl : evalListHOLExact (emptyLocalsHOLExact state) fields with
    | none => rw [evalHOLExact, hl] at h; cases h
    | some values =>
        have hstate := evalListHOLExact_transfer_of_pointwise state fields values ih3 hl
        rw [evalHOLExact, hl] at h
        simp only [Option.map_some, Option.some.injEq] at h
        cases h
        rw [evalHOLExact, hstate]; rfl
  case case5 =>
    rename_i index value values hstruct ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) value with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ => rw [evalHOLExact, hw] at h; cases h
        | rStruct vals => rw [evalHOLExact, hw] at h; rw [evalHOLExact, hs]; exact h
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case6 =>
    rename_i index value hno ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) value with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        cases w with
        | val wv =>
            cases wv with
            | word _ => rw [evalHOLExact, hw] at h; cases h
        | rStruct vals => exact (hno vals (ih (.rStruct vals) hw)).elim
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case7 =>
    rename_i name fields hlookup
    intro v h
    simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup] at h; cases h
  case case8 =>
    rename_i name fields info hlookup hnames heval ih2
    intro v h
    cases he : evalListFieldsHOLExact (emptyLocalsHOLExact state) fields with
    | none => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnames, he] at h; cases h
    | some values =>
        have hstate := evalListFieldsHOLExact_transfer_of_pointwise state fields values ih2 he
        rw [hstate] at heval; cases heval
  case case9 =>
    rename_i name fields info hlookup hnames fieldValues heval hcheck ih2
    intro v h
    cases he : evalListFieldsHOLExact (emptyLocalsHOLExact state) fields with
    | none => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnames, he] at h; cases h
    | some fv' =>
        have hstate := evalListFieldsHOLExact_transfer_of_pointwise state fields fv' ih2 he
        simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnames, he] at h
        simp only [evalHOLExact, hlookup, hnames, hstate]
        exact h
  case case10 =>
    rename_i name fields info hlookup hnames fieldValues heval hcheckfalse ih2
    intro v h
    cases he : evalListFieldsHOLExact (emptyLocalsHOLExact state) fields with
    | none => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnames, he] at h; cases h
    | some fv' =>
        have hstate := evalListFieldsHOLExact_transfer_of_pointwise state fields fv' ih2 he
        simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnames, he] at h
        simp only [evalHOLExact, hlookup, hnames, hstate]
        exact h
  case case11 =>
    rename_i name fields info hlookup hnotnames
    intro v h
    simp only [evalHOLExact, emptyLocalsHOLExact_structs, hlookup, hnotnames] at h; cases h
  case case12 =>
    rename_i name value structName values hstruct hisSome ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) value with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ => rw [evalHOLExact, hw] at h; cases h
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct sn vals =>
            simp only [evalHOLExact, hw, emptyLocalsHOLExact_structs] at h
            simp only [evalHOLExact, hs]; exact h
  case case13 =>
    rename_i name value structName values hstruct hnotSome ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) value with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ => rw [evalHOLExact, hw] at h; cases h
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct sn vals =>
            simp only [evalHOLExact, hw, emptyLocalsHOLExact_structs] at h
            simp only [evalHOLExact, hs]; exact h
  case case14 =>
    rename_i name value hno ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) value with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        cases w with
        | val wv =>
            cases wv with
            | word _ => rw [evalHOLExact, hw] at h; cases h
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct sn vals => exact (hno sn vals (ih (.nStruct sn vals) hw)).elim
  case case15 =>
    rename_i shape address hwf word hword ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ =>
                simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw,
                  emptyLocalsHOLExact_memaddrs, emptyLocalsHOLExact_memory] at h
                simp only [evalHOLExact, hwf, hs]; exact h
        | rStruct vals => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
        | nStruct nm vals => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
  case case16 =>
    rename_i shape address hwf hno ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
    | some w =>
        cases w with
        | val wv =>
            cases wv with
            | word bits => exact (hno bits (ih (.val (.word bits)) hw)).elim
        | rStruct vals => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
        | nStruct nm vals => simp only [evalHOLExact, emptyLocalsHOLExact_structs, hwf, hw] at h; cases h
  case case17 =>
    rename_i shape address hnotwf
    intro v h
    simp only [evalHOLExact, emptyLocalsHOLExact_structs, hnotwf] at h; cases h
  case case18 =>
    rename_i address word hword ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ =>
                simp only [evalHOLExact, hw, emptyLocalsHOLExact_memaddrs,
                  emptyLocalsHOLExact_memory, emptyLocalsHOLExact_be] at h
                simp only [evalHOLExact, hs]; exact h
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case19 =>
    rename_i address hno ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        cases w with
        | val wv =>
            cases wv with
            | word bits => exact (hno bits (ih (.val (.word bits)) hw)).elim
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case20 =>
    rename_i address word hword ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        have hs := ih w hw
        cases w with
        | val wv =>
            cases wv with
            | word _ =>
                simp only [evalHOLExact, hw, emptyLocalsHOLExact_memaddrs,
                  emptyLocalsHOLExact_memory, emptyLocalsHOLExact_be] at h
                simp only [evalHOLExact, hs]; exact h
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case21 =>
    rename_i address hno ih
    intro v h
    cases hw : evalHOLExact (emptyLocalsHOLExact state) address with
    | none => rw [evalHOLExact, hw] at h; cases h
    | some w =>
        cases w with
        | val wv =>
            cases wv with
            | word bits => exact (hno bits (ih (.val (.word bits)) hw)).elim
        | rStruct vals => rw [evalHOLExact, hw] at h; cases h
        | nStruct nm vals => rw [evalHOLExact, hw] at h; cases h
  case case22 =>
    rename_i operator arguments values heval hall ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        have hv : values' = values := by rw [hstate] at heval; exact Option.some.inj heval
        subst hv
        simp only [evalHOLExact, he] at h
        simp only [evalHOLExact, heval]; exact h
  case case23 =>
    rename_i operator arguments values heval hnotall ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        have hv : values' = values := by rw [hstate] at heval; exact Option.some.inj heval
        subst hv
        simp only [evalHOLExact, he] at h
        simp only [evalHOLExact, heval]; exact h
  case case24 =>
    rename_i operator arguments hnone ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        rw [hstate] at hnone; cases hnone
  case case25 =>
    rename_i operator arguments values heval hall ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        have hv : values' = values := by rw [hstate] at heval; exact Option.some.inj heval
        subst hv
        simp only [evalHOLExact, he] at h
        simp only [evalHOLExact, heval]; exact h
  case case26 =>
    rename_i operator arguments values heval hnotall ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        have hv : values' = values := by rw [hstate] at heval; exact Option.some.inj heval
        subst hv
        simp only [evalHOLExact, he] at h
        simp only [evalHOLExact, heval]; exact h
  case case27 =>
    rename_i operator arguments hnone ih3
    intro v h
    cases he : evalListHOLExact (emptyLocalsHOLExact state) arguments with
    | none => rw [evalHOLExact, he] at h; cases h
    | some values' =>
        have hstate := evalListHOLExact_transfer_of_pointwise state arguments values' ih3 he
        rw [hstate] at hnone; cases hnone
  case case28 =>
    rename_i operator left right lw rw hright hleft ihL ihR
    intro v h
    cases hl : evalHOLExact (emptyLocalsHOLExact state) left with
    | none => simp only [evalHOLExact, hl] at h; cases h
    | some lv =>
        have hsl := ihL lv hl
        cases hr : evalHOLExact (emptyLocalsHOLExact state) right with
        | none => simp only [evalHOLExact, hl, hr] at h; cases h
        | some rv =>
            have hsr := ihR rv hr
            cases lv with
            | val lwv =>
                cases lwv with
                | word _ =>
                    cases rv with
                    | val rwv =>
                        cases rwv with
                        | word _ =>
                            simp only [evalHOLExact, hl, hr] at h
                            simp only [evalHOLExact, hsl, hsr]; exact h
                    | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
                    | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
  case case29 =>
    rename_i operator left right hno ihL ihR
    intro v h
    cases hl : evalHOLExact (emptyLocalsHOLExact state) left with
    | none => simp only [evalHOLExact, hl] at h; cases h
    | some lv =>
        have hsl := ihL lv hl
        cases hr : evalHOLExact (emptyLocalsHOLExact state) right with
        | none => simp only [evalHOLExact, hl, hr] at h; cases h
        | some rv =>
            have hsr := ihR rv hr
            cases lv with
            | val lwv =>
                cases lwv with
                | word _ =>
                    cases rv with
                    | val rwv =>
                        cases rwv with
                        | word _ =>
                            simp only [evalHOLExact, hl, hr] at h
                            simp only [evalHOLExact, hsl, hsr]; exact h
                    | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
                    | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
  case case30 =>
    rename_i operator left right lw rw hright hleft ihL ihR
    intro v h
    cases hl : evalHOLExact (emptyLocalsHOLExact state) left with
    | none => simp only [evalHOLExact, hl] at h; cases h
    | some lv =>
        have hsl := ihL lv hl
        cases hr : evalHOLExact (emptyLocalsHOLExact state) right with
        | none => simp only [evalHOLExact, hl, hr] at h; cases h
        | some rv =>
            have hsr := ihR rv hr
            cases lv with
            | val lwv =>
                cases lwv with
                | word _ =>
                    cases rv with
                    | val rwv =>
                        cases rwv with
                        | word _ =>
                            simp only [evalHOLExact, hl, hr] at h
                            simp only [evalHOLExact, hsl, hsr]; exact h
                    | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
                    | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
  case case31 =>
    rename_i operator left right hno ihL ihR
    intro v h
    cases hl : evalHOLExact (emptyLocalsHOLExact state) left with
    | none => simp only [evalHOLExact, hl] at h; cases h
    | some lv =>
        have hsl := ihL lv hl
        cases hr : evalHOLExact (emptyLocalsHOLExact state) right with
        | none => simp only [evalHOLExact, hl, hr] at h; cases h
        | some rv =>
            have hsr := ihR rv hr
            cases lv with
            | val lwv =>
                cases lwv with
                | word _ =>
                    cases rv with
                    | val rwv =>
                        cases rwv with
                        | word _ =>
                            simp only [evalHOLExact, hl, hr] at h
                            simp only [evalHOLExact, hsl, hsr]; exact h
                    | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
                    | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | rStruct vals => simp only [evalHOLExact, hl, hr] at h; cases h
            | nStruct nm vals => simp only [evalHOLExact, hl, hr] at h; cases h
  case case32 => intro v h; simpa [evalHOLExact, emptyLocalsHOLExact_baseAddr] using h
  case case33 => intro v h; simpa [evalHOLExact, emptyLocalsHOLExact_topAddr] using h
  case case34 => intro v h; simpa [evalHOLExact] using h
  case case35 =>
    rename_i x hx y hy
    exact absurd hx (by simp)
  case case36 =>
    rename_i expression rest value values hrest hexpr ih1 ih3 x hx y hy
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih1 y hy
    · exact ih3 x hx y hy
  case case37 =>
    rename_i expression rest hno ih1 ih3 x hx y hy
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih1 y hy
    · exact ih3 x hx y hy
  case case38 =>
    rename_i x hx y hy
    exact absurd hx (by simp)
  case case39 =>
    rename_i name expression rest value values hrest hexpr ih1 ih2 x hx y hy
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih1 y hy
    · exact ih2 x hx y hy
  case case40 =>
    rename_i name expression rest hno ih1 ih2 x hx y hy
    simp only [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ih1 y hy
    · exact ih2 x hx y hy

/-- Broad untagged analogue of HOL `update_locals_not_vars_eval_eq_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:1042`): updating `locals` at a
    name absent from `var_exp e` leaves evaluation unchanged. This reads the
    raw-function `PanSemStateExact` carrier, so it is not tagged; the tagged
    finite-map port is `updateLocalsNotVarsEvalEqEqHOLFinite` below. -/
theorem evalHOLExact_updLocals_not_mem {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (name : MlS) (word : ValueHOL width) :
    ∀ (expression : ExpHOL width),
      name ∉ varExpHOL expression →
        evalHOLExact { state with locals := FUPDATE_HOL state.locals (name, word) }
          expression = evalHOLExact state expression := by
  intro expression
  induction expression using evalHOLExact.induct (state := state)
      (motive_2 := fun fields =>
        (∀ pair ∈ fields, name ∉ varExpHOL pair.2) →
          evalListFieldsHOLExact
            { state with locals := FUPDATE_HOL state.locals (name, word) } fields =
          evalListFieldsHOLExact state fields)
      (motive_3 := fun expressions =>
        (∀ e ∈ expressions, name ∉ varExpHOL e) →
          evalListHOLExact
            { state with locals := FUPDATE_HOL state.locals (name, word) } expressions =
          evalListHOLExact state expressions)
  case case1 value => intro _; rfl
  case case2 name' =>
    intro h
    have hne : name' ≠ name := by
      intro heq; exact h (by simp [varExpHOL, heq])
    change FLOOKUP (FUPDATE_HOL state.locals (name, word)) name' =
      FLOOKUP state.locals name'
    rw [FLOOKUP_FUPDATE_HOL, if_neg hne]
  case case3 name' => intro _; rfl
  case case4 fields ih =>
    intro h
    have hpoint : ∀ e ∈ fields, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL fields name).mp (by simpa [varExpHOL] using h)
    have hlist := ih hpoint
    simp only [evalHOLExact, hlist]
  case case5 index expression values hChild ih =>
    intro h
    have hchild : name ∉ varExpHOL expression := by simpa [varExpHOL] using h
    have heq := ih hchild
    simp only [evalHOLExact, heq, hChild]
  case case6 index expression hNo ih =>
    intro h
    have hchild : name ∉ varExpHOL expression := by simpa [varExpHOL] using h
    have heq := ih hchild
    simp only [evalHOLExact, heq]
  case case7 structName fields hlookup =>
    intro _; simp only [evalHOLExact, hlookup]
  case case8 structName fields info hlookup hnames heval ih2 =>
    intro h
    have hpoint : ∀ pair ∈ fields, name ∉ varExpHOL pair.2 :=
      (not_mem_map_flatten (fun pair : MlS × ExpHOL width => varExpHOL pair.2)
        fields name).mp (by simpa [varExpHOL] using h)
    have hlist := ih2 hpoint
    simp only [evalHOLExact, hlookup, if_pos hnames, hlist]
  case case9 structName fields info hlookup hnames fieldValues heval hcheck ih2 =>
    intro h
    have hpoint : ∀ pair ∈ fields, name ∉ varExpHOL pair.2 :=
      (not_mem_map_flatten (fun pair : MlS × ExpHOL width => varExpHOL pair.2)
        fields name).mp (by simpa [varExpHOL] using h)
    have hlist := ih2 hpoint
    simp only [evalHOLExact, hlookup, if_pos hnames, hlist, heval, hcheck]
  case case10 structName fields info hlookup hnames fieldValues heval hcheckfalse ih2 =>
    intro h
    have hpoint : ∀ pair ∈ fields, name ∉ varExpHOL pair.2 :=
      (not_mem_map_flatten (fun pair : MlS × ExpHOL width => varExpHOL pair.2)
        fields name).mp (by simpa [varExpHOL] using h)
    have hlist := ih2 hpoint
    simp only [evalHOLExact, hlookup, if_pos hnames, hlist, heval, hcheckfalse]
  case case11 structName fields info hlookup hnotnames =>
    intro _; simp only [evalHOLExact, hlookup, if_neg hnotnames]
  case case12 fieldName value structName values hstruct hisSome ih =>
    intro h
    have hchild : name ∉ varExpHOL value := by simpa [varExpHOL] using h
    have heq := ih hchild
    simp only [evalHOLExact, heq, hstruct, hisSome]
  case case13 fieldName value structName values hstruct hnotSome ih =>
    intro h
    have hchild : name ∉ varExpHOL value := by simpa [varExpHOL] using h
    have heq := ih hchild
    simp only [evalHOLExact, heq]
  case case14 fieldName value hNo ih =>
    intro h
    have hchild : name ∉ varExpHOL value := by simpa [varExpHOL] using h
    have heq := ih hchild
    simp only [evalHOLExact, heq]
  case case15 shape address hShape word hWord ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq, hShape, hWord]
  case case16 shape address hShape hNo ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq]
  case case17 shape address hNo =>
    intro _; simp [evalHOLExact, hNo]
  case case18 address word hWord ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq, hWord]
  case case19 address hNo ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq]
  case case20 address word hWord ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq, hWord]
  case case21 address hNo ih =>
    intro h
    have haddr : name ∉ varExpHOL address := by simpa [varExpHOL] using h
    have heq := ih haddr
    simp only [evalHOLExact, heq]
  case case22 operator arguments values heval hall ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case23 operator arguments values heval hnotall ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case24 operator arguments hnone ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case25 operator arguments values heval hall ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case26 operator arguments values heval hnotall ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case27 operator arguments hnone ih3 =>
    intro h
    have hpoint : ∀ e ∈ arguments, name ∉ varExpHOL e :=
      (not_mem_map_flatten varExpHOL arguments name).mp (by simpa [varExpHOL] using h)
    have hlist := ih3 hpoint
    simp only [evalHOLExact, hlist]
  case case28 operator left right leftWord rightWord hLeft hRight ihL ihR =>
    intro h
    simp only [varExpHOL, List.mem_append, not_or] at h
    have heqL := ihL h.1
    have heqR := ihR h.2
    simp only [evalHOLExact, heqL, heqR, hLeft, hRight]
  case case29 operator left right hNo ihL ihR =>
    intro h
    simp only [varExpHOL, List.mem_append, not_or] at h
    have heqL := ihL h.1
    have heqR := ihR h.2
    simp only [evalHOLExact, heqL, heqR]
  case case30 operator left right leftWord rightWord hLeft hRight ihL ihR =>
    intro h
    simp only [varExpHOL, List.mem_append, not_or] at h
    have heqL := ihL h.1
    have heqR := ihR h.2
    simp only [evalHOLExact, heqL, heqR, hLeft, hRight]
  case case31 operator left right hNo ihL ihR =>
    intro h
    simp only [varExpHOL, List.mem_append, not_or] at h
    have heqL := ihL h.1
    have heqR := ihR h.2
    simp only [evalHOLExact, heqL, heqR]
  case case32 => intro _; rfl
  case case33 => intro _; rfl
  case case34 => intro _; rfl
  case case35 => rfl
  case case36 =>
    rename_i head tail tailResult headResult tailEval headEval ihHead ihTail premise
    have hhead : name ∉ varExpHOL head := premise head (by simp)
    have htail : ∀ e ∈ tail, name ∉ varExpHOL e := fun e he => premise e (by simp [he])
    have hh := ihHead hhead
    have ht := ihTail htail
    simp only [evalListHOLExact, hh, ht]
  case case37 =>
    rename_i head tail hNoEval ihHead ihTail premise
    have hhead : name ∉ varExpHOL head := premise head (by simp)
    have htail : ∀ e ∈ tail, name ∉ varExpHOL e := fun e he => premise e (by simp [he])
    have hh := ihHead hhead
    have ht := ihTail htail
    simp only [evalListHOLExact, hh, ht]
  case case38 => rfl
  case case39 =>
    rename_i pairName pairExpr tail headResult tailResult tailEval headEval ihHead ihTail premise
    have hhead : name ∉ varExpHOL pairExpr := premise (pairName, pairExpr) (by simp)
    have htail : ∀ p ∈ tail, name ∉ varExpHOL p.2 := fun p hp => premise p (by simp [hp])
    have hh := ihHead hhead
    have ht := ihTail htail
    simp only [evalListFieldsHOLExact, hh, ht]
  case case40 =>
    rename_i pairName pairExpr tail hNoEval ihHead ihTail premise
    have hhead : name ∉ varExpHOL pairExpr := premise (pairName, pairExpr) (by simp)
    have htail : ∀ p ∈ tail, name ∉ varExpHOL p.2 := fun p hp => premise p (by simp [hp])
    have hh := ihHead hhead
    have ht := ihTail htail
    simp only [evalListFieldsHOLExact, hh, ht]

/-- Broad untagged list analogue for HOL
    `OPT_MMAP_update_locals_not_vars_eval_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:1088`): a local update at a
    name absent from every expression's `var_exp` leaves the `OPT_MMAP eval`
    list step unchanged. Reads the raw-function `PanSemStateExact` carrier. -/
theorem evalListHOLExact_updLocals_not_mem {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (name : MlS) (word : ValueHOL width) :
    ∀ (expressions : List (ExpHOL width)),
      name ∉ (expressions.map varExpHOL).flatten →
        evalListHOLExact { state with locals := FUPDATE_HOL state.locals (name, word) }
          expressions = evalListHOLExact state expressions := by
  intro expressions
  induction expressions with
  | nil => intro _; rfl
  | cons head tail ih =>
      intro h
      have hpoint : ∀ e ∈ head :: tail, name ∉ varExpHOL e :=
        (not_mem_map_flatten varExpHOL (head :: tail) name).mp h
      have hhead := hpoint head (by simp)
      have htailPoint : ∀ e ∈ tail, name ∉ varExpHOL e := fun e he => hpoint e (by simp [he])
      have ihTail := ih ((not_mem_map_flatten varExpHOL tail name).mpr htailPoint)
      have hheadEq := evalHOLExact_updLocals_not_mem state name word head hhead
      simp only [evalListHOLExact, hheadEq, ihTail]

/-- Broad lookup for a standalone HOL finite-map parameter. -/
private def resVarMaptoBroadlookup {α β : Type}
    (fm : HolFiniteMapExact α β) : α → Option β := fm.lookup

/-- Reconstruct the canonical map carrier from its broad function plus support. -/
private def resVarMapofBroad {α β : Type} (fm : α → Option β)
    (support : ∃ keys : List α, ∀ key, fm key ≠ none → key ∈ keys) :
    HolFiniteMapExact α β := ⟨fm, support⟩

/-- Roundtrip witness for the first direct finite-map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_feveryResVarFlookupHOL_fm
    {α β : Type} (fm : HolFiniteMapExact α β) :
    resVarMapofBroad (resVarMaptoBroadlookup fm) fm.finiteSupport = fm := by
  cases fm
  rfl

/-- Roundtrip witness for the second independent direct finite-map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_feveryResVarFlookupHOL_fm2
    {α β : Type} (fm2 : HolFiniteMapExact α β) :
    resVarMapofBroad (resVarMaptoBroadlookup fm2) fm2.finiteSupport = fm2 := by
  cases fm2
  rfl

/-- `FEVERY P fm` on the finite-support carrier. This pointwise definition
    follows HOL's `FEVERY`/`FLOOKUP` view without adding a membership premise. -/
def feveryHOL {α β : Type} (P : α × β → Bool) (fm : HolFiniteMapExact α β) : Prop :=
  ∀ key value, fm.lookup key = some value → P (key, value) = true

/-- Exact finite-map port of HOL `FEVERY_res_var_FLOOKUP`
    (`panPropsScript.sml:1222`). The two independent HOL map binders remain
    separate and in source order; each is translated directly to
    `HolFiniteMapExact` with a checked lookup/support roundtrip. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "FEVERY_res_var_FLOOKUP"
  (fmap_as_finite_support_parameters := [fm, fm2])]
theorem feveryResVarFlookupHOL {α β : Type} [DecidableEq α]
    (P : α × β → Bool) (fm : HolFiniteMapExact α β)
    (fm2 : HolFiniteMapExact α β) (name : α) :
    (feveryHOL P fm ∧ feveryHOL P fm2) →
      feveryHOL P (fm.resVarEq (name, fm2.lookup name)) := by
  intro h
  rcases h with ⟨hfm, hfm2⟩
  intro key value hresult
  cases hlookup : fm2.lookup name with
  | none =>
      by_cases hkey : key = name
      · subst key
        simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq,
          FDOMSUB_HOL, hlookup] at hresult
      · have hsource : fm.lookup key = some value := by
          simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.eraseEq,
            FDOMSUB_HOL, hlookup, hkey] using hresult
        exact hfm key value hsource
  | some newValue =>
      by_cases hkey : key = name
      · subst key
        have hvalue : newValue = value := by
          simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq,
            FUPDATE_HOL, hlookup] using hresult
        subst value
        exact hfm2 name newValue hlookup
      · have hsource : fm.lookup key = some value := by
          simpa [HolFiniteMapExact.resVarEq, HolFiniteMapExact.updateEq,
            FUPDATE_HOL, hlookup, hkey] using hresult
        exact hfm key value hsource

/-- PanProps-local finite-map rendering of HOL's PanSem state. The four
    `HolFiniteMapExact` fields correspond to HOL `|->` fields; all other fields
    retain the exact PanSem carrier types.

    This is intentionally a distinct structure from `PanSemStateFiniteExact`:
    the `fmap_as_finite_support` checker requires the qualified fields' owning
    structure and its checked roundtrip witness to live in the same module as
    each tagged PanProps declaration. The canonical PanSem carrier is owned by
    another counterpart module, so reusing it here would make the PanProps
    qualifier unverifiable. `toPanSemFinite`/`ofPanSemFinite` are field-for-field
    codecs; this local carrier changes no state field or evaluator behavior. -/
structure PanPropsEvalStateFiniteExact (width : Nat) (σ : Type) [NeZero width] where
  locals : HolFiniteMapExact MlS (ValueHOL width)
  globals : HolFiniteMapExact MlS (ValueHOL width)
  structs : StructContextExact
  code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)
  eshapes : HolFiniteMapExact MlS ShapeHOL
  memory : RiscV.Word width → HolWordLab width
  memaddrs : RiscV.Word width → Prop
  shMemaddrs : RiscV.Word width → Prop
  clock : Nat
  be : Bool
  ffi : HolFfiState σ
  baseAddr : RiscV.Word width
  topAddr : RiscV.Word width

namespace PanPropsEvalStateFiniteExact

/-- Forget the finite-map witnesses and expose the exact broad state. -/
def toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) : PanSemStateExact width σ where
  locals := state.locals.lookup
  globals := state.globals.lookup
  structs := state.structs
  code := state.code.lookup
  eshapes := state.eshapes.lookup
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

/-- Build this finite-map carrier from a broad state with finite support. -/
def ofExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    PanPropsEvalStateFiniteExact width σ where
  locals := { lookup := state.locals, finiteSupport := h.1 }
  globals := { lookup := state.globals, finiteSupport := h.2.1 }
  structs := state.structs
  code := { lookup := state.code, finiteSupport := h.2.2.1 }
  eshapes := { lookup := state.eshapes, finiteSupport := h.2.2.2 }
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

instance decidableToExactMemaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    DecidablePred state.toExact.memaddrs := by
  simpa [PanPropsEvalStateFiniteExact.toExact] using h

theorem toExact_ofExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) (h : state.FiniteSupport) :
    (ofExact state h).toExact = state := rfl

theorem toExact_finiteSupport {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) : state.toExact.FiniteSupport :=
  ⟨state.locals.finiteSupport, state.globals.finiteSupport,
    state.code.finiteSupport, state.eshapes.finiteSupport⟩

theorem ofExact_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    ofExact state.toExact state.toExact_finiteSupport = state := by
  cases state
  rfl

/-- Checked canonical witness for this module's finite-map field qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (ofExact state h).toExact = state) ∧
    (∀ state : PanPropsEvalStateFiniteExact width σ,
        ofExact state.toExact state.toExact_finiteSupport = state) :=
  ⟨fun state h => toExact_ofExact state h, fun state => ofExact_toExact state⟩

/-- State codec to the canonical PanSem finite-support carrier that owns the
    tagged `evaluate_decls_def`. Both structures retain identical HOL fields;
    this conversion changes only the Lean structure name. -/
def toPanSemFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    PanSemStateFiniteExact width σ where
  locals := state.locals
  globals := state.globals
  structs := state.structs
  code := state.code
  eshapes := state.eshapes
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

instance toPanSemFiniteDecidableMemaddrs {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    DecidablePred state.toPanSemFinite.memaddrs := by
  simpa [toPanSemFinite] using h

/-- Memory replacement and the canonical evaluator's empty-locals update
    preserve the address-set predicate definitionally.  This explicit
    transport is needed because the evaluator's declaration clause requests a
    `DecidablePred` for the updated state's `emptyLocalsHOLFinite` projection,
    while the available instance is indexed by the original PanProps state. -/
@[instance_reducible]
def decidablePred_memoryUpdate_emptyLocals_toPanSemFinite
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs]
    (memory : RiscV.Word width → HolWordLab width) :
    DecidablePred
      (PanSemStateFiniteExact.emptyLocalsHOLFinite
        ({ state with memory := memory }.toPanSemFinite)).memaddrs := by
  change DecidablePred state.memaddrs
  exact h

/-- The corresponding transport on the canonical PanSem carrier.  This is
    Flapjack-specific typeclass infrastructure: the address predicate is an
    unchanged state field under both record updates. -/
@[instance_reducible]
def decidablePred_memoryUpdate_emptyLocals_PanSem
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    [h : DecidablePred state.memaddrs]
    (memory : RiscV.Word width → HolWordLab width) :
    DecidablePred
      (PanSemStateFiniteExact.emptyLocalsHOLFinite
        ({ state with memory := memory })).memaddrs := by
  change DecidablePred state.memaddrs
  exact h

/-- Inverse state codec from the canonical PanSem finite-support carrier. -/
def ofPanSemFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) : PanPropsEvalStateFiniteExact width σ where
  locals := state.locals
  globals := state.globals
  structs := state.structs
  code := state.code
  eshapes := state.eshapes
  memory := state.memory
  memaddrs := state.memaddrs
  shMemaddrs := state.shMemaddrs
  clock := state.clock
  be := state.be
  ffi := state.ffi
  baseAddr := state.baseAddr
  topAddr := state.topAddr

@[simp] theorem ofPanSemFinite_toPanSemFinite {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ) :
    ofPanSemFinite state.toPanSemFinite = state := by
  cases state
  rfl

@[simp] theorem toPanSemFinite_ofPanSemFinite {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ) :
    (ofPanSemFinite state).toPanSemFinite = state := by
  cases state
  rfl

/-- Local finite-map `dec_clock` operation for the projection equations below
    (declaration-local helper exception reviewed under bead `flapjack-i6f8`;
    see the `structsSimpsHOLFinite` note for why the canonical
    `PanSemStateFiniteExact.decClockHOLFinite` cannot replace it here). -/
def decClockForStructsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    PanPropsEvalStateFiniteExact width σ :=
  { state with clock := state.clock - 1 }

/-- Local finite-map `empty_locals` operation for the projection equations below
    (declaration-local helper exception reviewed under bead `flapjack-i6f8`;
    see the `structsSimpsHOLFinite` note for why the canonical
    `PanSemStateFiniteExact.emptyLocalsHOLFinite` cannot replace it here). -/
def emptyLocalsForStructsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    PanPropsEvalStateFiniteExact width σ :=
  { state with locals := HolFiniteMapExact.empty }

/-- Clearing `locals` changes no other state component, so the address-set
    decision procedure is inherited. -/
instance emptyLocalsForStructsSimpsDecidablePred {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs] :
    DecidablePred (emptyLocalsForStructsSimps state).memaddrs :=
  (inferInstance : DecidablePred state.memaddrs)

/-- Projection of the finite-map empty-locals operation to the canonical broad
    `emptyLocalsHOLExact`. -/
@[simp] theorem emptyLocalsForStructsSimps_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    (emptyLocalsForStructsSimps state).toExact = emptyLocalsHOLExact state.toExact :=
  rfl

/-- HOL `panProps$structs_simps` (`panPropsScript.sml:1217`): the six
    projections of `dec_clock` and `empty_locals`. This uses the existing
    PanProps finite-map state and its canonical same-module roundtrip witness.

    FLAPJACK-SPECIFIC surface note (bead `flapjack-i6f8`): the canonical tagged
    `dec_clock_def`/`empty_locals_def` ports (`PanSemStateFiniteExact.decClockHOLFinite`,
    `emptyLocalsHOLFinite`) live with the `PanSemStateFiniteExact` carrier in the
    PanSem counterpart, whereas `structs_simps` is a `panPropsScript.sml`
    declaration whose `fmap_as_finite_support` qualifier requires the owning
    carrier structure and the same-module roundtrip witness to sit beside the
    tagged theorem. The `decClockForStructsSimps`/`emptyLocalsForStructsSimps`
    record updates below are therefore the minimal PanProps-carrier mirrors; they
    are definitionally the same field updates as the canonical ports and are not
    meant to introduce a second HOL definition. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "structs_simps"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem structsSimpsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) :
    (decClockForStructsSimps state).structs = state.structs ∧
    (emptyLocalsForStructsSimps state).structs = state.structs ∧
    (decClockForStructsSimps state).globals = state.globals ∧
    (emptyLocalsForStructsSimps state).globals = state.globals ∧
    (decClockForStructsSimps state).locals = state.locals ∧
    (emptyLocalsForStructsSimps state).locals = HolFiniteMapExact.empty := by
  simp [decClockForStructsSimps, emptyLocalsForStructsSimps]

/-!
### Source-reviewed port: `evaluate_structs_invariant`

HOL `panPropsScript.sml:1210` states
`evaluate (p, s) = (res, s') ==> s'.structs = s.structs`. The exact finite
state theorem is now tagged below, after the clause-level structural
preservation proof. It uses the line-780 exact finite `evaluate_def` port and
does not rely on the unrestricted-map `evaluateHOLFiniteViaExact` adapter or
add an evaluator-success premise beyond HOL's result equality.

### Source-review disposition: `evaluate_min_clock`

HOL `panPropsScript.sml:822` states that if
`evaluate (prog, s) = (q, r)` and `q ≠ SOME TimeOut`, then there is an input
clock `k` for which evaluation returns the same result and all the same
post-state components except that the clock is zero.  Its proof depends on
`evaluate_clock_sub`; it does not assume an evaluator-success marker as a
premise.  There is deliberately no `@[hol]` theorem for this result yet:
`evaluateHOLFiniteViaExact` is the total pair-shaped adapter, but it delegates
through the unrestricted-map `PanSemStateExact` evaluator, while the direct
finite evaluator's projection is proved and the tagged panSem `evaluate_def`
assembly is `evaluateHOLFiniteState_eq_evaluate_def`
(`PanSem/EvaluateClock.lean`). The faithful finite-state theorem
is tracked by `flapjack-4ac.4.47.1`.
-/

/-- Flapjack-specific adapter from the PanProps finite-support state to the
    existing PanSem expression evaluator. HOL `eval_def` is tagged on its
    PanSem counterpart; this adapter has no separate HOL declaration. -/
def evalHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    ExpHOL width → Option (ValueHOL width) :=
  @evalHOLExact width σ _ state.toExact h

/-- The finite-map empty-locals evaluation is the broad exact evaluation over
    the canonical `emptyLocalsHOLExact` state; this is the state-translation
    bridge used by the tagged port below. -/
theorem evalHOL_emptyLocalsForStructsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width) :
    (emptyLocalsForStructsSimps state).evalHOL expression =
      @evalHOLExact width σ _ (emptyLocalsHOLExact state.toExact) h expression := rfl

/-- Exact finite-support port of HOL `panProps$eval_upd_clock_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:644-652`):
    `!t e ck. eval (t with clock := ck) e = eval t e`. The quantifier order
    (state, expression, clock) follows the source and the expression evaluator
    does not read `clock`. The state is the canonical `PanSemStateFiniteExact`
    carrier, whose four `|->` fields use the reviewed `HolFiniteMapExact`
    translation and canonical roundtrip witness in the PanSem counterpart.
    This module's local witness forwards that imported roundtrip. The statement
    uses PanSem's tagged `evalHOLFinite`, which delegates to `evalHOLExact`
    through `toExact`. `[NeZero width]`
    models HOL's positive word dimension and `DecidablePred state.memaddrs` is
    computation evidence for the HOL word-set guard. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_upd_clock_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalHOL_upd_clock_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width) (clock : Nat) :
    @PanSemStateFiniteExact.evalHOLFinite width σ _ { state with clock := clock } h expression =
      @PanSemStateFiniteExact.evalHOLFinite width σ _ state h expression :=
  @PanSemStateFiniteExact.evalHOLFinite_upd_clock_eq width σ _ state h clock expression

/-- Exact finite-support port of HOL `panProps$eval_upd_code_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:654-662`):
    `!t e code. eval (t with code := code) e = eval t e`. Same canonical carrier,
    evaluator, and finite-map witness review as `evalHOL_upd_clock_eq`; the
    expression evaluator does not read `code`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_upd_code_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalHOL_upd_code_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width)
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    @PanSemStateFiniteExact.evalHOLFinite width σ _ { state with code := code } h expression =
      @PanSemStateFiniteExact.evalHOLFinite width σ _ state h expression :=
  @PanSemStateFiniteExact.evalHOLFinite_upd_code_eq width σ _ state h code expression

/-- Exact finite-support port of HOL `panProps$eval_upd_eshapes_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:664-672`):
    `!t e esh. eval (t with eshapes := esh) e = eval t e`. Same canonical
    carrier, evaluator, and finite-map witness review as
    `evalHOL_upd_clock_eq`; the expression evaluator does not read `eshapes`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_upd_eshapes_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalHOL_upd_eshapes_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expression : ExpHOL width) (eshapes : HolFiniteMapExact MlS ShapeHOL) :
    @PanSemStateFiniteExact.evalHOLFinite width σ _ { state with eshapes := eshapes } h expression =
      @PanSemStateFiniteExact.evalHOLFinite width σ _ state h expression :=
  @PanSemStateFiniteExact.evalHOLFinite_upd_eshapes_eq width σ _ state h eshapes expression

/-- Exact port of HOL `panProps$opt_mmap_eval_upd_clock_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:674-680`):
    `!es s ck. OPT_MMAP (eval (s with clock := ck + s.clock)) es =
       OPT_MMAP (eval s) es`. HOL binds `es`, `s`, `ck` and advances the clock by
    `ck + s.clock`, matching the `{ state with clock := clock + state.clock }`
    update below; HOL's `OPT_MMAP` is Lean's `List.mapM`. The state is the
    canonical PanSem counterpart carrier `PanSemStateFiniteExact`, whose four
    `HolFiniteMapExact` fields (locals/globals/code/eshapes) and canonical
    `holFmapAsFiniteSupportWitness` establish the `fmap_as_finite_support`
    representation. This module's local witness forwards that roundtrip; the
    statement uses the tagged `evalHOLFinite` evaluator. The carrier is
    width-indexed (`[NeZero width]` with `RiscV.Word width` fields), so HOL's
    type-indexed `'a word` translation is recorded by the
    `(words_as_type_indexed_bitvec)` qualifier alongside the finite-support field
    qualifier. The statement follows from the tagged `evalHOL_upd_clock_eq` by
    induction on `es`. `[NeZero width]` models HOL's positive word dimension and
    `DecidablePred state.memaddrs` is computation evidence for the HOL word-set
    guard. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "opt_mmap_eval_upd_clock_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem optMmapEvalHOL_upd_clock_eq {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (expressions : List (ExpHOL width)) (clock : Nat) :
    expressions.mapM
        (fun e =>
          @PanSemStateFiniteExact.evalHOLFinite width σ _
            { state with clock := clock + state.clock } h e) =
      expressions.mapM (fun e =>
        @PanSemStateFiniteExact.evalHOLFinite width σ _ state h e) := by
  induction expressions with
  | nil => rfl
  | cons e es ih =>
      simp only [List.mapM_cons, evalHOL_upd_clock_eq state e (clock + state.clock), ih]

/-- Exact finite-support port of the `[local]` HOL helper
    `panProps$opt_mmap_helper_thm`
    (`cakeml/pancake/semantics/panPropsScript.sml:614`). HOL derives it from
    `OPT_MMAP_CONG` (`miscScript.sml:2481`) by fixing `l1 = l2 = es`,
    `f := \e. eval ((if T then f else I) st) e` and `f' := eval st`, then
    generalizing `f`, `st`, `es`; `REWRITE_RULE []` reduces the update to
    `f st`, leaving
    `!f st es. (!x. MEM x es ==> eval (f st) x = eval st x) ==>
       OPT_MMAP (eval (f st)) es = OPT_MMAP (eval st) es`.

    The Lean statement keeps HOL's quantifier order (`f`, `st`, `es`), the same
    pointwise-evaluation premise and the same `OPT_MMAP`/`List.mapM` equality.
    `eval` is the canonical `PanSemStateFiniteExact.evalHOLFinite`, whose four
    `|->` fields are the reviewed `HolFiniteMapExact` translation and whose
    canonical witness is forwarded by this module's local checker witness. The
    two `DecidablePred`
    binders are Lean computation evidence for HOL's word-set membership guard
    on each of the two states `f st` and `st`; HOL's total `eval` needs no such
    evidence. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "opt_mmap_helper_thm"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem optMmapHelperThm {width : Nat} {σ : Type} [NeZero width]
    (f : PanSemStateFiniteExact width σ → PanSemStateFiniteExact width σ)
    (st : PanSemStateFiniteExact width σ) [hst : DecidablePred st.memaddrs]
    [hfst : DecidablePred (f st).memaddrs] (es : List (ExpHOL width)) :
    (∀ x, x ∈ es → (f st).evalHOLFinite x = st.evalHOLFinite x) →
      es.mapM (f st).evalHOLFinite = es.mapM st.evalHOLFinite := by
  intro h
  induction es with
  | nil => rfl
  | cons x xs ih =>
      rw [List.mapM_cons, List.mapM_cons, h x (by simp),
        ih (fun y hy => h y (by simp [hy]))]

/-- Exact finite-support port of HOL `panProps$eval_empty_locals_IMP`
    (`cakeml/pancake/semantics/panPropsScript.sml:1584`):
    `!s e v. eval (s with locals := FEMPTY) e = SOME v ==> eval s e = SOME v`.
    The quantifier order (state, expression, value) and the
    empty-locals premise/same-value conclusion follow the source. The state is
    the canonical PanSem finite-map carrier, and `emptyLocalsHOLFinite` clears
    `locals` exactly like HOL `FEMPTY`; `evalHOLFinite` is the tagged finite
    projection of the exact broad evaluator. The four `|->` fields
    (`locals`, `globals`, `code`, `eshapes`) use the reviewed canonical
    `HolFiniteMapExact` translation recorded by the `fmap_as_finite_support`
    qualifier and its PanSem roundtrip witness (forwarded locally for checker
    validation); `[NeZero width]` models HOL's nonempty word index and
    `DecidablePred state.memaddrs` is computation evidence for the HOL word-set
    guard. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_empty_locals_IMP"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalEmptyLocalsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanSemStateFiniteExact width σ)
      [hdec : DecidablePred state.memaddrs]
      (expression : ExpHOL width) (value : ValueHOL width),
      @PanSemStateFiniteExact.evalHOLFinite width σ _
          (PanSemStateFiniteExact.emptyLocalsHOLFinite state) hdec expression = some value →
        @PanSemStateFiniteExact.evalHOLFinite width σ _ state hdec expression = some value := by
  intro state hdec expression value h
  change evalHOLExact (emptyLocalsHOLExact state.toExact) expression = some value at h
  have hResult := evalHOLExact_emptyLocalsHOLExact state.toExact expression value h
  change evalHOLExact state.toExact expression = some value
  exact hResult

/-- Flapjack-specific representation adapter for PanProps theorems that need
    the local same-module finite-map witness. Evaluation itself is performed
    by the canonical tagged PanSem finite-support evaluator; only successful
    result states are converted back to this module’s carrier. -/
def evaluateDeclsPanPropsCanonical {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (program : List (DeclHOL width)) :
    Option (PanPropsEvalStateFiniteExact width σ) :=
  (PanSemStateFiniteExact.evaluateDeclsHOLFinite state.toPanSemFinite program).map
    PanPropsEvalStateFiniteExact.ofPanSemFinite

private theorem panMemLoad32HOL_monoDomain {width : Nat} [NeZero width]
    (memory : RiscV.Word width → HolWordLab width)
    (domain1 domain2 : RiscV.Word width → Prop)
    [DecidablePred domain1] [DecidablePred domain2]
    (bigEndian : Bool) (address : RiscV.Word width)
    (hsubset : ∀ current, domain1 current → domain2 current)
    {value : RiscV.Word 32}
    (hload : panMemLoad32HOL memory domain1 bigEndian address = some value) :
    panMemLoad32HOL memory domain2 bigEndian address = some value := by
  unfold panMemLoad32HOL at hload ⊢
  by_cases haligned : address.toNat % 4 = 0
  · simp only [if_pos haligned] at hload ⊢
    cases hmemory : memory (panByteAlignHOL (width := width) address) with
    | word word =>
        simp only [hmemory] at hload ⊢
        by_cases hdomain : domain1 (panByteAlignHOL (width := width) address)
        · simp only [if_pos hdomain] at hload
          have hdomain2 := hsubset _ hdomain
          simp only [if_pos hdomain2]
          exact hload
        · simp [hdomain] at hload
  · simp [haligned] at hload

private theorem evalHOLExactMemaddrsMono {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateExact width σ) [DecidablePred state.memaddrs]
    (memaddrs : RiscV.Word width → Prop) [DecidablePred memaddrs]
    (hsubset : ∀ address, state.memaddrs address → memaddrs address) :
    ∀ expression value,
      evalHOLExact state expression = some value →
        evalHOLExact { state with memaddrs := memaddrs } expression = some value := by
  intro expression
  induction expression using evalHOLExact.induct (state := state)
      (motive_2 := fun fields => ∀ values,
        evalListFieldsHOLExact state fields = some values →
          evalListFieldsHOLExact { state with memaddrs := memaddrs } fields = some values)
      (motive_3 := fun expressions => ∀ values,
        evalListHOLExact state expressions = some values →
          evalListHOLExact { state with memaddrs := memaddrs } expressions = some values)
  case case4 fields ih =>
    intro value hEval
    cases hFields : evalListHOLExact state fields with
    | none => simp [evalHOLExact, hFields] at hEval
    | some values =>
        simp only [evalHOLExact, hFields] at hEval
        cases hEval
        simp [evalHOLExact, ih values hFields]
  case case15 shape address hShape word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hLoad : memLoadHOLExact shape word state.memaddrs state.memory state.structs =
        some value := by
      simpa [evalHOLExact, hShape, hAddress] using hEval
    have hLoad' := memLoadHOLExactSwapMemaddrs.1 shape word state.memaddrs
      state.memory state.structs value memaddrs ⟨hLoad, hsubset⟩
    simpa [evalHOLExact, hShape, hAddress'] using hLoad'
  case case18 address word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hRead : Option.map (fun loaded =>
        .val (.word (BitVec.ofNat width loaded.toNat)))
        (panMemLoad32HOL state.memory state.memaddrs state.be word) = some value := by
      simpa [evalHOLExact, hAddress] using hEval
    cases hSource : panMemLoad32HOL state.memory state.memaddrs state.be word with
    | none => simp [hSource] at hRead
    | some loaded =>
        have hValue : ValueHOL.val (.word (BitVec.ofNat width loaded.toNat)) = value := by
          simpa [hSource] using hRead
        have hLoad' := panMemLoad32HOL_monoDomain state.memory state.memaddrs
          memaddrs state.be word hsubset hSource
        simpa [evalHOLExact, hAddress', hLoad'] using hValue
  all_goals
    try intro result hEval
    simp_all [evalHOLExact, evalListHOLExact, evalListFieldsHOLExact,
      panMemLoadByteHOL]

/-- Exact port of HOL `eval_swap_memaddrs`
    (`cakeml/pancake/semantics/panPropsScript.sml:1703-1715`). It keeps HOL's
    conjunction premise and record-update conclusion. The state uses the local
    finite-support carrier and the qualifier records precisely its four HOL
    finite-map fields. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_swap_memaddrs"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalSwapMemaddrsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (value : ValueHOL width)
      (memaddrs : RiscV.Word width → Prop) [DecidablePred memaddrs],
      (state.evalHOL expression = some value ∧
        (∀ address, state.memaddrs address → memaddrs address)) →
          ({ state with memaddrs := memaddrs }.evalHOL expression = some value) := by
  intro state hmemaddrs expression value memaddrs hmemaddrs2 h
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hmemaddrs
  have hEval : evalHOLExact state.toExact expression = some value := by
    simpa [evalHOL] using h.1
  have hWidened := evalHOLExactMemaddrsMono state.toExact memaddrs h.2
    expression value hEval
  simpa [evalHOL, PanPropsEvalStateFiniteExact.toExact] using hWidened

private theorem panMemLoad32HOL_agreeMemory {width : Nat} [NeZero width]
    (memory1 memory2 : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width)
    (hagree : ∀ current, domain current → memory1 current = memory2 current) :
    panMemLoad32HOL memory1 domain bigEndian address =
      panMemLoad32HOL memory2 domain bigEndian address := by
  unfold panMemLoad32HOL
  by_cases haligned : address.toNat % 4 = 0
  · simp only [if_pos haligned]
    by_cases hdomain : domain (panByteAlignHOL (width := width) address)
    · have hmemory := hagree _ hdomain
      rw [hmemory]
    · simp [hdomain]
  · simp [haligned]

private theorem panMemLoadByteHOL_agreeMemory {width : Nat} [NeZero width]
    (memory1 memory2 : RiscV.Word width → HolWordLab width)
    (domain : RiscV.Word width → Prop) [DecidablePred domain]
    (bigEndian : Bool) (address : RiscV.Word width)
    (hagree : ∀ current, domain current → memory1 current = memory2 current) :
    panMemLoadByteHOL memory1 domain bigEndian address =
      panMemLoadByteHOL memory2 domain bigEndian address := by
  unfold panMemLoadByteHOL
  let aligned := panByteAlignHOL (width := width) address
  by_cases hdomain : domain aligned
  · have hmemory := hagree aligned hdomain
    simp [aligned, hdomain, hmemory]
  · simp [aligned, hdomain]

private theorem evalHOLExactSwapMemory {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateExact width σ)
    [DecidablePred state.memaddrs] (memory : RiscV.Word width → HolWordLab width)
    (hagree : ∀ address, state.memaddrs address → state.memory address = memory address) :
    ∀ expression value,
      evalHOLExact state expression = some value →
        evalHOLExact { state with memory := memory } expression = some value := by
  intro expression
  induction expression using evalHOLExact.induct (state := state)
      (motive_2 := fun fields => ∀ values,
        evalListFieldsHOLExact state fields = some values →
          evalListFieldsHOLExact { state with memory := memory } fields = some values)
      (motive_3 := fun expressions => ∀ values,
        evalListHOLExact state expressions = some values →
          evalListHOLExact { state with memory := memory } expressions = some values)
  case case4 fields ih =>
    intro value hEval
    cases hFields : evalListHOLExact state fields with
    | none => simp [evalHOLExact, hFields] at hEval
    | some values =>
        simp only [evalHOLExact, hFields] at hEval
        cases hEval
        simp [evalHOLExact, ih values hFields]
  case case15 shape address hShape word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hLoad : memLoadHOLExact shape word state.memaddrs state.memory state.structs =
        some value := by
      simpa [evalHOLExact, hShape, hAddress] using hEval
    have hLoad' := memLoadHOLExactSwapMemory.1 shape word state.memaddrs
      state.memory state.structs value memory ⟨hLoad, hagree⟩
    simpa [evalHOLExact, hShape, hAddress'] using hLoad'
  case case18 address word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hRead : (panMemLoad32HOL state.memory state.memaddrs state.be word).map
        (fun loaded => .val (.word (BitVec.ofNat width loaded.toNat))) = some value := by
      simpa [evalHOLExact, hAddress] using hEval
    have hRead' := panMemLoad32HOL_agreeMemory state.memory memory state.memaddrs
      state.be word hagree
    rw [hRead'] at hRead
    simpa [evalHOLExact, hAddress'] using hRead
  case case20 address word hAddress ih =>
    intro value hEval
    have hAddress' := ih (.val (.word word)) hAddress
    have hRead : (panMemLoadByteHOL state.memory state.memaddrs state.be word).map
        (fun loaded => .val (.word (BitVec.ofNat width loaded.toNat))) = some value := by
      simpa [evalHOLExact, hAddress] using hEval
    have hRead' := panMemLoadByteHOL_agreeMemory state.memory memory state.memaddrs
      state.be word hagree
    rw [hRead'] at hRead
    simpa [evalHOLExact, hAddress'] using hRead
  all_goals
    try intro result hEval
    simp_all [evalHOLExact, evalListHOLExact, evalListFieldsHOLExact]

/-- Exact finite-support port of HOL `eval_swap_memory`
    (`panPropsScript.sml:1734-1742`). It preserves HOL's successful evaluation
    and pointwise memory-agreement premise, replacing only the state's memory.
    The local carrier owns the four finite-map fields named by the qualifier. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_swap_memory"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalSwapMemoryHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (expression : ExpHOL width)
      (value : ValueHOL width) (memory : RiscV.Word width → HolWordLab width),
      (state.evalHOL expression = some value ∧
        (∀ address, state.memaddrs address → state.memory address = memory address)) →
        ({ state with memory := memory }.evalHOL expression = some value) := by
  intro state hmemaddrs expression value memory h
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hmemaddrs
  have hEval : evalHOLExact state.toExact expression = some value := by
    simpa [evalHOL] using h.1
  have hSame := evalHOLExactSwapMemory state.toExact memory h.2 expression value hEval
  simpa [evalHOL, PanPropsEvalStateFiniteExact.toExact] using hSame

private theorem evaluateDeclsHOLFiniteMemaddrsMono {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (memaddrs : RiscV.Word width → Prop)
    [DecidablePred memaddrs] (program : List (DeclHOL width))
    (result : PanSemStateFiniteExact width σ)
    (hEval : PanSemStateFiniteExact.evaluateDeclsHOLFinite state program = some result)
    (hsubset : ∀ address, state.memaddrs address → memaddrs address) :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite
        { state with memaddrs := memaddrs } program =
      some { result with memaddrs := memaddrs } := by
  induction program generalizing state result with
  | nil =>
      simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
      cases hEval
      rfl
  | cons declaration rest ih =>
      cases declaration with
      | name name fields =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval ⊢
          exact ih state result hEval hsubset
      | decl shape name expression =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          letI : DecidablePred
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state).memaddrs := by
            simpa [PanSemStateFiniteExact.emptyLocalsHOLFinite] using
              (inferInstance : DecidablePred state.memaddrs)
          cases heval : PanSemStateFiniteExact.evalHOLFinite
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state) expression with
          | none => simp [heval] at hEval
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                let emptyState := PanSemStateFiniteExact.emptyLocalsHOLFinite state
                have hsubsetEmpty : ∀ address, emptyState.memaddrs address → memaddrs address := by
                  simpa [emptyState, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hsubset
                have hevalExact : evalHOLExact emptyState.toExact expression = some value := by
                  simpa [PanSemStateFiniteExact.evalHOLFinite, emptyState,
                    PanSemStateFiniteExact.emptyLocalsHOLFinite,
                    PanSemStateFiniteExact.toExact, emptyLocalsHOLExact] using heval
                have hevalWidened := evalHOLExactMemaddrsMono emptyState.toExact memaddrs
                  hsubsetEmpty expression value hevalExact
                let widenedInitial := { state with memaddrs := memaddrs }
                letI : DecidablePred widenedInitial.memaddrs := by
                  simpa [widenedInitial] using (inferInstance : DecidablePred memaddrs)
                letI : DecidablePred
                    (PanSemStateFiniteExact.emptyLocalsHOLFinite widenedInitial).memaddrs := by
                  simpa [PanSemStateFiniteExact.emptyLocalsHOLFinite] using
                    (inferInstance : DecidablePred widenedInitial.memaddrs)
                have hevalWidenedCanonical :
                    PanSemStateFiniteExact.evalHOLFinite
                      (PanSemStateFiniteExact.emptyLocalsHOLFinite widenedInitial)
                      expression = some value := by
                  have hstates : (PanSemStateFiniteExact.emptyLocalsHOLFinite
                      widenedInitial).toExact =
                      { emptyState.toExact with memaddrs := memaddrs } := by
                    cases state <;> rfl
                  simpa only [PanSemStateFiniteExact.evalHOLFinite_eq_toExact, hstates]
                    using hevalWidened
                let nextState := PanSemStateFiniteExact.setGlobalHOLFinite name value state
                letI : DecidablePred nextState.memaddrs := by
                  simpa [nextState, PanSemStateFiniteExact.setGlobalHOLFinite] using
                    (inferInstance : DecidablePred state.memaddrs)
                have htail := ih nextState result hEval hsubset
                let widenedNext := PanSemStateFiniteExact.setGlobalHOLFinite name value
                  widenedInitial
                letI : DecidablePred widenedNext.memaddrs := by
                  simpa [widenedNext, PanSemStateFiniteExact.setGlobalHOLFinite] using
                    (inferInstance : DecidablePred memaddrs)
                simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
                rw [hevalWidenedCanonical]
                simp only [if_pos hshape]
                simpa [nextState, widenedNext, PanSemStateFiniteExact.setGlobalHOLFinite] using htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          let condition := declaration.params.all
            (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite, condition, hcondition] at hEval ⊢
            exact ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hEval hsubset
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite, condition, hcondition] at hEval
      | exnDecl exceptionName shape =>
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite, condition, hcondition] at hEval ⊢
            exact ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hEval hsubset
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite, condition, hcondition] at hEval

 /-- Exact finite-support port of HOL `evaluate_decls_memaddrs_mono`
    (`panPropsScript.sml:1766-1778`). The quantified state, declaration list,
    successful result, replacement domain, conjunctive success/subset premise,
    and updated-result conclusion follow HOL's order and shape. The local
    evaluator follows `evaluate_decls_def` (`panSemScript.sml:814-837`) clause
    for clause. `PanPropsEvalStateFiniteExact` supplies the reviewed canonical
    finite-map representation for the four `|->` fields; the qualifier records
    only that representation. Its proof uses the canonical tagged PanSem
    `evaluate_decls_def` through the field-for-field `toPanSemFinite` codec;
    it does not unfold the PanProps-local recursive evaluator. `[NeZero width]`
    models HOL's positive word dimension, and `DecidablePred` supplies Lean
    decisions for HOL word-set membership. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_memaddrs_mono"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsMemaddrsMonoHOLFinite {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (program : List (DeclHOL width))
      (result : PanPropsEvalStateFiniteExact width σ)
      (memaddrs : RiscV.Word width → Prop) [DecidablePred memaddrs],
      (evaluateDeclsPanPropsCanonical state program = some result ∧
        (∀ address, state.memaddrs address → memaddrs address)) →
        evaluateDeclsPanPropsCanonical { state with memaddrs := memaddrs } program =
          some { result with memaddrs := memaddrs } := by
  intro state hstate program result memaddrs hmemaddrs h
  letI : DecidablePred state.toPanSemFinite.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hstate
  have hcanonical :
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state.toPanSemFinite program =
        some result.toPanSemFinite := by
    have hinj : Function.Injective
        (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ)) := by
      intro left right hEq
      have hEq' := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hEq
      simpa using hEq'
    have hmap : Option.map
        (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ))
        (PanSemStateFiniteExact.evaluateDeclsHOLFinite state.toPanSemFinite program) =
        some result := by
      simpa [evaluateDeclsPanPropsCanonical] using h.1
    have hmap' : Option.map
        (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ))
        (PanSemStateFiniteExact.evaluateDeclsHOLFinite state.toPanSemFinite program) =
        Option.map (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ))
          (some result.toPanSemFinite) := by
      rw [hmap]
      simp
    have hcanonical' := Option.map_injective hinj hmap'
    simpa using hcanonical'
  have hcanonicalWidened := evaluateDeclsHOLFiniteMemaddrsMono state.toPanSemFinite
    memaddrs program result.toPanSemFinite hcanonical h.2
  have hcanonicalOut :
      PanSemStateFiniteExact.evaluateDeclsHOLFinite
          { state.toPanSemFinite with memaddrs := memaddrs } program =
        some ({ result.toPanSemFinite with memaddrs := memaddrs }) := by
    exact hcanonicalWidened
  have hmap := congrArg
    (Option.map (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ)))
    hcanonicalOut
  change Option.map
      (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ))
      (PanSemStateFiniteExact.evaluateDeclsHOLFinite
        (PanPropsEvalStateFiniteExact.toPanSemFinite
          { state with memaddrs := memaddrs }) program) =
    some { result with memaddrs := memaddrs }
  simpa only [PanPropsEvalStateFiniteExact.toPanSemFinite, Option.map_some,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite,
    PanPropsEvalStateFiniteExact.ofPanSemFinite] using hmap

/-- Exact finite-support port of HOL `evaluate_decls_swap_memaddrs`
    (`panPropsScript.sml:1718`). It preserves the source quantifier order and
    premise: successful declaration evaluation together with inclusion of the
    original address domain in the replacement domain. The conclusion changes
    only `memaddrs` in the initial and successful result states. The four
    finite-map fields are the reviewed canonical representation recorded by
    the qualifier. Although this proof carrier has a separate Lean structure
    name, `evaluateDeclsPanPropsCanonical` evaluates with the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` and converts successful
    results through the checked field-for-field state codec.
    `[DecidablePred memaddrs]` supplies Lean computation evidence for the
    replacement HOL set. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_swap_memaddrs"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsSwapMemaddrsHOLFinite {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (program : List (DeclHOL width))
      (result : PanPropsEvalStateFiniteExact width σ)
      (memaddrs : RiscV.Word width → Prop) [DecidablePred memaddrs],
      (evaluateDeclsPanPropsCanonical state program = some result ∧
        (∀ address, state.memaddrs address → memaddrs address)) →
        evaluateDeclsPanPropsCanonical { state with memaddrs := memaddrs } program =
          some { result with memaddrs := memaddrs } := by
  exact evaluateDeclsMemaddrsMonoHOLFinite

private theorem evaluateDeclsPanSemMemorySwap {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (memory : RiscV.Word width → HolWordLab width)
    (program : List (DeclHOL width))
    (result : PanSemStateFiniteExact width σ)
    (hEval : PanSemStateFiniteExact.evaluateDeclsHOLFinite state program = some result)
    (hagree : ∀ address, state.memaddrs address → state.memory address = memory address) :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite { state with memory := memory } program =
      some { result with memory := memory } := by
  induction program generalizing state result with
  | nil =>
      simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
      cases hEval
      rfl
  | cons declaration rest ih =>
      cases declaration with
      | name name fields =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval ⊢
          exact ih state result hEval hagree
      | decl shape name expression =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval ⊢
          letI : DecidablePred
              (PanSemStateFiniteExact.emptyLocalsHOLFinite
                { state with memory := memory }).memaddrs :=
            PanPropsEvalStateFiniteExact.decidablePred_memoryUpdate_emptyLocals_PanSem
              state memory
          letI : DecidablePred
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state).memaddrs := by
            simpa [PanSemStateFiniteExact.emptyLocalsHOLFinite] using
              (inferInstance : DecidablePred state.memaddrs)
          cases heval : PanSemStateFiniteExact.evalHOLFinite
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state) expression with
          | none => simp [heval] at hEval
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                have hExactEval :
                    evalHOLExact
                      (PanSemStateFiniteExact.emptyLocalsHOLFinite state).toExact
                      expression = some value := by
                  simpa [PanSemStateFiniteExact.evalHOLFinite] using heval
                have hExactMemory := evalHOLExactSwapMemory
                  (PanSemStateFiniteExact.emptyLocalsHOLFinite state).toExact memory
                  (fun address haddress => hagree address
                    (by simpa [PanSemStateFiniteExact.emptyLocalsHOLFinite] using haddress))
                  expression value hExactEval
                have hevalMemory :
                    PanSemStateFiniteExact.evalHOLFinite
                      (PanSemStateFiniteExact.emptyLocalsHOLFinite
                        { state with memory := memory }) expression = some value := by
                  simpa [PanSemStateFiniteExact.evalHOLFinite,
                    PanSemStateFiniteExact.emptyLocalsHOLFinite,
                    PanSemStateFiniteExact.toExact] using hExactMemory
                let nextState := PanSemStateFiniteExact.setGlobalHOLFinite name value state
                letI : DecidablePred nextState.memaddrs := by
                  change DecidablePred state.memaddrs
                  exact inferInstance
                have htail := ih nextState result hEval hagree
                simpa [PanSemStateFiniteExact.evaluateDeclsHOLFinite, hshape,
                  hevalMemory, nextState, PanSemStateFiniteExact.setGlobalHOLFinite] using htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          let condition := declaration.params.all
            (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite,
              condition, hcondition] at hEval ⊢
            let nextState := { state with code := state.code.update (declaration.name,
              (declaration.params, declaration.body, declaration.returnShape)) }
            letI : DecidablePred nextState.memaddrs := by
              change DecidablePred state.memaddrs
              exact inferInstance
            exact ih nextState result hEval hagree
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite,
              condition, hcondition] at hEval ⊢
      | exnDecl exceptionName shape =>
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite,
              condition, hcondition] at hEval ⊢
            let nextState := { state with eshapes := state.eshapes.update (exceptionName, shape) }
            letI : DecidablePred nextState.memaddrs := by
              change DecidablePred state.memaddrs
              exact inferInstance
            exact ih nextState result hEval hagree
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite,
              condition, hcondition] at hEval ⊢

private theorem evaluateDeclsHOLFiniteSwapLocals {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs]
    (locals : HolFiniteMapExact MlS (ValueHOL width))
    (program : List (DeclHOL width)) (result : PanSemStateFiniteExact width σ)
    (hEval : PanSemStateFiniteExact.evaluateDeclsHOLFinite state program = some result) :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite { state with locals := locals } program =
      some { result with locals := locals } := by
  induction program generalizing state result with
  | nil =>
      simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
      cases hEval
      rfl
  | cons declaration rest ih =>
      cases declaration with
      | name name fields =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval ⊢
          exact ih state result hEval
      | decl shape name expression =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval ⊢
          let stateWithLocals := { state with locals := locals }
          letI : DecidablePred
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state).memaddrs := by
            simpa [PanSemStateFiniteExact.emptyLocalsHOLFinite] using
              (inferInstance : DecidablePred state.memaddrs)
          letI : DecidablePred
              (PanSemStateFiniteExact.emptyLocalsHOLFinite stateWithLocals).memaddrs := by
            simpa [stateWithLocals, PanSemStateFiniteExact.emptyLocalsHOLFinite] using
              (inferInstance : DecidablePred state.memaddrs)
          cases heval : PanSemStateFiniteExact.evalHOLFinite
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state) expression with
          | none => simp [heval] at hEval
          | some value =>
              have hevalChanged : PanSemStateFiniteExact.evalHOLFinite
                  (PanSemStateFiniteExact.emptyLocalsHOLFinite stateWithLocals)
                  expression = some value := by
                simpa [stateWithLocals,
                  PanSemStateFiniteExact.emptyLocalsHOLFinite] using heval
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                let nextState := PanSemStateFiniteExact.setGlobalHOLFinite name value state
                letI : DecidablePred nextState.memaddrs := by
                  simpa [nextState, PanSemStateFiniteExact.setGlobalHOLFinite] using
                    (inferInstance : DecidablePred state.memaddrs)
                have htail := ih nextState result hEval
                rw [hevalChanged]
                simp only [if_pos hshape]
                simpa [nextState, stateWithLocals,
                  PanSemStateFiniteExact.setGlobalHOLFinite] using htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite, condition,
              hcondition] at hEval ⊢
            exact ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hEval
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite, condition,
              hcondition] at hEval
      | exnDecl exceptionName shape =>
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite, condition,
              hcondition] at hEval ⊢
            exact ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hEval
          · simp [PanSemStateFiniteExact.evaluateDeclsHOLFinite, condition,
              hcondition] at hEval

/-- HOL `evaluate_decls_swap_locals`
    (`panPropsScript.sml:1645`) over the reviewed finite-support state.
    The finite-map qualifier records the four HOL `|->` fields. The theorem's
    premise and conclusion match HOL: a successful declaration evaluation
    remains successful after replacing `locals`, and the resulting state has
    exactly that replacement. The PanProps proof carrier has a separate Lean
    structure name; `evaluateDeclsPanPropsCanonical` directly uses the
    canonical tagged `PanSemStateFiniteExact.evaluateDeclsHOLFinite` and maps
    its successful result through the checked field-for-field codec. The
    declaration initializer clause clears locals before evaluating, while the
    other clauses preserve the field. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_swap_locals"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsSwapLocalsHOLFinite {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (program : List (DeclHOL width))
      (result : PanPropsEvalStateFiniteExact width σ)
      (locals : HolFiniteMapExact MlS (ValueHOL width)),
      evaluateDeclsPanPropsCanonical state program = some result →
        evaluateDeclsPanPropsCanonical { state with locals := locals } program =
          some { result with locals := locals } := by
  intro state hstate program result locals hEval
  letI : DecidablePred state.toPanSemFinite.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hstate
  have hcanonical :
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state.toPanSemFinite program =
        some result.toPanSemFinite := by
    have hinj : Function.Injective
        (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ)) := by
      intro left right hEq
      have hEq' := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hEq
      simpa using hEq'
    have hmap : Option.map
        (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ))
        (PanSemStateFiniteExact.evaluateDeclsHOLFinite state.toPanSemFinite program) =
        some result := by
      simpa [evaluateDeclsPanPropsCanonical] using hEval
    have hmap' : Option.map
        (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ))
        (PanSemStateFiniteExact.evaluateDeclsHOLFinite state.toPanSemFinite program) =
        Option.map (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ))
          (some result.toPanSemFinite) := by
      rw [hmap]
      simp
    have hcanonical' := Option.map_injective hinj hmap'
    simpa using hcanonical'
  have hcanonicalChanged := evaluateDeclsHOLFiniteSwapLocals state.toPanSemFinite
    locals program result.toPanSemFinite hcanonical
  have hmap := congrArg
    (Option.map (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ)))
    hcanonicalChanged
  change Option.map
      (PanPropsEvalStateFiniteExact.ofPanSemFinite (width := width) (σ := σ))
      (PanSemStateFiniteExact.evaluateDeclsHOLFinite
        (PanPropsEvalStateFiniteExact.toPanSemFinite
          { state with locals := locals }) program) =
    some { result with locals := locals }
  simpa only [PanPropsEvalStateFiniteExact.toPanSemFinite, Option.map_some,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite,
    PanPropsEvalStateFiniteExact.ofPanSemFinite] using hmap

/-- Exact finite-support port of HOL `evaluate_decls_swap_memory`
    (`panPropsScript.sml:1750-1763`). It preserves HOL's quantified state,
    declaration list, result state, replacement memory, conjunctive premise,
    and conclusion. The declaration evaluator has a checked `toExact` bridge
    to PanSem's established evaluator; the finite-map qualifier records only
    its four HOL `|->` fields. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_swap_memory"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsSwapMemoryHOLFinite {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (program : List (DeclHOL width))
      (result : PanPropsEvalStateFiniteExact width σ)
      (memory : RiscV.Word width → HolWordLab width),
      (evaluateDeclsPanPropsCanonical state program = some result ∧
        (∀ address, state.memaddrs address → state.memory address = memory address)) →
        evaluateDeclsPanPropsCanonical { state with memory := memory } program =
          some { result with memory := memory } := by
  intro state hstate program result memory h
  have hcanonical :
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state.toPanSemFinite program =
        some result.toPanSemFinite := by
    have hmap := h.1
    change Option.map PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.evaluateDeclsHOLFinite state.toPanSemFinite program) =
      some result at hmap
    cases heval : PanSemStateFiniteExact.evaluateDeclsHOLFinite
        state.toPanSemFinite program with
    | none => simp [heval] at hmap
    | some canonicalResult =>
        simp only [heval, Option.map_some, Option.some.injEq] at hmap
        have hEq := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hmap
        simpa using hEq
  letI : DecidablePred state.toPanSemFinite.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hstate
  have hcanonicalChanged := evaluateDeclsPanSemMemorySwap
    state.toPanSemFinite memory program result.toPanSemFinite hcanonical h.2
  have hmap := congrArg
    (Option.map (PanPropsEvalStateFiniteExact.ofPanSemFinite
      (width := width) (σ := σ))) hcanonicalChanged
  simpa [evaluateDeclsPanPropsCanonical,
    PanPropsEvalStateFiniteExact.toPanSemFinite,
    PanPropsEvalStateFiniteExact.ofPanSemFinite] using hmap

/-- `OPT_MMAP eval` over the same finite-support carrier. -/
def evalListHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (ExpHOL width) → Option (List (ValueHOL width)) :=
  @evalListHOLExact width σ _ state.toExact (by
    simpa [PanPropsEvalStateFiniteExact.toExact] using h)

/-- PanProps proof support that assembles the finite-map `lookup_code` result
    needed by `lookup_code_wf_shape_invariant_step`. The underlying HOL
    `lookup_code_def` is in `panSemScript.sml:458-467`; this helper is untagged
    because it is an invariant-proof wrapper in the PanProps counterpart. -/
def lookupCodeHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (fname : MlS)
    (arguments : List (ValueHOL width)) :
    Option (ProgHOL width × HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL) :=
  match state.code.lookup fname with
  | none => none
  | some (parameters, body, returnShape) =>
      if (parameters.map Prod.fst).Nodup ∧ parameters.length = arguments.length ∧
          ((parameters.zip arguments).all
            (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true then
        some (body,
          HolFiniteMapExact.empty.updateList ((parameters.map Prod.fst).zip arguments),
          returnShape)
      else none

/-- Exact port of HOL `panProps$eval_is_wf_shape_v`
    (`cakeml/pancake/semantics/panPropsScript.sml:126`). The conjunction
    preserves HOL's successful-evaluation, `FEVERY locals`, `FEVERY globals`
    hypothesis order. Finite-map fields use the reviewed canonical
    `HolFiniteMapExact` translation. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_is_wf_shape_v"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalIsWfShapeValueHOL {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (value : ValueHOL width),
      state.evalHOL expression = some value ∧
        (∀ name bound, state.locals.lookup name = some bound →
          isWfShapeValueHOLExact state.structs bound = true) ∧
        (∀ name bound, state.globals.lookup name = some bound →
          isWfShapeValueHOLExact state.structs bound = true) →
        isWfShapeValueHOLExact state.structs value = true := by
  intro state hdec expression value h
  have hEval := h.1
  have hlocals := h.2.1
  have hglobals := h.2.2
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hdec
  apply evalHOLExact_isWfShapeValueHOLExact state.toExact hlocals hglobals expression value
  simpa [evalHOL] using hEval

private theorem snd_mem_of_mem_zip {α β : Type} {left : List α} {right : List β}
    {pair : α × β} (h : pair ∈ left.zip right) : pair.2 ∈ right := by
  induction left generalizing right pair with
  | nil => simp at h
  | cons head tail ih =>
      cases right with
      | nil => simp at h
      | cons head' tail' =>
          simp only [List.zip_cons_cons, List.mem_cons] at h
          rcases h with heq | htail
          · cases heq
            simp
          · exact List.mem_cons_of_mem head' (ih htail)

private theorem evalListHOLExact_mem_isWf {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    [DecidablePred state.memaddrs]
    (hlocals : ∀ name value, state.locals.lookup name = some value →
      isWfShapeValueHOLExact state.structs value = true)
    (hglobals : ∀ name value, state.globals.lookup name = some value →
      isWfShapeValueHOLExact state.structs value = true) :
    ∀ expressions values,
      state.evalListHOL expressions = some values →
        ∀ value, value ∈ values → isWfShapeValueHOLExact state.structs value = true := by
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using
      (inferInstance : DecidablePred state.memaddrs)
  intro expressions
  induction expressions with
  | nil =>
      intro values hEval value hmem
      change evalListHOLExact state.toExact [] = some values at hEval
      simp [evalListHOLExact] at hEval
      cases hEval
      simp at hmem
  | cons expression rest ih =>
      intro values hEval value hmem
      change evalListHOLExact state.toExact (expression :: rest) = some values at hEval
      cases hExpression : evalHOLExact state.toExact expression with
      | none => simp [evalListHOLExact, hExpression] at hEval
      | some head =>
          cases hRest : evalListHOLExact state.toExact rest with
          | none => simp [evalListHOLExact, hExpression, hRest] at hEval
          | some tail =>
              have hSomeValues : some (head :: tail) = some values := by
                simpa only [evalListHOLExact, hExpression, hRest] using hEval
              have hValues : head :: tail = values := Option.some.inj hSomeValues
              subst values
              simp only [List.mem_cons] at hmem
              rcases hmem with hHead | hmem
              · subst value
                have hExpressionFinite : state.evalHOL expression = some head := by
                  simpa [evalHOL] using hExpression
                exact evalIsWfShapeValueHOL state expression head
                  ⟨hExpressionFinite, hlocals, hglobals⟩
              · exact ih tail (by simpa [evalListHOL] using hRest) value hmem

/-- HOL `lookup_code_wf_shape_invariant_step` proof dependency: evaluated
    arguments are well-formed, so every value installed into the callee's
    finite locals map is well-formed. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "lookup_code_wf_shape_invariant_step"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem lookupCodeWfShapeInvariantStep {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      [DecidablePred state.memaddrs]
      (argexps : List (ExpHOL width)) (args : List (ValueHOL width))
      (fname : MlS) (prog : ProgHOL width)
      (newlocals : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL),
      state.evalListHOL argexps = some args ∧
        lookupCodeHOLFinite state fname args = some (prog, newlocals, returnShape) ∧
        (∀ name value, state.locals.lookup name = some value →
          isWfShapeValueHOLExact state.structs value = true) ∧
        (∀ name value, state.globals.lookup name = some value →
          isWfShapeValueHOLExact state.structs value = true) →
        (∀ name value, newlocals.lookup name = some value →
          isWfShapeValueHOLExact state.structs value = true) := by
  intro state hdec argexps args fname prog newlocals returnShape h
  have hArgs := h.1
  have hLookup := h.2.1
  have hlocals := h.2.2.1
  have hglobals := h.2.2.2
  letI : DecidablePred state.toExact.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toExact] using hdec
  cases hCode : state.code.lookup fname with
  | none => simp [lookupCodeHOLFinite, hCode] at hLookup
  | some codeEntry =>
      rcases codeEntry with ⟨parameters, body, declaredReturn⟩
      by_cases hValid : (parameters.map Prod.fst).Nodup ∧
          parameters.length = args.length ∧
          ((parameters.zip args).all
            (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true
      · have hResult :
            some (body, HolFiniteMapExact.empty.updateList
              ((parameters.map Prod.fst).zip args), declaredReturn) =
              some (prog, newlocals, returnShape) := by
          simpa [lookupCodeHOLFinite, hCode, hValid] using hLookup
        have hTuple := Option.some.inj hResult
        have hMap : HolFiniteMapExact.empty.updateList
            ((parameters.map Prod.fst).zip args) = newlocals :=
          congrArg Prod.fst (congrArg Prod.snd hTuple)
        have hMapLookup := congrArg HolFiniteMapExact.lookup hMap
        intro name value hValue
        have hFold :
            FUPDATE_LIST (FEMPTY : FiniteMap MlS (ValueHOL width))
              ((parameters.map Prod.fst).zip args) name = some value := by
          rw [← hMapLookup] at hValue
          change FUPDATE_LIST (fun _ => none)
            ((parameters.map Prod.fst).zip args) name = some value
          simpa [HolFiniteMapExact.updateList, HolFiniteMapExact.empty, FEMPTY] using hValue
        have hEntries := flookupFupdateList_mem_or_base
          (FEMPTY : FiniteMap MlS (ValueHOL width))
          ((parameters.map Prod.fst).zip args) name value (by
            simpa [FLOOKUP] using hFold)
        rcases hEntries with ⟨entry, hentry, _, hentryValue⟩ | hbase
        · subst value
          exact evalListHOLExact_mem_isWf state hlocals hglobals argexps args hArgs
            entry.2 (snd_mem_of_mem_zip hentry)
        · simp [FLOOKUP, FEMPTY] at hbase
      · have hLookup' := hLookup
        simp [lookupCodeHOLFinite, hCode] at hLookup'
        have hValid' : (parameters.map Prod.fst).Nodup ∧
            parameters.length = args.length ∧
            ((parameters.zip args).all
              (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2))) = true := by
          refine ⟨hLookup'.1.1, hLookup'.1.2.1, List.all_eq_true.mpr ?_⟩
          intro pair hpair
          exact hLookup'.1.2.2 pair.1.1 pair.1.2 pair.2 hpair
        exact False.elim (hValid hValid')

/-- Flapjack-specific finite-carrier rendering of HOL's local update
    `s with locals := s.locals |+ (n, w)`. The finite carrier's `locals` field
    is a `HolFiniteMapExact`, so the HOL `FUPDATE` (`|+`) is the
    equality-based `HolFiniteMapExact.updateEq`. Untagged adapter, mirroring
    `emptyLocalsForStructsSimps`. -/
def updateLocalsForVarsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (word : ValueHOL width) :
    PanPropsEvalStateFiniteExact width σ :=
  { state with locals := state.locals.updateEq (name, word) }

/-- Projection of the finite-map local update to the canonical broad
    `FUPDATE_HOL` state. -/
@[simp] theorem updateLocalsForVarsSimps_toExact {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (word : ValueHOL width) :
    (updateLocalsForVarsSimps state name word).toExact =
      { state.toExact with locals := FUPDATE_HOL state.toExact.locals (name, word) } := rfl

/-- Updating `locals` changes no other state component, so the address-set
    decision procedure is inherited. -/
instance updateLocalsForVarsSimpsDecidablePred {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (word : ValueHOL width)
    [DecidablePred state.memaddrs] :
    DecidablePred (updateLocalsForVarsSimps state name word).memaddrs :=
  (inferInstance : DecidablePred state.memaddrs)

/-- Finite-carrier evaluation after `updateLocalsForVarsSimps` is the broad
    exact evaluation over the canonical `FUPDATE_HOL` state. -/
@[simp] theorem evalHOL_updateLocalsForVarsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (name : MlS) (word : ValueHOL width) (expression : ExpHOL width) :
    (updateLocalsForVarsSimps state name word).evalHOL expression =
      @evalHOLExact width σ _ { state.toExact with
        locals := FUPDATE_HOL state.toExact.locals (name, word) } h expression := rfl

/-- Finite-carrier `OPT_MMAP eval` after `updateLocalsForVarsSimps` is the broad
    exact list step over the canonical `FUPDATE_HOL` state. -/
@[simp] theorem evalListHOL_updateLocalsForVarsSimps {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (name : MlS) (word : ValueHOL width) (expressions : List (ExpHOL width)) :
    (updateLocalsForVarsSimps state name word).evalListHOL expressions =
      @evalListHOLExact width σ _ { state.toExact with
        locals := FUPDATE_HOL state.toExact.locals (name, word) } h expressions := rfl

/-- Exact finite-support port of HOL `panProps$update_locals_not_vars_eval_eq_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:1042`): binding a fresh local
    name `n` to `w` leaves `eval e` unchanged when `n` does not occur in
    `var_exp e`. The quantifier order is HOL's `s e v n w`; HOL's `v` does not
    occur in the hypothesis or conclusion, so HOL type inference gives it a
    fresh independent type variable (distinct from the locals value type of the
    live `w`), and the Lean statement binds it fully polymorphically as
    `{β : Type} (_value : β)`. The
    state is the reviewed PanProps finite-map carrier: `updateLocalsForVarsSimps`
    renders HOL's `locals |+ (n, w)` through `HolFiniteMapExact.updateEq`, and
    `evalHOL` delegates to the exact broad evaluator through `toExact`. The four
    `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the reviewed
    canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier (canonical witness
    `holFmapAsFiniteSupportWitness` in this module). -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "update_locals_not_vars_eval_eq_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem updateLocalsNotVarsEvalEqEqHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (expression : ExpHOL width) {β : Type} (_value : β) (name : MlS)
      (word : ValueHOL width),
      name ∉ varExpHOL expression →
        (updateLocalsForVarsSimps state name word).evalHOL expression = state.evalHOL expression := by
  intro state hdec expression β _value name word h
  rw [evalHOL_updateLocalsForVarsSimps]
  exact evalHOLExact_updLocals_not_mem state.toExact name word expression h

/-- Exact finite-support port of HOL `panProps$update_locals_not_vars_eval_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:1060`): a fresh local binding
    preserves a successful evaluation and its value. Quantifier order is HOL's
    `s e v n w`; the fresh-name premise and the `SOME`-success hypothesis are
    conjoined as in the source. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "update_locals_not_vars_eval_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem updateLocalsNotVarsEvalEqHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (value : ValueHOL width) (name : MlS)
      (word : ValueHOL width),
      (name ∉ varExpHOL expression ∧ state.evalHOL expression = some value) →
        (updateLocalsForVarsSimps state name word).evalHOL expression = some value := by
  intro state hdec expression value name word h
  rw [updateLocalsNotVarsEvalEqEqHOLFinite state expression value name word h.1, h.2]

/-- Exact finite-support port of HOL `panProps$update_locals_not_vars_eval_eq_NONE`
    (`cakeml/pancake/semantics/panPropsScript.sml:1069`): a fresh local binding
    preserves a failing evaluation. Quantifier order is HOL's `s e v n w`; as in
    the source, the dead `v` gets a fresh independent HOL type variable and is
    bound fully polymorphically as `{β : Type} (_value : β)`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "update_locals_not_vars_eval_eq_NONE"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem updateLocalsNotVarsEvalEqNoneHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (expression : ExpHOL width) {β : Type} (_value : β) (name : MlS)
      (word : ValueHOL width),
      (name ∉ varExpHOL expression ∧ state.evalHOL expression = none) →
        (updateLocalsForVarsSimps state name word).evalHOL expression = none := by
  intro state hdec expression β _value name word h
  rw [updateLocalsNotVarsEvalEqEqHOLFinite state expression _value name word h.1, h.2]

/-- Exact finite-support port of HOL `panProps$eval_fresh_var`
    (`cakeml/pancake/semantics/panPropsScript.sml:1078`): binding an absent name
    to any word leaves evaluation unchanged. Same content as
    `updateLocalsNotVarsEvalEqEqHOLFinite` with HOL's dead `v` dropped, matching
    the source's `s e n w` quantifier list. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "eval_fresh_var"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalFreshVarHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (expression : ExpHOL width) (name : MlS) (word : ValueHOL width),
      name ∉ varExpHOL expression →
        (updateLocalsForVarsSimps state name word).evalHOL expression = state.evalHOL expression := by
  intro state hdec expression name word h
  rw [evalHOL_updateLocalsForVarsSimps]
  exact evalHOLExact_updLocals_not_mem state.toExact name word expression h

/-- Exact finite-support port of HOL
    `panProps$OPT_MMAP_update_locals_not_vars_eval_eq`
    (`cakeml/pancake/semantics/panPropsScript.sml:1088`): a fresh local binding
    preserves a successful `OPT_MMAP (eval ·)` over a list of expressions.
    `evalListHOL` is the repository's exact `OPT_MMAP` rendering over the
    finite-support carrier. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "OPT_MMAP_update_locals_not_vars_eval_eq"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem optMmapUpdateLocalsNotVarsEvalEqHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (expressions : List (ExpHOL width)) (values : List (ValueHOL width)) (name : MlS)
      (word : ValueHOL width),
      (name ∉ (expressions.map varExpHOL).flatten ∧
        state.evalListHOL expressions = some values) →
        (updateLocalsForVarsSimps state name word).evalListHOL expressions = some values := by
  intro state hdec expressions values name word h
  rw [evalListHOL_updateLocalsForVarsSimps,
    evalListHOLExact_updLocals_not_mem state.toExact name word expressions h.1]
  exact h.2

/-! ## HOL `evaluate_decls_functions`, `evaluate_decls_eshapes`,
    `evaluate_decls_only_functions`

The ports below inspect only the final state's `code`/`eshapes` (or the whole
final state under an `EVERY is_function` premise); none of them evaluates a
declaration in an abstract result state, so each is stated over the reviewed
finite-map carrier exactly as its HOL source. -/

/-- `|++` after `|+` is `|++` with the entry prepended (`FUPDATE_LIST_cons` on
    the finite-support carrier). Untagged finite-map helper. -/
private theorem updateList_cons {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) (entry : α × β) (entries : List (α × β)) :
    (map.update entry).updateList entries = map.updateList (entry :: entries) := by
  apply HolFiniteMapExact.ext
  rfl

/-- `|++` of the empty list is the identity (`FUPDATE_LIST_nil` on the
    finite-support carrier). Untagged finite-map helper. -/
private theorem updateList_nil {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) : map.updateList [] = map := by
  apply HolFiniteMapExact.ext
  rfl

/-- Exact finite-support port of HOL `panProps$evaluate_decls_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1518`):
    `evaluate_decls s pan_code = SOME s' ==> s'.code = s.code |++ functions
    pan_code`. The quantifier order `s pan_code s'`, the successful-evaluation
    premise, and the code conclusion follow the source. `functionsHOL` is the
    reviewed word-indexed `functions` port and `HolFiniteMapExact.updateList` is
    the canonical finite-support rendering of HOL `|++`. The four `|->` fields
    (`locals`, `globals`, `code`, `eshapes`) are the reviewed canonical
    `HolFiniteMapExact` translation recorded by the `fmap_as_finite_support`
    qualifier (canonical witness `holFmapAsFiniteSupportWitness`). `[NeZero
    width]` models HOL's positive word dimension and `DecidablePred
    state.memaddrs` is computation evidence for the HOL word-set guard.

    PanProps-counterpart exact port (bead flapjack-4ac.4.84, audit
    flapjack-4ac.6). Its proof transfers the successful result through the
    field-for-field `toPanSemFinite` codec and uses the canonical
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite_functions` result lemma
    directly; it does not unfold the PanProps-local recursive proof helper.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_functions"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsFunctionsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      evaluateDeclsPanPropsCanonical state program = some result →
        result.code = state.code.updateList (functionsHOL program) := by
  intro state hdec program result hEval
  letI : DecidablePred state.toPanSemFinite.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hdec
  unfold evaluateDeclsPanPropsCanonical at hEval
  cases hcanonical : PanSemStateFiniteExact.evaluateDeclsHOLFinite
      state.toPanSemFinite program with
  | none => simp [hcanonical] at hEval
  | some canonicalResult =>
      simp only [hcanonical, Option.map_some] at hEval
      have hconverted : ofPanSemFinite canonicalResult = result :=
        Option.some.inj hEval
      have hresult : canonicalResult = result.toPanSemFinite := by
        simpa using congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hconverted
      subst canonicalResult
      have hfunctions := PanSemStateFiniteExact.evaluateDeclsHOLFinite_functions
        state.toPanSemFinite program result.toPanSemFinite hcanonical
      simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hfunctions

private theorem evaluateDeclsHOLFinite_eshapes {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanSemStateFiniteExact width σ),
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state program = some result →
        result.eshapes = state.eshapes.updateList (exceptionsHOL program) := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result hEval
      injection hEval with hEq
      subst hEq
      simp [exceptionsHOL, updateList_nil]
  | cons declaration rest ih =>
      intro result hEval
      cases declaration with
      | name name fields =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite, exceptionsHOL] at hEval ⊢
          exact ih state result hEval
      | decl shape name expression =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          letI : DecidablePred
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state).memaddrs := hdec
          cases heval : PanSemStateFiniteExact.evalHOLFinite
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state) expression with
          | none => simp [heval] at hEval
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                have htail := ih
                  { state with globals := state.globals.update (name, value) } result hEval
                simpa [exceptionsHOL] using htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) } result hEval
            simpa [exceptionsHOL] using htail
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | exnDecl exceptionName shape =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) } result hEval
            rw [htail]
            simp [exceptionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval

/-- Exact finite-support port of HOL `panProps$evaluate_decls_eshapes`
    (`cakeml/pancake/semantics/panPropsScript.sml:1409`):
    `evaluate_decls s ds = SOME s' ==> s'.eshapes = s.eshapes |++ exceptions
    ds`. Quantifier order, premise, and conclusion follow the source;
    `exceptionsHOL` is the reviewed `exceptions` port and
    `HolFiniteMapExact.updateList` renders HOL `|++`.

    PanProps-counterpart exact port (bead flapjack-4ac.4.75, audit
    flapjack-4ac.6). Its proof applies the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` through the field-for-field
    state codec `toPanSemFinite`; it does not unfold the PanProps-local
    recursive proof helper.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_eshapes"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsEshapesHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      evaluateDeclsPanPropsCanonical state program = some result →
        result.eshapes = state.eshapes.updateList (exceptionsHOL program) := by
  intro state hdec program result hEval
  letI : DecidablePred state.toPanSemFinite.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hdec
  unfold evaluateDeclsPanPropsCanonical at hEval
  cases hcanonical : PanSemStateFiniteExact.evaluateDeclsHOLFinite
      state.toPanSemFinite program with
  | none => simp [hcanonical] at hEval
  | some canonicalResult =>
      simp only [hcanonical, Option.map_some] at hEval
      have hconverted : PanPropsEvalStateFiniteExact.ofPanSemFinite canonicalResult = result :=
        Option.some.inj hEval
      have hresult : canonicalResult = result.toPanSemFinite := by
        simpa using congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hconverted
      subst canonicalResult
      have heshapes := evaluateDeclsHOLFinite_eshapes
        state.toPanSemFinite program result.toPanSemFinite hcanonical
      simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using heshapes

private theorem evaluateDeclsHOLFinite_onlyFunctions {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanSemStateFiniteExact width σ),
      program.all isFunctionHOL = true →
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state program = some result →
        result = { state with code := state.code.updateList (functionsHOL program) } := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result _ hEval
      injection hEval with hEq
      subst hEq
      rw [show functionsHOL ([] : List (DeclHOL width)) = [] from rfl]
      cases state
      simp [updateList_nil]
  | cons declaration rest ih =>
      intro result hall hEval
      cases declaration with
      | function declaration =>
          simp only [List.all_cons, isFunctionHOL, Bool.true_and] at hall
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hall hEval
            rw [htail]
            simp [functionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | name name fields =>
          exact absurd hall (by simp [List.all_cons, isFunctionHOL])
      | decl shape name expression =>
          exact absurd hall (by simp [List.all_cons, isFunctionHOL])
      | exnDecl exceptionName shape =>
          exact absurd hall (by simp [List.all_cons, isFunctionHOL])

/-- Exact finite-support port of HOL `panProps$evaluate_decls_only_functions`
    (`cakeml/pancake/semantics/panPropsScript.sml:1528`): under `EVERY
    is_function pan_code`, a successful declaration evaluation changes only
    `code`, appending the function entries. The premise is rendered as `program.all
    isFunctionHOL = true`, the exact `EVERY is_function` reading over the
    reviewed `DeclHOL` carrier; the conclusion is HOL's record update with
    `|++`.

    PanProps-counterpart exact port (bead flapjack-4ac.4.85, audit
    flapjack-4ac.6). Its proof uses a structural lemma about the canonical
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` and transfers the result
    through the field-for-field `toPanSemFinite` codec; it does not unfold the
    PanProps-local recursive proof helper.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_only_functions"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsOnlyFunctionsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      program.all isFunctionHOL = true →
      evaluateDeclsPanPropsCanonical state program = some result →
        result = { state with code := state.code.updateList (functionsHOL program) } := by
  intro state hdec program result hall hEval
  letI : DecidablePred state.toPanSemFinite.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hdec
  unfold evaluateDeclsPanPropsCanonical at hEval
  cases hcanonical : PanSemStateFiniteExact.evaluateDeclsHOLFinite
      state.toPanSemFinite program with
  | none => simp [hcanonical] at hEval
  | some canonicalResult =>
      simp only [hcanonical, Option.map_some] at hEval
      have hconverted : ofPanSemFinite canonicalResult = result :=
        Option.some.inj hEval
      have hresult : canonicalResult = result.toPanSemFinite := by
        simpa using congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hconverted
      subst canonicalResult
      have hfunctions := evaluateDeclsHOLFinite_onlyFunctions
        state.toPanSemFinite program result.toPanSemFinite hall hcanonical
      cases state <;> cases result <;>
        simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hfunctions

section
open Classical

private theorem evaluateDeclsHOLFinite_append {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanSemStateFiniteExact width σ) [_hdec : DecidablePred state.memaddrs]
      (ds1 ds2 : List (DeclHOL width)),
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state (ds1 ++ ds2) =
        Option.bind (PanSemStateFiniteExact.evaluateDeclsHOLFinite state ds1)
          (fun state' => PanSemStateFiniteExact.evaluateDeclsHOLFinite state' ds2) := by
  intro state _hdec ds1
  induction ds1 generalizing state with
  | nil =>
      intro ds2
      simp only [List.nil_append, PanSemStateFiniteExact.evaluateDeclsHOLFinite]
      have hdecEq : _hdec = (fun address => Classical.propDecidable (state.memaddrs address)) :=
        Subsingleton.elim _ _
      rw [hdecEq]
      rfl
  | cons declaration rest ih =>
      intro ds2
      cases declaration with
      | name name fields =>
          simpa [List.cons_append, PanSemStateFiniteExact.evaluateDeclsHOLFinite]
            using ih state ds2
      | decl shape name expression =>
          letI : DecidablePred
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state).memaddrs := by
            simpa [PanSemStateFiniteExact.emptyLocalsHOLFinite] using _hdec
          simp only [List.cons_append, PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          cases heval : PanSemStateFiniteExact.evalHOLFinite
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state) expression with
          | none => simp
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [if_pos hshape]
                exact ih (PanSemStateFiniteExact.setGlobalHOLFinite name value state)
                  (_hdec := _hdec) ds2
              · simp [hshape]
      | function declaration =>
          simp only [List.cons_append, PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos]
            exact ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              (_hdec := _hdec) ds2
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse]
      | exnDecl exceptionName shape =>
          simp only [List.cons_append, PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos]
            exact ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              (_hdec := _hdec) ds2
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse]

/-- Exact finite-support port of HOL `panProps$evaluate_decls_append`
    (`cakeml/pancake/semantics/panPropsScript.sml:1540`): evaluating `ds1 ++ ds2`
    is the monadic bind of evaluating `ds1` and then `ds2` in the resulting
    state. HOL's `case ... of NONE => NONE | SOME s' => ...` is rendered as
    `Option.bind`. The finite-map qualifier records only the four HOL `|->`
    fields. The nested evaluation on HOL's existential result state uses Lean's
    classical decidability for the `memaddrs` word-set guard; `Decidable`
    instances are subsingleton, so this adds no side condition and does not
    change the evaluator's value relative to HOL's total classical logic.

    PanProps-counterpart exact port (bead flapjack-4ac.4.86, audit
    flapjack-4ac.6). Its proof applies a structural append lemma over the
    canonical `PanSemStateFiniteExact.evaluateDeclsHOLFinite` and maps the
    result through the field-for-field `toPanSemFinite` codec; it does not
    unfold the PanProps-local recursive proof helper.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_append"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsAppendHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) (ds1 ds2 : List (DeclHOL width)),
      evaluateDeclsPanPropsCanonical state (ds1 ++ ds2) =
        Option.bind (evaluateDeclsPanPropsCanonical state ds1)
          (fun state' => evaluateDeclsPanPropsCanonical state' ds2) := by
  classical
  intro state ds1 ds2
  letI : DecidablePred state.toPanSemFinite.memaddrs :=
    toPanSemFiniteDecidableMemaddrs state
  unfold evaluateDeclsPanPropsCanonical
  rw [evaluateDeclsHOLFinite_append state.toPanSemFinite ds1 ds2]
  cases hfirst : PanSemStateFiniteExact.evaluateDeclsHOLFinite
      state.toPanSemFinite ds1 <;>
    simp [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite]

end

/-! ## HOL `evaluate_decls_exns_wf`, `evaluate_decls_only_exn_decls`,
    `exns_wf_evaluate_decls`, `evaluate_decls_only_funs_and_exn_decls`

The four ports below prove properties of the final exception table (and, for the
last, the final exception table and code) under evaluation; none evaluates a
declaration in an abstract result state, so each is stated over the reviewed
finite-map carrier exactly as its HOL source. -/

/-- `lookup` after a single `update` at a distinct key is unchanged
    (`FLOOKUP_UPDATE` on the finite-support carrier). Untagged finite-map
    helper. -/
private theorem lookup_update_ne {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) (entry : α × β) (key : α)
    (h : entry.1 ≠ key) :
    (map.update entry).lookup key = map.lookup key := by
  simp only [HolFiniteMapExact.lookup_update, FUPDATE, beq_eq_false_iff_ne.mpr h,
    Bool.false_eq_true, if_false]

/-- Tail freshness survives prepending a distinct exception binding. Untagged
    finite-map helper. -/
private theorem all_isNone_update_forward {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL)
    (entries : List (MlS × ShapeHOL))
    (hne : name ∉ entries.map Prod.fst)
    (hfresh : entries.all (fun entry => (state.eshapes.lookup entry.1).isNone) = true) :
    entries.all (fun entry =>
      ((state.eshapes.update (name, shape)).lookup entry.1).isNone) = true := by
  rw [List.all_eq_true] at hfresh ⊢
  intro entry hentry
  have hkey : name ≠ entry.1 := by
    intro h
    exact hne (List.mem_map.mpr ⟨entry, hentry, h.symm⟩)
  rw [lookup_update_ne state.eshapes (name, shape) entry.1 hkey]
  exact hfresh entry hentry

/-- Tail freshness about the updated table implies freshness about the original
    table when the prepended key is absent from the tail. Untagged finite-map
    helper. -/
private theorem all_isNone_update_backward {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL)
    (entries : List (MlS × ShapeHOL))
    (hne : name ∉ entries.map Prod.fst)
    (hfresh : entries.all (fun entry =>
      ((state.eshapes.update (name, shape)).lookup entry.1).isNone) = true) :
    entries.all (fun entry => (state.eshapes.lookup entry.1).isNone) = true := by
  rw [List.all_eq_true] at hfresh ⊢
  intro entry hentry
  have hkey : name ≠ entry.1 := by
    intro h
    exact hne (List.mem_map.mpr ⟨entry, hentry, h.symm⟩)
  have h := hfresh entry hentry
  rw [lookup_update_ne state.eshapes (name, shape) entry.1 hkey] at h
  exact h

/-- A key freshly bound in the exception table cannot occur in the tail update
    list when the tail is fresh for the updated table. Untagged finite-map
    helper. -/
private theorem notMem_fst_of_all_isNone_update {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (name : MlS) (shape : ShapeHOL)
    (entries : List (MlS × ShapeHOL))
    (hfresh : entries.all (fun entry =>
      ((state.eshapes.update (name, shape)).lookup entry.1).isNone) = true) :
    name ∉ entries.map Prod.fst := by
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨entry, hentry, hkey⟩ := hmem
  rw [List.all_eq_true] at hfresh
  have hlook := hfresh entry hentry
  have hsome : ((state.eshapes.update (name, shape)).lookup name).isNone = true := by
    simpa [hkey] using hlook
  have hval : (state.eshapes.update (name, shape)).lookup name = some shape := by
    rw [HolFiniteMapExact.lookup_update, FUPDATE]
    simp
  rw [hval] at hsome
  simp at hsome

/-- Canonical PanSem recursion helper for the exception-only state invariant.
    It is deliberately stated on `PanSemStateFiniteExact` so the tagged PanProps
    theorem can avoid unfolding its local recursive proof evaluator. -/
private theorem evaluateDeclsHOLFinite_onlyExnDecls {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanSemStateFiniteExact width σ),
      program.all isExnDeclHOL = true →
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state program = some result →
        result = { state with
          eshapes := state.eshapes.updateList (exceptionsHOL program) } := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result _ hEval
      injection hEval with hEq
      subst hEq
      rw [show exceptionsHOL ([] : List (DeclHOL width)) = [] from rfl,
        updateList_nil]
  | cons declaration rest ih =>
      intro result hall hEval
      cases declaration with
      | exnDecl exceptionName shape =>
          simp only [List.all_cons, isExnDeclHOL, Bool.true_and] at hall
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hall hEval
            rw [htail]
            simp [exceptionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | name name fields =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])
      | decl shape name expression =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])
      | function declaration =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])

/-- Exact finite-support port of HOL `panProps$evaluate_decls_only_exn_decls`
    (`cakeml/pancake/semantics/panPropsScript.sml:1436`): if every declaration is
    an exception declaration, a successful evaluation leaves the whole state
    unchanged except for the exception table, which becomes
    `s.eshapes |++ exceptions ds`. Quantifier order `s ds s'`, the
    `EVERY is_exn_decl` premise rendered as `program.all isExnDeclHOL = true`,
    the successful-evaluation premise, and HOL's record update with
    `exceptionsHOL` follow the source.

    PanProps-counterpart exact port (bead flapjack-4ac.4.77, audit
    flapjack-4ac.6). Its proof applies the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` through the field-for-field
    state codec `toPanSemFinite`; it does not unfold the PanProps-local
    recursive proof helper.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_only_exn_decls"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsOnlyExnDeclsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      program.all isExnDeclHOL = true →
      evaluateDeclsPanPropsCanonical state program = some result →
      result = { state with eshapes := state.eshapes.updateList (exceptionsHOL program) } := by
  intro state hdec program result hall hEval
  unfold evaluateDeclsPanPropsCanonical at hEval
  cases hcanonical : PanSemStateFiniteExact.evaluateDeclsHOLFinite
      state.toPanSemFinite program with
  | none => simp [hcanonical] at hEval
  | some final =>
      have hresult : PanPropsEvalStateFiniteExact.ofPanSemFinite final = result := by
        simpa [hcanonical] using hEval
      subst result
      have hfinal := evaluateDeclsHOLFinite_onlyExnDecls
        state.toPanSemFinite program final hall hcanonical
      rw [hfinal]
      simp [PanPropsEvalStateFiniteExact.ofPanSemFinite,
        PanPropsEvalStateFiniteExact.toPanSemFinite]

/-- Canonical PanSem recursion helper for the exception well-formedness
    invariant. The finite-map facts are applied to the PanProps codec view of
    the same canonical state; this keeps the tagged theorem proof off the local
    recursive evaluator. -/
private theorem evaluateDeclsHOLFinite_exnsWf {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanSemStateFiniteExact width σ),
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state program = some result →
        ((exceptionsHOL program).map Prod.fst).Nodup ∧
        (exceptionsHOL program).all
          (fun entry => (state.eshapes.lookup entry.1).isNone) = true ∧
        (exceptionsHOL program).all
          (fun entry => isWfShapeExactHOL state.structs entry.2) = true := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result hEval
      simp [exceptionsHOL]
  | cons declaration rest ih =>
      intro result hEval
      cases declaration with
      | exnDecl exceptionName shape =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have hcondRaw : ((state.eshapes.lookup exceptionName).isNone &&
                isWfShapeExactHOL state.structs shape) = true := by
              simpa [condition] using hcondition
            rw [Bool.and_eq_true] at hcondRaw
            obtain ⟨hfreshHead, hwfHead⟩ := hcondRaw
            have hih := ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hEval
            obtain ⟨hnodupTail, hfreshTail, hwfTail⟩ := hih
            refine ⟨?_, ?_, ?_⟩
            · rw [exceptionsHOL, List.map_cons, List.nodup_cons]
              exact ⟨notMem_fst_of_all_isNone_update
                (PanPropsEvalStateFiniteExact.ofPanSemFinite state) exceptionName shape
                (exceptionsHOL rest) hfreshTail, hnodupTail⟩
            · rw [exceptionsHOL, List.all_cons, Bool.and_eq_true]
              exact ⟨hfreshHead, all_isNone_update_backward
                (PanPropsEvalStateFiniteExact.ofPanSemFinite state) exceptionName shape
                (exceptionsHOL rest)
                (notMem_fst_of_all_isNone_update
                  (PanPropsEvalStateFiniteExact.ofPanSemFinite state) exceptionName shape
                  (exceptionsHOL rest) hfreshTail) hfreshTail⟩
            · rw [exceptionsHOL, List.all_cons, Bool.and_eq_true]
              exact ⟨hwfHead, by simpa using hwfTail⟩
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | name name fields =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          simpa [exceptionsHOL] using ih state result hEval
      | decl shape name expression =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          letI : DecidablePred
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state).memaddrs := hdec
          cases heval : PanSemStateFiniteExact.evalHOLFinite
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state) expression with
          | none => simp [heval] at hEval
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [heval, if_pos hshape] at hEval
                have htail := ih
                  { state with globals := state.globals.update (name, value) } result hEval
                simpa [exceptionsHOL] using htail
              · simp [heval, hshape] at hEval
      | function declaration =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hEval
            simpa [exceptionsHOL] using htail
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval

/-- Exact finite-support port of HOL `panProps$evaluate_decls_exns_wf`
    (`cakeml/pancake/semantics/panPropsScript.sml:1419`): a successful declaration
    evaluation guarantees that the exception ids are all distinct, that every
    exception shape is absent from the original exception table, and that every
    exception shape is well formed in the original structure context. HOL's
    `s'` is used by the success hypothesis, so it is retained.
    `ALL_DISTINCT (MAP FST ...)` is rendered as `Nodup` of the projected id
    list; `FLOOKUP s.eshapes eid = NONE` as the Bool `... .isNone = true`, the
    same key comparison the evaluator's own guard performs; and
    `is_wf_shape s.structs` as the tagged `isWfShapeExactHOL`.

    PanProps-counterpart exact port (bead flapjack-4ac.4.76, audit
    flapjack-4ac.6). Its proof applies the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` through the field-for-field
    state codec `toPanSemFinite`; it does not unfold the PanProps-local
    recursive proof helper.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_exns_wf"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsExnsWfHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      evaluateDeclsPanPropsCanonical state program = some result →
        ((exceptionsHOL program).map Prod.fst).Nodup ∧
        (exceptionsHOL program).all
          (fun entry => (state.eshapes.lookup entry.1).isNone) = true ∧
      (exceptionsHOL program).all
          (fun entry => isWfShapeExactHOL state.structs entry.2) = true := by
  intro state hdec program result hEval
  unfold evaluateDeclsPanPropsCanonical at hEval
  cases hcanonical : PanSemStateFiniteExact.evaluateDeclsHOLFinite
      state.toPanSemFinite program with
  | none => simp [hcanonical] at hEval
  | some final =>
      have hresult : PanPropsEvalStateFiniteExact.ofPanSemFinite final = result := by
        simpa [hcanonical] using hEval
      subst result
      have hfinal := evaluateDeclsHOLFinite_exnsWf
        state.toPanSemFinite program final hcanonical
      simpa [PanPropsEvalStateFiniteExact.ofPanSemFinite,
        PanPropsEvalStateFiniteExact.toPanSemFinite] using hfinal

/-- Untagged canonical recursion support for HOL
    `panProps$exns_wf_evaluate_decls`. The proof is stated over PanSem's
    canonical finite-map carrier and uses PanProps' codec view only for the
    exception-map update facts. -/
private theorem evaluateDeclsHOLFinite_exnsWfEvaluateDecls {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) {γ : Type} (_result : γ),
      program.all isExnDeclHOL = true →
      ((exceptionsHOL program).map Prod.fst).Nodup →
      (exceptionsHOL program).all
        (fun entry => (state.eshapes.lookup entry.1).isNone) = true →
      (exceptionsHOL program).all
        (fun entry => isWfShapeExactHOL state.structs entry.2) = true →
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state program =
        some { state with eshapes := state.eshapes.updateList (exceptionsHOL program) } := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro γ _result _ _ _ _
      rfl
  | cons declaration rest ih =>
      intro γ _result hall hnodup hfresh hwf
      cases declaration with
      | exnDecl exceptionName shape =>
          simp only [List.all_cons, isExnDeclHOL, Bool.true_and] at hall
          rw [exceptionsHOL] at hnodup hfresh hwf
          rw [List.map_cons, List.nodup_cons] at hnodup
          rw [List.all_cons, Bool.and_eq_true] at hfresh
          rw [List.all_cons, Bool.and_eq_true] at hwf
          obtain ⟨hnotmem, hnodupTail⟩ := hnodup
          obtain ⟨hfreshHead, hfreshTail⟩ := hfresh
          obtain ⟨hwfHead, hwfTail⟩ := hwf
          have hcondition : ((state.eshapes.lookup exceptionName).isNone &&
              isWfShapeExactHOL state.structs shape) = true := by
            rw [Bool.and_eq_true]
            exact ⟨hfreshHead, hwfHead⟩
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite, if_pos hcondition]
          have htail := ih
            { state with eshapes := state.eshapes.update (exceptionName, shape) }
            _result hall hnodupTail
            (all_isNone_update_forward
              (PanPropsEvalStateFiniteExact.ofPanSemFinite state) exceptionName shape
              (exceptionsHOL rest) hnotmem hfreshTail)
            (by simpa using hwfTail)
          rw [htail]
          simp [exceptionsHOL, updateList_cons]
      | name name fields =>
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])
      | decl shape name expression =>
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])
      | function declaration =>
          exact absurd hall (by simp [List.all_cons, isExnDeclHOL])

/-- Exact finite-support port of HOL `panProps$exns_wf_evaluate_decls`
    (`cakeml/pancake/semantics/panPropsScript.sml:1448`): the converse
    characterization. Under `EVERY is_exn_decl ds` together with the three
    well-formedness conditions (distinct ids, ids absent from the table,
    well-formed shapes), the evaluation succeeds and yields exactly the state
    with the exception table updated by `exceptions ds`. Premises are rendered
    with the same Bool `all`/`isNone`/`isWfShapeExactHOL` vocabulary as
    `evaluateDeclsExnsWfHOLFinite`. The quantifier order is HOL's `s ds s'`;
    HOL's `s'` does not occur in any hypothesis or in the conclusion, so HOL
    type inference gives it a fresh independent type variable, and the Lean
    statement binds it fully polymorphically as `{γ : Type} (_result : γ)`
    rather than at the narrowed state type.

    PanProps-counterpart exact port (bead flapjack-4ac.4.78, audit
    flapjack-4ac.6). Its proof applies the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` through the field-for-field
    state codec `toPanSemFinite`; it does not unfold the PanProps-local
    recursive proof helper.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "exns_wf_evaluate_decls"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem exnsWfEvaluateDeclsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) {γ : Type} (_result : γ),
      program.all isExnDeclHOL = true →
      ((exceptionsHOL program).map Prod.fst).Nodup →
      (exceptionsHOL program).all
        (fun entry => (state.eshapes.lookup entry.1).isNone) = true →
      (exceptionsHOL program).all
          (fun entry => isWfShapeExactHOL state.structs entry.2) = true →
      evaluateDeclsPanPropsCanonical state program =
        some { state with eshapes := state.eshapes.updateList (exceptionsHOL program) } := by
  intro state hdec program γ _result hall hnodup hfresh hwf
  have hcanonical := evaluateDeclsHOLFinite_exnsWfEvaluateDecls
    state.toPanSemFinite program _result hall (by simpa using hnodup)
    (by simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hfresh)
    (by simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hwf)
  unfold evaluateDeclsPanPropsCanonical
  rw [hcanonical]
  simp [PanPropsEvalStateFiniteExact.ofPanSemFinite,
    PanPropsEvalStateFiniteExact.toPanSemFinite]

/-- Exact finite-support port of HOL
    `panProps$evaluate_decls_only_funs_and_exn_decls`
    (`cakeml/pancake/semantics/panPropsScript.sml:1561`): under
    `EVERY (λd. is_function d ∨ is_exn_decl d) ds`, a successful evaluation
    changes only `code` and `eshapes`, appending `functions ds` and
    `exceptions ds`. The premise is rendered as the Bool
    `program.all (fun d => isFunctionHOL d || isExnDeclHOL d) = true`, the exact
    `EVERY` disjunction over the reviewed `DeclHOL` carrier, and the conclusion
    is HOL's two-field record update with `|++` on both maps.

    PanProps-counterpart exact port (bead flapjack-4ac.4.88, audit
    flapjack-4ac.6). Its proof applies the canonical tagged
    `PanSemStateFiniteExact.evaluateDeclsHOLFinite` through the field-for-field
    state codec `toPanSemFinite`; it does not unfold the PanProps-local
    recursive proof helper.
    The four `|->` fields (`locals`, `globals`, `code`, `eshapes`) are the
    reviewed canonical `HolFiniteMapExact` translation recorded by the
    `fmap_as_finite_support` qualifier; the canonical witness
    `holFmapAsFiniteSupportWitness` is in this module. -/
private theorem evaluateDeclsHOLFinite_onlyFunsAndExnDecls {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanSemStateFiniteExact width σ),
      program.all
        (fun declaration => isFunctionHOL declaration || isExnDeclHOL declaration) = true →
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state program = some result →
        result = { state with
          code := state.code.updateList (functionsHOL program)
          eshapes := state.eshapes.updateList (exceptionsHOL program) } := by
  intro state hdec program
  induction program generalizing state with
  | nil =>
      intro result _ hEval
      injection hEval with hEq
      subst hEq
      rw [show functionsHOL ([] : List (DeclHOL width)) = [] from rfl,
        show exceptionsHOL ([] : List (DeclHOL width)) = [] from rfl]
      rw [updateList_nil, updateList_nil]
  | cons declaration rest ih =>
      intro result hall hEval
      cases declaration with
      | function declaration =>
          simp only [List.all_cons, isFunctionHOL, isExnDeclHOL, Bool.true_or,
            Bool.true_and] at hall
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              result hall hEval
            rw [htail]
            simp [functionsHOL, exceptionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | exnDecl exceptionName shape =>
          simp only [List.all_cons, isFunctionHOL, isExnDeclHOL, Bool.false_or,
            Bool.true_and] at hall
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos] at hEval
            have htail := ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              result hall hEval
            rw [htail]
            simp [functionsHOL, exceptionsHOL, updateList_cons]
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse] at hEval
      | name name fields =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          exact absurd hall (by simp [List.all_cons, isFunctionHOL, isExnDeclHOL])
      | decl shape name expression =>
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite] at hEval
          exact absurd hall (by simp [List.all_cons, isFunctionHOL, isExnDeclHOL])

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_only_funs_and_exn_decls"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsOnlyFunsAndExnDeclsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ) [DecidablePred state.memaddrs]
      (program : List (DeclHOL width)) (result : PanPropsEvalStateFiniteExact width σ),
      program.all
        (fun declaration => isFunctionHOL declaration || isExnDeclHOL declaration) = true →
      evaluateDeclsPanPropsCanonical state program = some result →
        result = { state with
          code := state.code.updateList (functionsHOL program)
          eshapes := state.eshapes.updateList (exceptionsHOL program) } := by
  intro state hdec program result hall hEval
  letI : DecidablePred state.toPanSemFinite.memaddrs := by
    simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hdec
  unfold evaluateDeclsPanPropsCanonical at hEval
  cases hcanonical : PanSemStateFiniteExact.evaluateDeclsHOLFinite
      state.toPanSemFinite program with
  | none => simp [hcanonical] at hEval
  | some canonicalResult =>
      simp only [hcanonical, Option.map_some] at hEval
      have hconverted : PanPropsEvalStateFiniteExact.ofPanSemFinite canonicalResult = result :=
        Option.some.inj hEval
      have hresult : canonicalResult = result.toPanSemFinite := by
        simpa using congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hconverted
      subst canonicalResult
      have honly := evaluateDeclsHOLFinite_onlyFunsAndExnDecls
        state.toPanSemFinite program result.toPanSemFinite hall hcanonical
      have hconverted := congrArg PanPropsEvalStateFiniteExact.ofPanSemFinite honly
      simpa only [PanPropsEvalStateFiniteExact.ofPanSemFinite,
        PanPropsEvalStateFiniteExact.toPanSemFinite] using hconverted
/-- Exact finite-support port of HOL `panProps$evaluate_decls_names`
    (`cakeml/pancake/semantics/panPropsScript.sml:1552`):
    `!s decs. EVERY is_name decs ==> evaluate_decls s decs = SOME s`.
    HOL `EVERY is_name decs` renders as `decs.all isNameHOL = true` (the tagged
    `is_name_def` counterpart). It states the result directly over the canonical
    `PanSemStateFiniteExact` carrier and tagged `evaluateDeclsHOLFinite`; its
    `locals`, `globals`, `code`, and `eshapes` fields use the reviewed
    `HolFiniteMapExact` translation. This module's namespaced witness forwards
    the PanSem roundtrip for checker validation.
    `[NeZero width]` models HOL's positive word dimension and
    `DecidablePred state.memaddrs` is computation evidence for the HOL word-set
    guard. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decls_names"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsNamesHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
    (decs : List (DeclHOL width)) :
    decs.all (fun declaration => Flapjack.Pancake.PanLang.isNameHOL declaration) = true →
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state decs = some state :=
  PanSemStateFiniteExact.evaluateDeclsHOLFinite_names state decs

/-- Exact finite-support port of HOL `panProps$evaluate_decl_commute`
    (`cakeml/pancake/semantics/panPropsScript.sml:1472-1480`):
    `!s fi sh v' e ds. evaluate_decls s (Function fi::Decl sh v' e::ds) =
    evaluate_decls s (Decl sh v' e::Function fi::ds)`. Swapping an adjacent
    `Function`/`Decl` declaration leaves the evaluator unchanged because `Decl`
    clears the locals and updates only `globals`, while `Function` updates only
    `code` and the evaluator does not read `code`. The state is the PanProps
    counterpart carrier over the reviewed canonical `HolFiniteMapExact`
    translation (canonical witness `holFmapAsFiniteSupportWitness` in this
    module). Its statement uses `evaluateDeclsPanPropsCanonical`, which calls
    the canonical tagged PanSem `evaluateDeclsHOLFinite` and maps only the
    result state back through the field-for-field carrier codec. Thus the
    theorem statement itself is about the canonical evaluator. `[NeZero width]` models
    HOL's positive word dimension and `DecidablePred state.memaddrs` is
    computation evidence for the HOL word-set guard. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_decl_commute"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsDeclCommuteHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (fi : FunDeclHOL width) (sh : ShapeHOL) (v' : MlS) (e : ExpHOL width)
    (ds : List (DeclHOL width)) :
    evaluateDeclsPanPropsCanonical state (.function fi :: .decl sh v' e :: ds)
      = evaluateDeclsPanPropsCanonical state (.decl sh v' e :: .function fi :: ds) := by
  letI : DecidablePred state.toPanSemFinite.memaddrs := toPanSemFiniteDecidableMemaddrs state
  have hcanon := PanSemStateFiniteExact.evaluateDeclsHOLFinite_declCommute
    state.toPanSemFinite fi sh v' e ds
  unfold evaluateDeclsPanPropsCanonical
  exact congrArg (fun result => result.map PanPropsEvalStateFiniteExact.ofPanSemFinite) hcanon

/-- Pair-shaped (`result`, state) view of the exact total evaluator over the
    PanProps carrier. This is the HOL `evaluate ... = (result, t)` shape used by
    the exact `evaluate_is_wf_shape_invariant` port; it is definitionally the
    canonical `PanSemStateFiniteExact.evaluateHOLFiniteState` result. -/
noncomputable def evaluateHOLFinitePair {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (program : ProgHOL width) :
    Option (PanSemResultExact width) × PanPropsEvalStateFiniteExact width σ := by
  classical
  let output := PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite program
  exact (output.1, ofPanSemFinite output.2)

end PanPropsEvalStateFiniteExact

namespace PanPropsCanonicalCarrierWitness

/-- Same-module checker witness for PanProps tags stated directly over the
    imported `PanSemStateFiniteExact` carrier. It forwards the canonical
    finite-support roundtrip while the compatibility carrier and its separate
    witness remain in use by older PanProps theorem statements. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  @PanSemStateFiniteExact.holFmapAsFiniteSupportWitness width σ _

end PanPropsCanonicalCarrierWitness

end Flapjack


namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

/-- A small proof-support lemma for the `Call` induction case. It isolates
    the HOL `Call` subcase where argument evaluation fails, in which
    `evaluate_def` returns the source state unchanged. This helper has an
    extra branch premise and so is Flapjack proof infrastructure, not a
    separate port of a HOL declaration. -/
private theorem evaluateInvariantsCallArgsFailureHOLFinite
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width))
    (result : Option (PanSemResultExact width))
    (post : PanPropsEvalStateFiniteExact width σ)
    (hargs : PanSemStateFiniteExact.evalListHOLFinite state.toPanSemFinite
      (h := fun address => Classical.propDecidable
        (state.toPanSemFinite.memaddrs address)) arguments = none)
    (hRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
      (.call info function arguments : ProgHOL width) = (result, post)) :
    post.memaddrs = state.memaddrs ∧
    post.shMemaddrs = state.shMemaddrs ∧
    post.be = state.be ∧
    post.eshapes = state.eshapes ∧
    post.baseAddr = state.baseAddr ∧
    post.structs = state.structs ∧
    post.code = state.code ∧
    post.ffi.oracle = state.ffi.oracle := by
  classical
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  rw [evaluateHOLFiniteState_call, hargs] at hcanonical
  have hpost := congrArg Prod.snd hcanonical
  have hsame : post.toPanSemFinite = state.toPanSemFinite := by
    simpa using hpost.symm
  have hmem := congrArg (fun s : PanSemStateFiniteExact width σ => s.memaddrs) hsame
  have hshared := congrArg (fun s : PanSemStateFiniteExact width σ => s.shMemaddrs) hsame
  have hbe := congrArg (fun s : PanSemStateFiniteExact width σ => s.be) hsame
  have heshapes := congrArg (fun s : PanSemStateFiniteExact width σ => s.eshapes) hsame
  have hbase := congrArg (fun s : PanSemStateFiniteExact width σ => s.baseAddr) hsame
  have hstructs := congrArg (fun s : PanSemStateFiniteExact width σ => s.structs) hsame
  have hcode := congrArg (fun s : PanSemStateFiniteExact width σ => s.code) hsame
  have horacle := congrArg (fun s : PanSemStateFiniteExact width σ => s.ffi.oracle) hsame
  simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using
    And.intro hmem (And.intro hshared (And.intro hbe (And.intro heshapes
      (And.intro hbase (And.intro hstructs (And.intro hcode horacle))))))

/-- Proof-support for the next HOL `Call` early exit: a successfully evaluated
    argument list whose code lookup fails leaves the state unchanged. This
    branch-specific helper is not itself a HOL theorem port. -/
private theorem evaluateInvariantsCallLookupFailureHOLFinite
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (result : Option (PanSemResultExact width))
    (post : PanPropsEvalStateFiniteExact width σ)
    (hargs : PanSemStateFiniteExact.evalListHOLFinite state.toPanSemFinite
      (h := fun address => Classical.propDecidable
        (state.toPanSemFinite.memaddrs address)) arguments = some values)
    (hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite
      state.toPanSemFinite.code.lookup function values = none)
    (hRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
      (.call info function arguments : ProgHOL width) = (result, post)) :
    post.memaddrs = state.memaddrs ∧
    post.shMemaddrs = state.shMemaddrs ∧
    post.be = state.be ∧
    post.eshapes = state.eshapes ∧
    post.baseAddr = state.baseAddr ∧
    post.structs = state.structs ∧
    post.code = state.code ∧
    post.ffi.oracle = state.ffi.oracle := by
  classical
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  simp only [evaluateHOLFiniteState_call, hargs, hlookup] at hcanonical
  have hpost := congrArg Prod.snd hcanonical
  have hsame : post.toPanSemFinite = state.toPanSemFinite := by
    simpa using hpost.symm
  have hmem := congrArg (fun s : PanSemStateFiniteExact width σ => s.memaddrs) hsame
  have hshared := congrArg (fun s : PanSemStateFiniteExact width σ => s.shMemaddrs) hsame
  have hbe := congrArg (fun s : PanSemStateFiniteExact width σ => s.be) hsame
  have heshapes := congrArg (fun s : PanSemStateFiniteExact width σ => s.eshapes) hsame
  have hbase := congrArg (fun s : PanSemStateFiniteExact width σ => s.baseAddr) hsame
  have hstructs := congrArg (fun s : PanSemStateFiniteExact width σ => s.structs) hsame
  have hcode := congrArg (fun s : PanSemStateFiniteExact width σ => s.code) hsame
  have horacle := congrArg (fun s : PanSemStateFiniteExact width σ => s.ffi.oracle) hsame
  simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using
    And.intro hmem (And.intro hshared (And.intro hbe (And.intro heshapes
      (And.intro hbase (And.intro hstructs (And.intro hcode horacle))))))

/-- Proof-support for the HOL `Call` timeout branch: the source evaluator
    returns the original state with only `locals` cleared. This helper has an
    extra source-branch premise and is not itself a HOL theorem port. -/
private theorem evaluateInvariantsCallTimeoutHOLFinite
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width)) (values : List (ValueHOL width))
    (body : ProgHOL width) (callee : HolFiniteMapExact MlS (ValueHOL width))
    (returnShape : ShapeHOL) (result : Option (PanSemResultExact width))
    (post : PanPropsEvalStateFiniteExact width σ)
    (hargs : PanSemStateFiniteExact.evalListHOLFinite state.toPanSemFinite
      (h := fun address => Classical.propDecidable
        (state.toPanSemFinite.memaddrs address)) arguments = some values)
    (hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite
      state.toPanSemFinite.code.lookup function values = some (body, callee, returnShape))
    (hclock : state.toPanSemFinite.clock = 0)
    (hRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
      (.call info function arguments : ProgHOL width) = (result, post)) :
    post.memaddrs = state.memaddrs ∧
    post.shMemaddrs = state.shMemaddrs ∧
    post.be = state.be ∧
    post.eshapes = state.eshapes ∧
    post.baseAddr = state.baseAddr ∧
    post.structs = state.structs ∧
    post.code = state.code ∧
    post.ffi.oracle = state.ffi.oracle := by
  classical
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  simp only [evaluateHOLFiniteState_call, hargs, hlookup, if_pos hclock] at hcanonical
  have hpost := congrArg Prod.snd hcanonical
  have hsame : post.toPanSemFinite =
      PanSemStateFiniteExact.emptyLocalsHOLFinite state.toPanSemFinite := by
    simpa using hpost.symm
  have hmem := congrArg (fun s : PanSemStateFiniteExact width σ => s.memaddrs) hsame
  have hshared := congrArg (fun s : PanSemStateFiniteExact width σ => s.shMemaddrs) hsame
  have hbe := congrArg (fun s : PanSemStateFiniteExact width σ => s.be) hsame
  have heshapes := congrArg (fun s : PanSemStateFiniteExact width σ => s.eshapes) hsame
  have hbase := congrArg (fun s : PanSemStateFiniteExact width σ => s.baseAddr) hsame
  have hstructs := congrArg (fun s : PanSemStateFiniteExact width σ => s.structs) hsame
  have hcode := congrArg (fun s : PanSemStateFiniteExact width σ => s.code) hsame
  have horacle := congrArg (fun s : PanSemStateFiniteExact width σ => s.ffi.oracle) hsame
  simpa [PanSemStateFiniteExact.emptyLocalsHOLFinite,
    PanPropsEvalStateFiniteExact.toPanSemFinite] using
    And.intro hmem (And.intro hshared (And.intro hbe (And.intro heshapes
      (And.intro hbase (And.intro hstructs (And.intro hcode horacle))))))

private def evaluateInvariantsCallBodyClassification
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (returnShape : ShapeHOL) (bodyResult : Option (PanSemResultExact width)) : Prop :=
    bodyResult = none ∨ bodyResult = some .break ∨
    bodyResult = some .continue ∨ bodyResult = some .error ∨
    bodyResult = some .timeOut ∨ (∃ event, bodyResult = some (.finalFfi event)) ∨
    (∃ value, bodyResult = some (.returned value) ∧
      shapeEqHOL (shapeOfHOLExact value) returnShape = false) ∨
    (∃ value, bodyResult = some (.returned value) ∧
      shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧ info = none) ∨
    (∃ value handler, bodyResult = some (.returned value) ∧
      shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧ info = some (none, handler)) ∨
    (∃ value kind name handler, bodyResult = some (.returned value) ∧
      shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧
      info = some (some (kind, name), handler)) ∨
    (∃ exceptionId value, bodyResult = some (.exception exceptionId value) ∧ info = none) ∨
    (∃ exceptionId value returnInfo,
      bodyResult = some (.exception exceptionId value) ∧ info = some (returnInfo, none)) ∨
    (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram,
      bodyResult = some (.exception exceptionId value) ∧
      info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
      exceptionId ≠ handlerId) ∨
    (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram,
      bodyResult = some (.exception exceptionId value) ∧
      info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
      exceptionId = handlerId ∧ state.toPanSemFinite.eshapes.lookup exceptionId = none) ∨
    (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram declaredShape,
      bodyResult = some (.exception exceptionId value) ∧
      info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
      exceptionId = handlerId ∧ state.toPanSemFinite.eshapes.lookup exceptionId = some declaredShape ∧
      (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
        isValidValueHOLExact state.toPanSemFinite.toExact VarKind.local handlerVar value) = false) ∨
    (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram declaredShape,
      bodyResult = some (.exception exceptionId value) ∧
      info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
      exceptionId = handlerId ∧ state.toPanSemFinite.eshapes.lookup exceptionId = some declaredShape ∧
      (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
        isValidValueHOLExact state.toPanSemFinite.toExact VarKind.local handlerVar value) = true)

private theorem evaluateInvariantsCallBodyClassification_complete
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (returnShape : ShapeHOL) (bodyResult : Option (PanSemResultExact width)) :
    evaluateInvariantsCallBodyClassification state info returnShape bodyResult := by
  cases bodyResult with
  | none => simp [evaluateInvariantsCallBodyClassification]
  | some result =>
      cases result with
      | error => simp [evaluateInvariantsCallBodyClassification]
      | timeOut => simp [evaluateInvariantsCallBodyClassification]
      | «break» => simp [evaluateInvariantsCallBodyClassification]
      | «continue» => simp [evaluateInvariantsCallBodyClassification]
      | finalFfi event => simp [evaluateInvariantsCallBodyClassification]
      | returned value =>
          by_cases hshape : shapeEqHOL (shapeOfHOLExact value) returnShape = true
          · cases info with
            | none => simp [evaluateInvariantsCallBodyClassification, hshape]
            | some info' =>
                cases info' with
                | mk returnInfo handler =>
                    cases returnInfo with
                    | none => simp [evaluateInvariantsCallBodyClassification, hshape]
                    | some target =>
                        cases target with
                        | mk kind name => simp [evaluateInvariantsCallBodyClassification, hshape]
          · have hshapeFalse : shapeEqHOL (shapeOfHOLExact value) returnShape = false := by
              cases h : shapeEqHOL (shapeOfHOLExact value) returnShape <;> simp_all
            simp [evaluateInvariantsCallBodyClassification, hshapeFalse]
      | exception exceptionId value =>
          cases info with
          | none => simp [evaluateInvariantsCallBodyClassification]
          | some info' =>
              cases info' with
              | mk returnInfo handler =>
                  cases handler with
                  | none => simp [evaluateInvariantsCallBodyClassification]
                  | some handlerInfo =>
                      cases handlerInfo with
                      | mk handlerId handlerRest =>
                          cases handlerRest with
                          | mk handlerVar handlerProgram =>
                              by_cases heq : exceptionId = handlerId
                              · cases hshape : state.toPanSemFinite.eshapes.lookup exceptionId with
                                | none =>
                                    unfold evaluateInvariantsCallBodyClassification
                                    right; right; right; right; right; right; right; right; right; right
                                    right; right; right; left
                                    exact ⟨exceptionId, value, returnInfo, handlerId,
                                      handlerVar, handlerProgram, rfl, rfl, heq, hshape⟩
                                | some declaredShape =>
                                    by_cases hcond : (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
                                      isValidValueHOLExact state.toPanSemFinite.toExact
                                        VarKind.local handlerVar value) = true
                                    · unfold evaluateInvariantsCallBodyClassification
                                      right; right; right; right; right; right; right; right; right; right
                                      right; right; right; right; right
                                      exact ⟨exceptionId, value, returnInfo, handlerId,
                                        handlerVar, handlerProgram, declaredShape,
                                        rfl, rfl, heq, hshape, hcond⟩
                                    · have hcondFalse : (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
                                          isValidValueHOLExact state.toPanSemFinite.toExact
                                            VarKind.local handlerVar value) = false := by
                                        cases h : (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
                                          isValidValueHOLExact state.toPanSemFinite.toExact
                                            VarKind.local handlerVar value) <;> simp_all
                                      unfold evaluateInvariantsCallBodyClassification
                                      right; right; right; right; right; right; right; right; right; right
                                      right; right; right; right; left
                                      exact ⟨exceptionId, value, returnInfo, handlerId,
                                        handlerVar, handlerProgram, declaredShape,
                                        rfl, rfl, heq, hshape, hcondFalse⟩
                              · unfold evaluateInvariantsCallBodyClassification
                                right; right; right; right; right; right; right; right; right; right
                                right; right; left
                                exact ⟨exceptionId, value, returnInfo, handlerId,
                                  handlerVar, handlerProgram, rfl, rfl, heq⟩

/-! # HOL `OPT_MMAP eval` rendering for the finite Call carrier

The checked-in `evaluate_ind` probe states the Call premises using HOL's
`OPT_MMAP (eval s) argexps`. `evalListHOLFinite` is the finite-support carrier
rendering of that operation. This Flapjack-specific bridge is untagged because
it translates the HOL list operation to Lean `List.mapM`; the exact Call leaf
below consumes this bridge through its binder-aligned callee IH.
-/

private theorem evalListHOLFinite_eq_mapM {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (expressions : List (ExpHOL width)) :
    state.evalListHOLFinite expressions = expressions.mapM (state.evalHOLFinite) := by
  rw [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact]
  exact evalListHOLExact_eq_mapM state.toExact expressions


/-! ## Binder-aligned Call induction hypotheses

These Flapjack-specific abbreviations spell the two recursive predicates from
the checked `evaluate_ind` Call conjunct over the finite-support carrier. The
map-valued code result is nested like HOL's `(prog,(newlocals,return_sh))`,
while `lookupCodeHOLFinite` stores the same components as a triple. The list
premise is `List.mapM`, the Lean rendering of HOL `OPT_MMAP`. These aliases are
untagged source-shape infrastructure; the tagged exact Call leaf consumes them
below. See the probe output beside the HOL oracle.
-/

private abbrev evaluateInvariantsAtHOLFinite {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    (program : ProgHOL width) : Prop :=
  ∀ (result : Option (PanSemResultExact width))
    (post : PanPropsEvalStateFiniteExact width σ),
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state program = (result, post) →
    post.memaddrs = state.memaddrs ∧
    post.shMemaddrs = state.shMemaddrs ∧
    post.be = state.be ∧
    post.eshapes = state.eshapes ∧
    post.baseAddr = state.baseAddr ∧
    post.structs = state.structs ∧
    post.code = state.code ∧
    post.ffi.oracle = state.ffi.oracle

private abbrev evaluateInvariantsCallCalleeIH {width : Nat} {σ : Type}
    [NeZero width] (function : MlS) (arguments : List (ExpHOL width))
    (state : PanPropsEvalStateFiniteExact width σ) :
    Prop :=
  ∀ (args : List (ValueHOL width))
    (v7 : ProgHOL width × (HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL))
    (prog : ProgHOL width)
    (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (return_sh : ShapeHOL),
    arguments.mapM (fun expression =>
      PanSemStateFiniteExact.evalHOLFinite state.toPanSemFinite
        (h := fun address => Classical.propDecidable
          (state.toPanSemFinite.memaddrs address)) expression) = some args →
    PanSemStateFiniteExact.lookupCodeHOLFinite state.toPanSemFinite.code.lookup
      function args = some (v7.1, v7.2.1, v7.2.2) →
    v7 = (prog, v12) →
    v12 = (newlocals, return_sh) →
    state.toPanSemFinite.clock ≠ 0 →
    evaluateInvariantsAtHOLFinite
      (PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.callEntryStateHOLFinite state.toPanSemFinite newlocals)) prog

private abbrev evaluateInvariantsCallHandlerIH {width : Nat} {σ : Type}
    [NeZero width] (info : Option (Option (VarKind × MlS) ×
      Option (MlS × MlS × ProgHOL width))) (function : MlS)
    (arguments : List (ExpHOL width)) (state : PanPropsEvalStateFiniteExact width σ) :
    Prop :=
  ∀ (args : List (ValueHOL width))
    (v7 : ProgHOL width × (HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL))
    (prog : ProgHOL width)
    (v12 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (return_sh : ShapeHOL)
    (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (v4 : Option (PanSemResultExact width))
    (st : PanSemStateFiniteExact width σ)
    (v8 : PanSemResultExact width) (eid : MlS) (exn : ValueHOL width)
    (v : Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))
    (v1 : Option (VarKind × MlS)) (v2 : Option (MlS × MlS × ProgHOL width))
    (v3 : MlS × MlS × ProgHOL width) (eid' : MlS)
    (v5 : MlS × ProgHOL width) (evar : MlS) (p : ProgHOL width) (sh : ShapeHOL),
    arguments.mapM (fun expression =>
      PanSemStateFiniteExact.evalHOLFinite state.toPanSemFinite
        (h := fun address => Classical.propDecidable
          (state.toPanSemFinite.memaddrs address)) expression) = some args →
    PanSemStateFiniteExact.lookupCodeHOLFinite state.toPanSemFinite.code.lookup
      function args = some (v7.1, v7.2.1, v7.2.2) →
    v7 = (prog, v12) →
    v12 = (newlocals, return_sh) →
    state.toPanSemFinite.clock ≠ 0 →
    eval_prog = PanSemStateFiniteExact.evaluateHOLFiniteState
      (PanSemStateFiniteExact.callEntryStateHOLFinite state.toPanSemFinite newlocals) prog →
    eval_prog = (v4, st) →
    v4 = some v8 →
    v8 = .exception eid exn →
    info = some v →
    v = (v1, v2) →
    v2 = some v3 →
    v3 = (eid', v5) →
    v5 = (evar, p) →
    eid = eid' →
    state.toPanSemFinite.eshapes.lookup eid = some sh →
    shapeOfHOLExact exn = sh →
    isValidValueHOLExact state.toPanSemFinite.toExact VarKind.local evar exn = true →
    evaluateInvariantsAtHOLFinite
      (PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.setVarHOLFinite evar exn
          { st with locals := state.toPanSemFinite.locals })) p


/- Proof-support for the recursive result branches of HOL `Call`. It carries
    the callee body invariant through errors, timeouts, FFI completion, normal
    returns, unhandled/error exceptions, and a valid matched handler using the
    nested program IH. Its explicit result-classification premise means this is
    still infrastructure, not the tagged Call induction case. -/
private theorem evaluateInvariantsCallBodyResultBranchesHOLFinite
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (function : MlS) (arguments : List (ExpHOL width))
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (returnShape : ShapeHOL)
    (bodyResult : Option (PanSemResultExact width))
    (bodyPost : PanSemStateFiniteExact width σ)
    (result : Option (PanSemResultExact width))
    (post : PanPropsEvalStateFiniteExact width σ)
    (ihBody : evaluateInvariantsCallCalleeIH function arguments state)
    (ihHandler : evaluateInvariantsCallHandlerIH info function arguments state)
    (hargs : PanSemStateFiniteExact.evalListHOLFinite state.toPanSemFinite
      (h := fun address => Classical.propDecidable
        (state.toPanSemFinite.memaddrs address)) arguments = some values)
    (hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite
      state.toPanSemFinite.code.lookup function values = some (body, callee, returnShape))
    (hclock : state.toPanSemFinite.clock ≠ 0)
    (hbody : PanSemStateFiniteExact.evaluateHOLFiniteState
      (PanSemStateFiniteExact.callEntryStateHOLFinite state.toPanSemFinite callee) body =
        (bodyResult, bodyPost))
    (hbodyKind : bodyResult = none ∨ bodyResult = some .break ∨
      bodyResult = some .continue ∨ bodyResult = some .error ∨
      bodyResult = some .timeOut ∨
      (∃ event, bodyResult = some (.finalFfi event)) ∨
      (∃ value, bodyResult = some (.returned value) ∧
        shapeEqHOL (shapeOfHOLExact value) returnShape = false) ∨
      (∃ value, bodyResult = some (.returned value) ∧
        shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧ info = none) ∨
      (∃ value handler, bodyResult = some (.returned value) ∧
        shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧
        info = some (none, handler)) ∨
      (∃ value kind name handler, bodyResult = some (.returned value) ∧
        shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧
        info = some (some (kind, name), handler)) ∨
      (∃ exceptionId value, bodyResult = some (.exception exceptionId value) ∧
        info = none) ∨
      (∃ exceptionId value returnInfo,
        bodyResult = some (.exception exceptionId value) ∧
        info = some (returnInfo, none)) ∨
      (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram,
        bodyResult = some (.exception exceptionId value) ∧
        info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
        exceptionId ≠ handlerId) ∨
      (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram,
        bodyResult = some (.exception exceptionId value) ∧
        info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
        exceptionId = handlerId ∧
        state.toPanSemFinite.eshapes.lookup exceptionId = none) ∨
      (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram declaredShape,
        bodyResult = some (.exception exceptionId value) ∧
        info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
        exceptionId = handlerId ∧
        state.toPanSemFinite.eshapes.lookup exceptionId = some declaredShape ∧
        (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
          isValidValueHOLExact state.toPanSemFinite.toExact VarKind.local handlerVar value) = false) ∨
      (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram declaredShape,
        bodyResult = some (.exception exceptionId value) ∧
        info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
        exceptionId = handlerId ∧
        state.toPanSemFinite.eshapes.lookup exceptionId = some declaredShape ∧
        (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
          isValidValueHOLExact state.toPanSemFinite.toExact VarKind.local handlerVar value) = true))
    (hRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
      (.call info function arguments : ProgHOL width) = (result, post)) :
    post.memaddrs = state.memaddrs ∧
    post.shMemaddrs = state.shMemaddrs ∧
    post.be = state.be ∧
    post.eshapes = state.eshapes ∧
    post.baseAddr = state.baseAddr ∧
    post.structs = state.structs ∧
    post.code = state.code ∧
    post.ffi.oracle = state.ffi.oracle := by
  classical
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.call info function arguments : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  let entry := PanSemStateFiniteExact.callEntryStateHOLFinite state.toPanSemFinite callee
  let entryProps := PanPropsEvalStateFiniteExact.ofPanSemFinite entry
  let bodyPostProps := PanPropsEvalStateFiniteExact.ofPanSemFinite bodyPost
  have hbodyPair :
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair entryProps body =
        (bodyResult, bodyPostProps) := by
    simp [entryProps, bodyPostProps, entry,
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, hbody]
  have hentryClock : entryProps.clock < state.clock := by
    have hentry : entry.clock < state.toPanSemFinite.clock := by
      simp [entry, PanSemStateFiniteExact.callEntryStateHOLFinite]
      omega
    simpa [entryProps, PanPropsEvalStateFiniteExact.ofPanSemFinite,
      PanPropsEvalStateFiniteExact.toPanSemFinite] using hentry
  have hargsMapM : arguments.mapM (fun expression =>
      PanSemStateFiniteExact.evalHOLFinite state.toPanSemFinite
        (h := fun address => Classical.propDecidable
          (state.toPanSemFinite.memaddrs address)) expression) = some values := by
    have hargsExact := hargs
    rw [PanSemStateFiniteExact.evalListHOLFinite_eq_toExact,
      evalListHOLExact_eq_mapM] at hargsExact
    simpa only [PanSemStateFiniteExact.evalHOLFinite_eq_toExact] using hargsExact
  have hbodyInvAt := ihBody values (body, (callee, returnShape)) body
    (callee, returnShape) callee returnShape
    hargsMapM hlookup rfl rfl hclock
  have hbodyInv := hbodyInvAt bodyResult bodyPostProps hbodyPair
  have hbodyFields :
      bodyPost.memaddrs = state.toPanSemFinite.memaddrs ∧
      bodyPost.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
      bodyPost.be = state.toPanSemFinite.be ∧
      bodyPost.eshapes = state.toPanSemFinite.eshapes ∧
      bodyPost.baseAddr = state.toPanSemFinite.baseAddr ∧
      bodyPost.structs = state.toPanSemFinite.structs ∧
      bodyPost.code = state.toPanSemFinite.code ∧
      bodyPost.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
    simpa [entryProps, bodyPostProps, entry,
      PanSemStateFiniteExact.callEntryStateHOLFinite,
      PanPropsEvalStateFiniteExact.ofPanSemFinite,
      PanPropsEvalStateFiniteExact.toPanSemFinite] using hbodyInv
  have hfinish (output : PanSemStateFiniteExact width σ)
      (houtput : output = post.toPanSemFinite)
      (hfields :
        output.memaddrs = state.toPanSemFinite.memaddrs ∧
        output.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
        output.be = state.toPanSemFinite.be ∧
        output.eshapes = state.toPanSemFinite.eshapes ∧
        output.baseAddr = state.toPanSemFinite.baseAddr ∧
        output.structs = state.toPanSemFinite.structs ∧
        output.code = state.toPanSemFinite.code ∧
        output.ffi.oracle = state.toPanSemFinite.ffi.oracle) :
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
    have hpost : post = PanPropsEvalStateFiniteExact.ofPanSemFinite output := by
      have h := congrArg PanPropsEvalStateFiniteExact.ofPanSemFinite houtput.symm
      simpa using h
    subst post
    simpa [PanPropsEvalStateFiniteExact.ofPanSemFinite,
      PanPropsEvalStateFiniteExact.toPanSemFinite] using hfields
  simp only [evaluateHOLFiniteState_call, hargs, hlookup, if_neg hclock, hbody]
    at hcanonical
  rcases hbodyKind with hnone | hbreak | hcontinue
      | herror | htimeout | ⟨event, hffi⟩ | ⟨value, hreturn, hshapeFalse⟩
      | ⟨value, hreturn, hshapeTrue, hinfo⟩
      | ⟨value, handler, hreturn, hshapeTrue, hinfo⟩
      | ⟨value, kind, name, handler, hreturn, hshapeTrue, hinfo⟩
      | ⟨exceptionId, value, hexception, hinfo⟩
      | ⟨exceptionId, value, returnInfo, hexception, hinfo⟩
      | ⟨exceptionId, value, returnInfo, handlerId, handlerVar, handlerProgram,
          hexception, hinfo, hne⟩
      | ⟨exceptionId, value, returnInfo, handlerId, handlerVar, handlerProgram,
          hexception, hinfo, heq, hshapeNone⟩
      | ⟨exceptionId, value, returnInfo, handlerId, handlerVar, handlerProgram,
          declaredShape, hexception, hinfo, heq, hshapeSome, hcondFalse⟩
      | ⟨exceptionId, value, returnInfo, handlerId, handlerVar, handlerProgram,
          declaredShape, hexception, hinfo, heq, hshapeSome, hcondTrue⟩
  · simp only [hnone] at hcanonical
    exact hfinish bodyPost (by simpa using congrArg Prod.snd hcanonical) hbodyFields
  · simp only [hbreak] at hcanonical
    exact hfinish bodyPost (by simpa using congrArg Prod.snd hcanonical) hbodyFields
  · simp only [hcontinue] at hcanonical
    exact hfinish bodyPost (by simpa using congrArg Prod.snd hcanonical) hbodyFields
  · simp only [herror] at hcanonical
    let empty := PanSemStateFiniteExact.emptyLocalsHOLFinite bodyPost
    have hemptyFields :
        empty.memaddrs = state.toPanSemFinite.memaddrs ∧
        empty.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
        empty.be = state.toPanSemFinite.be ∧
        empty.eshapes = state.toPanSemFinite.eshapes ∧
        empty.baseAddr = state.toPanSemFinite.baseAddr ∧
        empty.structs = state.toPanSemFinite.structs ∧
        empty.code = state.toPanSemFinite.code ∧
        empty.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
      simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hbodyFields
    exact hfinish empty
      (by simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using
        congrArg Prod.snd hcanonical) hemptyFields
  · simp only [htimeout] at hcanonical
    let empty := PanSemStateFiniteExact.emptyLocalsHOLFinite bodyPost
    have hemptyFields :
        empty.memaddrs = state.toPanSemFinite.memaddrs ∧
        empty.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
        empty.be = state.toPanSemFinite.be ∧
        empty.eshapes = state.toPanSemFinite.eshapes ∧
        empty.baseAddr = state.toPanSemFinite.baseAddr ∧
        empty.structs = state.toPanSemFinite.structs ∧
        empty.code = state.toPanSemFinite.code ∧
        empty.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
      simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hbodyFields
    exact hfinish empty
      (by simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using
        congrArg Prod.snd hcanonical) hemptyFields
  · simp only [hffi] at hcanonical
    let empty := PanSemStateFiniteExact.emptyLocalsHOLFinite bodyPost
    have hemptyFields :
        empty.memaddrs = state.toPanSemFinite.memaddrs ∧
        empty.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
        empty.be = state.toPanSemFinite.be ∧
        empty.eshapes = state.toPanSemFinite.eshapes ∧
        empty.baseAddr = state.toPanSemFinite.baseAddr ∧
        empty.structs = state.toPanSemFinite.structs ∧
        empty.code = state.toPanSemFinite.code ∧
        empty.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
      simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hbodyFields
    exact hfinish empty
      (by simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using
        congrArg Prod.snd hcanonical) hemptyFields
  · simp only [hreturn, hshapeFalse] at hcanonical
    exact hfinish bodyPost (by simpa using congrArg Prod.snd hcanonical) hbodyFields
  · simp only [hreturn, hshapeTrue, hinfo] at hcanonical
    let empty := PanSemStateFiniteExact.emptyLocalsHOLFinite bodyPost
    have hemptyFields :
        empty.memaddrs = state.toPanSemFinite.memaddrs ∧
        empty.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
        empty.be = state.toPanSemFinite.be ∧
        empty.eshapes = state.toPanSemFinite.eshapes ∧
        empty.baseAddr = state.toPanSemFinite.baseAddr ∧
        empty.structs = state.toPanSemFinite.structs ∧
        empty.code = state.toPanSemFinite.code ∧
        empty.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
      simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hbodyFields
    exact hfinish empty
      (by simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using
        congrArg Prod.snd hcanonical) hemptyFields
  · simp only [hreturn, hshapeTrue, hinfo] at hcanonical
    let restored := { bodyPost with locals := state.toPanSemFinite.locals }
    have hrestoredFields :
        restored.memaddrs = state.toPanSemFinite.memaddrs ∧
        restored.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
        restored.be = state.toPanSemFinite.be ∧
        restored.eshapes = state.toPanSemFinite.eshapes ∧
        restored.baseAddr = state.toPanSemFinite.baseAddr ∧
        restored.structs = state.toPanSemFinite.structs ∧
        restored.code = state.toPanSemFinite.code ∧
        restored.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
      simpa [restored] using hbodyFields
    exact hfinish restored
      (by simpa [restored] using congrArg Prod.snd hcanonical) hrestoredFields
  · simp only [hreturn, hshapeTrue, hinfo] at hcanonical
    by_cases hvalid : isValidValueHOLExact
        state.toPanSemFinite.toExact kind name value = true
    · simp only [hvalid] at hcanonical
      let restored := { bodyPost with locals := state.toPanSemFinite.locals }
      let output := PanSemStateFiniteExact.setKvarHOLFinite kind name value restored
      have houtputFields :
          output.memaddrs = state.toPanSemFinite.memaddrs ∧
          output.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
          output.be = state.toPanSemFinite.be ∧
          output.eshapes = state.toPanSemFinite.eshapes ∧
          output.baseAddr = state.toPanSemFinite.baseAddr ∧
          output.structs = state.toPanSemFinite.structs ∧
          output.code = state.toPanSemFinite.code ∧
          output.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
        cases kind <;> simpa [output, PanSemStateFiniteExact.setKvarHOLFinite,
          PanSemStateFiniteExact.setVarHOLFinite,
          PanSemStateFiniteExact.setGlobalHOLFinite, restored] using hbodyFields
      exact hfinish output
        (by cases kind <;> simpa [output, PanSemStateFiniteExact.setKvarHOLFinite,
          PanSemStateFiniteExact.setVarHOLFinite,
          PanSemStateFiniteExact.setGlobalHOLFinite, restored] using
          congrArg Prod.snd hcanonical) houtputFields
    · have hinvalid : isValidValueHOLExact
          state.toPanSemFinite.toExact kind name value = false := by
        cases h : isValidValueHOLExact
            state.toPanSemFinite.toExact kind name value <;> simp_all
      simp only [hinvalid] at hcanonical
      exact hfinish bodyPost
        (by simpa using congrArg Prod.snd hcanonical) hbodyFields
  · simp only [hexception, hinfo] at hcanonical
    let empty := PanSemStateFiniteExact.emptyLocalsHOLFinite bodyPost
    have hemptyFields :
        empty.memaddrs = state.toPanSemFinite.memaddrs ∧
        empty.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
        empty.be = state.toPanSemFinite.be ∧
        empty.eshapes = state.toPanSemFinite.eshapes ∧
        empty.baseAddr = state.toPanSemFinite.baseAddr ∧
        empty.structs = state.toPanSemFinite.structs ∧
        empty.code = state.toPanSemFinite.code ∧
        empty.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
      simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hbodyFields
    exact hfinish empty
      (by simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using
        congrArg Prod.snd hcanonical) hemptyFields
  · simp only [hexception, hinfo] at hcanonical
    let empty := PanSemStateFiniteExact.emptyLocalsHOLFinite bodyPost
    have hemptyFields :
        empty.memaddrs = state.toPanSemFinite.memaddrs ∧
        empty.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
        empty.be = state.toPanSemFinite.be ∧
        empty.eshapes = state.toPanSemFinite.eshapes ∧
        empty.baseAddr = state.toPanSemFinite.baseAddr ∧
        empty.structs = state.toPanSemFinite.structs ∧
        empty.code = state.toPanSemFinite.code ∧
        empty.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
      simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hbodyFields
    exact hfinish empty
      (by simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using
        congrArg Prod.snd hcanonical) hemptyFields
  · simp only [hexception, hinfo, if_neg hne] at hcanonical
    let empty := PanSemStateFiniteExact.emptyLocalsHOLFinite bodyPost
    have hemptyFields :
        empty.memaddrs = state.toPanSemFinite.memaddrs ∧
        empty.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
        empty.be = state.toPanSemFinite.be ∧
        empty.eshapes = state.toPanSemFinite.eshapes ∧
        empty.baseAddr = state.toPanSemFinite.baseAddr ∧
        empty.structs = state.toPanSemFinite.structs ∧
        empty.code = state.toPanSemFinite.code ∧
        empty.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
      simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hbodyFields
    exact hfinish empty
      (by simpa [empty, PanSemStateFiniteExact.emptyLocalsHOLFinite] using
        congrArg Prod.snd hcanonical) hemptyFields
  · simp only [hexception, hinfo, if_pos heq, hshapeNone] at hcanonical
    exact hfinish bodyPost (by simpa using congrArg Prod.snd hcanonical) hbodyFields
  · simp only [hexception, hinfo, if_pos heq, hshapeSome, hcondFalse] at hcanonical
    exact hfinish bodyPost (by simpa using congrArg Prod.snd hcanonical) hbodyFields
  · have hshapeEq : shapeEqHOL (shapeOfHOLExact value) declaredShape = true :=
      (Bool.and_eq_true_iff.mp hcondTrue).1
    have hvalid : isValidValueHOLExact state.toPanSemFinite.toExact
        VarKind.local handlerVar value = true := (Bool.and_eq_true_iff.mp hcondTrue).2
    have hshapeSome' : state.toPanSemFinite.eshapes.lookup handlerId = some declaredShape := by
      simpa [heq] using hshapeSome
    rw [hexception, heq] at hcanonical
    simp [hinfo, hshapeSome', hshapeEq, hvalid] at hcanonical
    let handlerState := PanSemStateFiniteExact.setVarHOLFinite handlerVar value
      { bodyPost with locals := state.toPanSemFinite.locals }
    let handlerStateProps := PanPropsEvalStateFiniteExact.ofPanSemFinite handlerState
    let handlerRun := PanSemStateFiniteExact.evaluateHOLFiniteState handlerState handlerProgram
    let handlerPostProps := PanPropsEvalStateFiniteExact.ofPanSemFinite handlerRun.2
    have hhandlerPair :
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair handlerStateProps handlerProgram =
          (handlerRun.1, handlerPostProps) := by
      simp [handlerStateProps, handlerPostProps, handlerRun,
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.ofPanSemFinite,
        PanPropsEvalStateFiniteExact.toPanSemFinite]
    have hshapeSource : shapeOfHOLExact value = declaredShape :=
      (shapeEqHOL_eq_true (shapeOfHOLExact value) declaredShape).mp hshapeEq
    have hhandlerInvAt := ihHandler values (body, (callee, returnShape)) body
      (callee, returnShape) callee returnShape (bodyResult, bodyPost) bodyResult bodyPost
      (.exception exceptionId value) exceptionId value
      (returnInfo, some (handlerId, handlerVar, handlerProgram)) returnInfo
      (some (handlerId, handlerVar, handlerProgram))
      (handlerId, handlerVar, handlerProgram) handlerId
      (handlerVar, handlerProgram) handlerVar handlerProgram declaredShape
      hargsMapM hlookup rfl rfl hclock hbody.symm rfl hexception rfl hinfo
      rfl rfl rfl rfl heq hshapeSome hshapeSource hvalid
    have hhandlerInv := hhandlerInvAt handlerRun.1 handlerPostProps hhandlerPair
    have hhandlerFields :
        handlerRun.2.memaddrs = state.toPanSemFinite.memaddrs ∧
        handlerRun.2.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
        handlerRun.2.be = state.toPanSemFinite.be ∧
        handlerRun.2.eshapes = state.toPanSemFinite.eshapes ∧
        handlerRun.2.baseAddr = state.toPanSemFinite.baseAddr ∧
        handlerRun.2.structs = state.toPanSemFinite.structs ∧
        handlerRun.2.code = state.toPanSemFinite.code ∧
        handlerRun.2.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
      have hstateFields :
          handlerState.memaddrs = state.toPanSemFinite.memaddrs ∧
          handlerState.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
          handlerState.be = state.toPanSemFinite.be ∧
          handlerState.eshapes = state.toPanSemFinite.eshapes ∧
          handlerState.baseAddr = state.toPanSemFinite.baseAddr ∧
          handlerState.structs = state.toPanSemFinite.structs ∧
          handlerState.code = state.toPanSemFinite.code ∧
          handlerState.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
        simpa [handlerState, PanSemStateFiniteExact.setVarHOLFinite] using hbodyFields
      have hInv' :
          handlerRun.2.memaddrs = handlerState.memaddrs ∧
          handlerRun.2.shMemaddrs = handlerState.shMemaddrs ∧
          handlerRun.2.be = handlerState.be ∧
          handlerRun.2.eshapes = handlerState.eshapes ∧
          handlerRun.2.baseAddr = handlerState.baseAddr ∧
          handlerRun.2.structs = handlerState.structs ∧
          handlerRun.2.code = handlerState.code ∧
          handlerRun.2.ffi.oracle = handlerState.ffi.oracle := by
        simpa [handlerStateProps, handlerPostProps,
          handlerState, handlerRun,
          PanPropsEvalStateFiniteExact.ofPanSemFinite,
          PanPropsEvalStateFiniteExact.toPanSemFinite] using hhandlerInv
      exact ⟨hInv'.1.trans hstateFields.1,
        hInv'.2.1.trans hstateFields.2.1,
        hInv'.2.2.1.trans hstateFields.2.2.1,
        hInv'.2.2.2.1.trans hstateFields.2.2.2.1,
        hInv'.2.2.2.2.1.trans hstateFields.2.2.2.2.1,
        hInv'.2.2.2.2.2.1.trans hstateFields.2.2.2.2.2.1,
        hInv'.2.2.2.2.2.2.1.trans hstateFields.2.2.2.2.2.2.1,
        hInv'.2.2.2.2.2.2.2.trans hstateFields.2.2.2.2.2.2.2⟩
    have hhandlerEval : handlerRun = (result, post.toPanSemFinite) := by
      simpa [handlerRun, handlerState, PanSemStateFiniteExact.setVarHOLFinite] using hcanonical
    exact hfinish handlerRun.2 (by simpa [handlerRun] using congrArg Prod.snd hhandlerEval)
      hhandlerFields



/-! # The `Call` case of HOL `evaluate_invariants`

This is the exact `Call` conjunct printed by the checked `evaluate_ind` probe
at `scripts/hol-probes/pan_sem_evaluate_ind_probe.out`: its handler IH comes
first and is guarded by the concrete callee result, nested `caltyp` shape,
matched exception, source shape equality, and value validity; its callee IH is
the separate, smaller conjunct and carries only the concrete `OPT_MMAP`,
lookup/decomposition, and nonzero-clock premises. The recursive evaluation
equations `eval_prog = evaluate ...` and `eval_prog = (v4, st)` belong to the
handler IH alone and are absent from the callee IH. The theorem keeps the
source result/post equation and all eight state-field conclusions. The
same-module state uses the reviewed finite-support maps and indexed-word
carrier qualifiers.
-/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsCallCaseHOLFinite {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
      (function : MlS) (arguments : List (ExpHOL width))
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.call info function arguments : ProgHOL width) = (result, post) →
      evaluateInvariantsCallHandlerIH info function arguments state →
      evaluateInvariantsCallCalleeIH function arguments state →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro info function arguments state result post hRun ihHandler ihBody
  let memaddrsDec : DecidablePred state.toPanSemFinite.memaddrs :=
    fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address)
  cases hargs : PanSemStateFiniteExact.evalListHOLFinite state.toPanSemFinite
      (h := memaddrsDec) arguments with
  | none =>
      exact evaluateInvariantsCallArgsFailureHOLFinite state info function arguments
        result post hargs hRun
  | some values =>
      cases hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite
          state.toPanSemFinite.code.lookup function values with
      | none =>
          exact evaluateInvariantsCallLookupFailureHOLFinite state info function arguments
            values result post hargs hlookup hRun
      | some found =>
          rcases found with ⟨body, callee, returnShape⟩
          by_cases hclockZero : state.toPanSemFinite.clock = 0
          · exact evaluateInvariantsCallTimeoutHOLFinite state info function arguments values
              body callee returnShape result post hargs hlookup hclockZero hRun
          · have hclock : state.toPanSemFinite.clock ≠ 0 := hclockZero
            cases hbody : PanSemStateFiniteExact.evaluateHOLFiniteState
                (PanSemStateFiniteExact.callEntryStateHOLFinite state.toPanSemFinite callee) body with
            | mk bodyResult bodyPost =>
                have hbodyKind := evaluateInvariantsCallBodyClassification_complete
                  state info returnShape bodyResult
                have hbodyKind' : bodyResult = none ∨ bodyResult = some .break ∨
                    bodyResult = some .continue ∨ bodyResult = some .error ∨
                    bodyResult = some .timeOut ∨
                    (∃ event, bodyResult = some (.finalFfi event)) ∨
                    (∃ value, bodyResult = some (.returned value) ∧
                      shapeEqHOL (shapeOfHOLExact value) returnShape = false) ∨
                    (∃ value, bodyResult = some (.returned value) ∧
                      shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧ info = none) ∨
                    (∃ value handler, bodyResult = some (.returned value) ∧
                      shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧
                      info = some (none, handler)) ∨
                    (∃ value kind name handler, bodyResult = some (.returned value) ∧
                      shapeEqHOL (shapeOfHOLExact value) returnShape = true ∧
                      info = some (some (kind, name), handler)) ∨
                    (∃ exceptionId value, bodyResult = some (.exception exceptionId value) ∧
                      info = none) ∨
                    (∃ exceptionId value returnInfo,
                      bodyResult = some (.exception exceptionId value) ∧
                      info = some (returnInfo, none)) ∨
                    (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram,
                      bodyResult = some (.exception exceptionId value) ∧
                      info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
                      exceptionId ≠ handlerId) ∨
                    (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram,
                      bodyResult = some (.exception exceptionId value) ∧
                      info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
                      exceptionId = handlerId ∧
                      state.toPanSemFinite.eshapes.lookup exceptionId = none) ∨
                    (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram declaredShape,
                      bodyResult = some (.exception exceptionId value) ∧
                      info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
                      exceptionId = handlerId ∧
                      state.toPanSemFinite.eshapes.lookup exceptionId = some declaredShape ∧
                      (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
                        isValidValueHOLExact state.toPanSemFinite.toExact VarKind.local
                          handlerVar value) = false) ∨
                    (∃ exceptionId value returnInfo handlerId handlerVar handlerProgram declaredShape,
                      bodyResult = some (.exception exceptionId value) ∧
                      info = some (returnInfo, some (handlerId, handlerVar, handlerProgram)) ∧
                      exceptionId = handlerId ∧
                      state.toPanSemFinite.eshapes.lookup exceptionId = some declaredShape ∧
                      (shapeEqHOL (shapeOfHOLExact value) declaredShape &&
                        isValidValueHOLExact state.toPanSemFinite.toExact VarKind.local
                          handlerVar value) = true) := by
                  simpa [evaluateInvariantsCallBodyClassification] using hbodyKind
                exact evaluateInvariantsCallBodyResultBranchesHOLFinite state info function
                  arguments values body callee returnShape bodyResult bodyPost result post
                  ihBody ihHandler hargs hlookup hclock hbody hbodyKind' hRun

end Flapjack

/-! # The `Skip` case of HOL `evaluate_invariants`

This genuine induction case keeps the source theorem's evaluator premise and
all eight state-field conclusions.  HOL's `Skip` clause returns the original
state, so this leaf is immediate over the reviewed finite-support carrier.
The `Dec`, `If`, `Seq`, `While`, `DecCall`, and `Call` cases have separate
exact tagged proofs, and the assembling theorem is the tagged
`evaluateInvariantsHOLFinite` below (bead `flapjack-4ac.4.61`). -/

open Flapjack.Pancake.PanLang (ProgHOL)

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsSkipCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.skip : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro state result post hRun
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_skip,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hRun
  rcases Prod.mk.inj hRun with ⟨rfl, rfl⟩
  simp

end Flapjack


/-! # The `Break` case of HOL `evaluate_invariants`

HOL evaluates `Break` to `(SOME Break, state)`. This induction leaf keeps the
source theorem's result premise and all eight field conclusions. The recursive
cases and the assembling theorem `evaluateInvariantsHOLFinite` below are
tagged (bead `flapjack-4ac.4.61`). -/

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsBreakCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.break : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro state result post hRun
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_break,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hRun
  rcases Prod.mk.inj hRun with ⟨rfl, rfl⟩
  simp

end Flapjack


/-! # The `Continue` case of HOL `evaluate_invariants`

HOL's `Continue` equation preserves the state and this genuine induction leaf
retains the source premise and all eight field conclusions. -/

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsContinueCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.continue : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro state result post hRun
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_continue,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hRun
  rcases Prod.mk.inj hRun with ⟨rfl, rfl⟩
  simp

end Flapjack


/-! # The `Annot` case of HOL `evaluate_invariants`

HOL's annotation equation returns `(NONE, state)`, so this genuine induction
leaf retains the source premise and all eight field conclusions. -/

open Flapjack.Pancake.PanLang (MlS)

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsAnnotCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (tag text : MlS)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.annot tag text : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro tag text state result post hRun
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_annot,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hRun
  rcases Prod.mk.inj hRun with ⟨rfl, rfl⟩
  simp

end Flapjack


/-! # The `Tick` case of HOL `evaluate_invariants`

HOL `Tick` changes only the clock on its positive-clock branch and clears only
locals on timeout. This induction leaf keeps the source evaluator premise and
all eight state-field conclusions. -/

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsTickCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.tick : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro state result post hRun
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_tick] at hRun
  by_cases hclock : state.toPanSemFinite.clock = 0
  · simp [hclock, PanPropsEvalStateFiniteExact.ofPanSemFinite,
      PanSemStateFiniteExact.emptyLocalsHOLFinite] at hRun
    rcases hRun with ⟨_, hpost⟩
    cases hpost
    simp [PanPropsEvalStateFiniteExact.toPanSemFinite]
  · simp [hclock, PanPropsEvalStateFiniteExact.ofPanSemFinite,
      PanSemStateFiniteExact.decClockHOLFinite] at hRun
    rcases hRun with ⟨_, hpost⟩
    cases hpost
    simp [PanPropsEvalStateFiniteExact.toPanSemFinite]

end Flapjack


/-! # The `Return` case of HOL `evaluate_invariants`

The successful Return clause clears locals but leaves all eight fields in the
source invariant unchanged; expression and size failures preserve the state. -/

open Flapjack.Pancake.PanLang (ExpHOL)

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsReturnCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (expression : ExpHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state (.return expression) =
        (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro expression state result post hRun
  cases heval : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
      expression with
  | none =>
      simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanSemStateFiniteExact.evaluateHOLFiniteState_return, heval] at hRun
      rcases hRun with ⟨_, hpost⟩
      cases hpost
      simp
  | some value =>
      by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
          state.toPanSemFinite.structs (shapeOfHOLExact value) ≤ 32
      · simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
          PanSemStateFiniteExact.evaluateHOLFiniteState_return, heval, hsize] at hRun
        rcases hRun with ⟨_, hpost⟩
        cases hpost
        simp [PanPropsEvalStateFiniteExact.ofPanSemFinite,
          PanPropsEvalStateFiniteExact.toPanSemFinite,
          PanSemStateFiniteExact.emptyLocalsHOLFinite]
      · simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
          PanSemStateFiniteExact.evaluateHOLFiniteState_return, heval, hsize] at hRun
        rcases hRun with ⟨_, hpost⟩
        cases hpost
        simp

end Flapjack


/-! # The `Assign` induction case of HOL `evaluate_invariants`

HOL `Assign` either reports Error with the input state or applies `set_kvar`.
Both keyed-variable updates affect only locals/globals, so all eight fields in
the invariant are preserved. -/

open Flapjack.Pancake.PanLang (ExpHOL MlS)

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsAssignCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (kind : VarKind) (name : MlS) (source : ExpHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.assign kind name source : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro kind name source state result post hRun
  cases heval : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
      source with
  | none =>
      simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanSemStateFiniteExact.evaluateHOLFiniteState_assign, heval] at hRun
      rcases hRun with ⟨_, rfl⟩
      simp
  | some value =>
      by_cases hvalid : Flapjack.isValidValueHOLExact
          state.toPanSemFinite.toExact kind name value = true
      · simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
          PanSemStateFiniteExact.evaluateHOLFiniteState_assign, heval, hvalid] at hRun
        rcases hRun with ⟨_, hpost⟩
        cases hpost
        cases kind <;> simp [PanPropsEvalStateFiniteExact.ofPanSemFinite,
          PanPropsEvalStateFiniteExact.toPanSemFinite,
          PanSemStateFiniteExact.setKvarHOLFinite,
          PanSemStateFiniteExact.setVarHOLFinite,
          PanSemStateFiniteExact.setGlobalHOLFinite]
      · have hinvalid : Flapjack.isValidValueHOLExact
            state.toPanSemFinite.toExact kind name value = false :=
          Bool.eq_false_iff.mpr hvalid
        simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
          PanSemStateFiniteExact.evaluateHOLFiniteState_assign, heval, hinvalid] at hRun
        rcases hRun with ⟨_, rfl⟩
        simp

end Flapjack


/-! # The `Primitive` induction case of HOL `evaluate_invariants`

HOL `Primitive` either reports Error with the input state or writes its result
to locals. Since the invariant fields exclude locals, each outcome preserves
all eight fields. -/

open Flapjack.Pancake.PanLang (MlS ProgHOL)

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsPrimitiveCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (name : MlS) (operator : PrimOp) (arguments : List (ExpHOL width))
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.primitive name operator arguments : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro name operator arguments state result post hRun
  cases heval : @evalListHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
      arguments with
  | none =>
      simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanSemStateFiniteExact.evaluateHOLFiniteState_primitive, heval] at hRun
      rcases hRun with ⟨_, rfl⟩
      simp
  | some values =>
      cases hprim : panPrimopHOLExact operator values with
      | none =>
          simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
            PanSemStateFiniteExact.evaluateHOLFiniteState_primitive, heval, hprim] at hRun
          rcases hRun with ⟨_, rfl⟩
          simp
      | some value =>
          by_cases hvalid : Flapjack.isValidValueHOLExact
              state.toPanSemFinite.toExact .local name value = true
          · simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
              PanSemStateFiniteExact.evaluateHOLFiniteState_primitive,
              heval, hprim, hvalid] at hRun
            rcases hRun with ⟨_, hpost⟩
            cases hpost
            simp [PanPropsEvalStateFiniteExact.ofPanSemFinite,
              PanPropsEvalStateFiniteExact.toPanSemFinite,
              PanSemStateFiniteExact.setVarHOLFinite]
          · have hinvalid : Flapjack.isValidValueHOLExact
                state.toPanSemFinite.toExact .local name value = false :=
              Bool.eq_false_iff.mpr hvalid
            simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
              PanSemStateFiniteExact.evaluateHOLFiniteState_primitive,
              heval, hprim, hinvalid] at hRun
            rcases hRun with ⟨_, rfl⟩
            simp

end Flapjack


/-! # The `ExtCall` case of HOL `evaluate_invariants`

HOL `evaluate_def`'s `ExtCall` clause (`panSemScript.sml:711-726`) evaluates its
four argument expressions in order, reads the two byte arrays, dispatches
`call_FFI`, and either returns `FinalFFI` with the locals cleared or writes the
returned bytes back into memory and installs the new FFI state. This genuine
induction leaf has no recursive sub-evaluation, so HOL `evaluate_ind` gives it
no induction hypothesis and no premise beyond the evaluator run itself. This
theorem keeps that exact run premise and all eight state-field conclusions.

Source review: HOL's only state updates are `empty_locals s` (which rewrites
`locals` alone) on the `FFI_final` branch and
`<| memory := nmem; ffi := new_ffi |>` on the `FFI_return` branch. The cleared
locals branch leaves all eight fields untouched; the returned branch changes
only `memory` and `ffi`, and a returned `call_FFI` state carries the original
`oracle` field, so `ffi.oracle` is preserved. Consequently none of `memaddrs`,
`shMemaddrs`, `be`, `eshapes`, `baseAddr`, `structs`, `code`, or `ffi.oracle`
changes. The `fmap_as_finite_support` qualifier records the reviewed
`HolFiniteMapExact` carrier for the four map fields and
`words_as_type_indexed_bitvec` records the positive indexed-`BitVec` word
translation; no evaluator shortcut, extra hypothesis, or changed conclusion is
introduced. -/

open Flapjack.Pancake.PanLang (MlS ExpHOL ProgHOL)

namespace Flapjack

/-- Flapjack-only helper: a finite `callFFIHOL` returned result preserves the
    FFI `oracle`. HOL has no standalone declaration for this projection; it is
    the FFI-state field read used by the `ExtCall` invariant leaf. Untagged
    infrastructure. -/
theorem callFFIHOL_ret_oracle {σ : Type} (state : HolFfiState σ)
    (name : HolFfiName) (configuration bytes : List (BitVec 8))
    (nextState : HolFfiState σ) (nextBytes : List (BitVec 8))
    (h : callFFIHOL state name configuration bytes = .ret nextState nextBytes) :
    nextState.oracle = state.oracle := by
  unfold callFFIHOL at h
  split at h
  · simp only [HolFfiResult.ret.injEq] at h
    rw [← h.1]
  · split at h
    · split at h
      · simp only [HolFfiResult.ret.injEq] at h
        rw [← h.1]
      · simp at h
    · simp at h

/-- Flapjack-only helper: the eight `evaluate_invariants` state fields are
    preserved by the canonical finite-support `ExtCall` clause. This is the
    field-level core of the tagged `ExtCall` case; it is stated on the canonical
    carrier so the tagged theorem can transport it through the PanProps codec.
    Untagged infrastructure. -/
theorem extCallStepFieldsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (function : MlS)
    (configuration configurationLength array arrayLength : ExpHOL width) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).2.memaddrs =
      state.memaddrs ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).2.shMemaddrs =
      state.shMemaddrs ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).2.be =
      state.be ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).2.eshapes =
      state.eshapes ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).2.baseAddr =
      state.baseAddr ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).2.structs =
      state.structs ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).2.code =
      state.code ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState state
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).2.ffi.oracle =
      state.ffi.oracle := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [PanSemStateFiniteExact.evaluateHOLFiniteState_extCall_source]
  all_goals
    split
    · split
      · rename_i bytes1 bytes2 hread1 hread2
        cases hcall : callFFIHOL state.ffi (.extCall function) bytes1 bytes2 with
        | final event => simp [PanSemStateFiniteExact.emptyLocalsHOLFinite]
        | ret newFfi newBytes =>
            have horacle := callFFIHOL_ret_oracle state.ffi (.extCall function)
              bytes1 bytes2 newFfi newBytes hcall
            simp [PanSemStateFiniteExact.ofExact, horacle]
      · simp
    · simp

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsExtCallCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (function : MlS) (configuration configurationLength array arrayLength : ExpHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.extCall function configuration configurationLength array arrayLength : ProgHOL width) =
        (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro function configuration configurationLength array arrayLength state result post hRun
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.extCall function configuration configurationLength array arrayLength : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).1 =
            result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).2 =
            post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  have hpost : post.toPanSemFinite =
      (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
        (.extCall function configuration configurationLength array arrayLength : ProgHOL width)).2 :=
    (Prod.mk.inj hcanonical).2.symm
  have hfields := extCallStepFieldsHOLFinite state.toPanSemFinite function
    configuration configurationLength array arrayLength
  rw [← hpost] at hfields
  simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hfields

end Flapjack


/-! # The `Raise` induction case of HOL `evaluate_invariants`

HOL `Raise` either returns Error with the input state or clears only locals
when producing an exception, preserving all eight invariant fields. -/

open Flapjack.Pancake.PanLang (ExpHOL MlS ProgHOL)

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsRaiseCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (exceptionId : MlS) (expression : ExpHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.raise exceptionId expression : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro exceptionId expression state result post hRun
  cases hshape : state.toPanSemFinite.eshapes.lookup exceptionId with
  | none =>
      cases heval : @evalHOLExact width σ _ state.toPanSemFinite.toExact
          (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
          expression <;>
        simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
          PanSemStateFiniteExact.evaluateHOLFiniteState_raise, hshape, heval] at hRun <;>
        rcases hRun with ⟨_, rfl⟩ <;> simp
  | some shape =>
      cases heval : @evalHOLExact width σ _ state.toPanSemFinite.toExact
          (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
          expression with
      | none =>
          simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
            PanSemStateFiniteExact.evaluateHOLFiniteState_raise, hshape, heval] at hRun
          rcases hRun with ⟨_, rfl⟩
          simp
      | some value =>
          by_cases heq : shapeOfHOLExact value = shape
          · by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
                state.toPanSemFinite.structs (shapeOfHOLExact value) ≤ 32
            · have hsizeShape : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
                  state.toPanSemFinite.structs shape ≤ 32 := by
                simpa [heq] using hsize
              simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
                PanSemStateFiniteExact.evaluateHOLFiniteState_raise,
                hshape, heval, heq, hsizeShape] at hRun
              rcases hRun with ⟨_, hpost⟩
              cases hpost
              simp [PanPropsEvalStateFiniteExact.ofPanSemFinite,
                PanPropsEvalStateFiniteExact.toPanSemFinite,
                PanSemStateFiniteExact.emptyLocalsHOLFinite]
            · have hnotSize : ¬ Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
                  state.toPanSemFinite.structs shape ≤ 32 := by
                simpa [heq] using hsize
              simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
                PanSemStateFiniteExact.evaluateHOLFiniteState_raise,
                hshape, heval, heq, hnotSize] at hRun
              rcases hRun with ⟨_, rfl⟩
              simp
          · simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
              PanSemStateFiniteExact.evaluateHOLFiniteState_raise,
              hshape, heval, heq] at hRun
            rcases hRun with ⟨_, rfl⟩
            simp

end Flapjack


/-! # The `Store` induction case of HOL `evaluate_invariants`

HOL `Store` can update only `memory`; on any failed evaluation or store it
returns the input state. Therefore all eight fields in the invariant are
preserved. -/

open Flapjack.Pancake.PanLang (ExpHOL ProgHOL)

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsStoreCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (destination source : ExpHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.store destination source : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro destination source state result post hRun
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.store destination source : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.store destination source : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.store destination source : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_store] at hcanonical
  have hpreserved (memory : RiscV.Word width → HolWordLab width)
      (hpost : post.toPanSemFinite = {state.toPanSemFinite with memory := memory}) :
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
    constructor
    · change post.toPanSemFinite.memaddrs = state.toPanSemFinite.memaddrs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.shMemaddrs = state.toPanSemFinite.shMemaddrs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.be = state.toPanSemFinite.be
      rw [hpost]
    constructor
    · change post.toPanSemFinite.eshapes = state.toPanSemFinite.eshapes
      rw [hpost]
    constructor
    · change post.toPanSemFinite.baseAddr = state.toPanSemFinite.baseAddr
      rw [hpost]
    constructor
    · change post.toPanSemFinite.structs = state.toPanSemFinite.structs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.code = state.toPanSemFinite.code
      rw [hpost]
    · change post.toPanSemFinite.ffi.oracle = state.toPanSemFinite.ffi.oracle
      rw [hpost]
  -- The canonical clause has three possible evaluation failures and a
  -- successful memory update; split those HOL cases without weakening the
  -- source evaluator premise.
  cases hdestination : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
      destination with
  | none =>
      simp [hdestination] at hcanonical
      rcases hcanonical with ⟨_, hpost⟩
      exact hpreserved state.memory hpost.symm
  | some destinationValue =>
      cases destinationValue with
      | val destinationPayload =>
          cases destinationPayload with
          | word address =>
              cases hsource : @evalHOLExact width σ _ state.toPanSemFinite.toExact
                  (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
                  source with
              | none =>
                  simp [hdestination, hsource] at hcanonical
                  rcases hcanonical with ⟨_, hpost⟩
                  exact hpreserved state.memory hpost.symm
              | some value =>
                  cases hstore : @panMemStoresHOL width _ address (flattenHOL value)
                      state.toPanSemFinite.memaddrs
                      (fun address => Classical.propDecidable
                        (state.toPanSemFinite.memaddrs address)) state.toPanSemFinite.memory with
                  | none =>
                      simp [hdestination, hsource, hstore] at hcanonical
                      rcases hcanonical with ⟨_, hpost⟩
                      exact hpreserved state.memory hpost.symm
                  | some memory =>
                      simp [hdestination, hsource, hstore] at hcanonical
                      rcases hcanonical with ⟨_, hpost⟩
                      exact hpreserved memory hpost.symm
      | rStruct _ | nStruct _ _ =>
          simp [hdestination] at hcanonical
          rcases hcanonical with ⟨_, hpost⟩
          exact hpreserved state.memory hpost.symm

end Flapjack


/-! # The `Store32` induction case of HOL `evaluate_invariants`

The `Store32` clause requires word values for both expressions and changes only
memory on success; every error path returns the input state. -/

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsStore32CaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (destination source : ExpHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.store32 destination source : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro destination source state result post hRun
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.store32 destination source : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.store32 destination source : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.store32 destination source : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_store32] at hcanonical
  have hpreserved (memory : RiscV.Word width → HolWordLab width)
      (hpost : post.toPanSemFinite = {state.toPanSemFinite with memory := memory}) :
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
    constructor
    · change post.toPanSemFinite.memaddrs = state.toPanSemFinite.memaddrs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.shMemaddrs = state.toPanSemFinite.shMemaddrs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.be = state.toPanSemFinite.be
      rw [hpost]
    constructor
    · change post.toPanSemFinite.eshapes = state.toPanSemFinite.eshapes
      rw [hpost]
    constructor
    · change post.toPanSemFinite.baseAddr = state.toPanSemFinite.baseAddr
      rw [hpost]
    constructor
    · change post.toPanSemFinite.structs = state.toPanSemFinite.structs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.code = state.toPanSemFinite.code
      rw [hpost]
    · change post.toPanSemFinite.ffi.oracle = state.toPanSemFinite.ffi.oracle
      rw [hpost]
  cases hdestination : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
      destination with
  | none =>
      simp [hdestination] at hcanonical
      rcases hcanonical with ⟨_, hpost⟩
      exact hpreserved state.memory hpost.symm
  | some destinationValue =>
      cases destinationValue with
      | val destinationPayload =>
          cases destinationPayload with
          | word address =>
              cases hsource : @evalHOLExact width σ _ state.toPanSemFinite.toExact
                  (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
                  source with
              | none =>
                  simp [hdestination, hsource] at hcanonical
                  rcases hcanonical with ⟨_, hpost⟩
                  exact hpreserved state.memory hpost.symm
              | some sourceValue =>
                  cases sourceValue with
                  | val sourcePayload =>
                      cases sourcePayload with
                      | word value =>
                          cases hstore : @panMemStore32HOL width _ state.toPanSemFinite.memory
                              state.toPanSemFinite.memaddrs
                              (fun address => Classical.propDecidable
                                (state.toPanSemFinite.memaddrs address))
                              state.toPanSemFinite.be address (BitVec.setWidth 32 value) with
                          | none =>
                              simp [hdestination, hsource, hstore] at hcanonical
                              rcases hcanonical with ⟨_, hpost⟩
                              exact hpreserved state.memory hpost.symm
                          | some memory =>
                              simp [hdestination, hsource, hstore] at hcanonical
                              rcases hcanonical with ⟨_, hpost⟩
                              exact hpreserved memory hpost.symm
                  | rStruct _ | nStruct _ _ =>
                      simp [hdestination, hsource] at hcanonical
                      rcases hcanonical with ⟨_, hpost⟩
                      exact hpreserved state.memory hpost.symm
      | rStruct _ | nStruct _ _ =>
          simp [hdestination] at hcanonical
          rcases hcanonical with ⟨_, hpost⟩
          exact hpreserved state.memory hpost.symm

end Flapjack


/-! # The `StoreByte` induction case of HOL `evaluate_invariants`

The byte-store clause has the same state footprint as `Store32`; HOL converts
the source word to a byte before updating memory. -/

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsStoreByteCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (destination source : ExpHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.storeByte destination source : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro destination source state result post hRun
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.storeByte destination source : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.storeByte destination source : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.storeByte destination source : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_storeByte] at hcanonical
  have hpreserved (memory : RiscV.Word width → HolWordLab width)
      (hpost : post.toPanSemFinite = {state.toPanSemFinite with memory := memory}) :
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
    constructor
    · change post.toPanSemFinite.memaddrs = state.toPanSemFinite.memaddrs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.shMemaddrs = state.toPanSemFinite.shMemaddrs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.be = state.toPanSemFinite.be
      rw [hpost]
    constructor
    · change post.toPanSemFinite.eshapes = state.toPanSemFinite.eshapes
      rw [hpost]
    constructor
    · change post.toPanSemFinite.baseAddr = state.toPanSemFinite.baseAddr
      rw [hpost]
    constructor
    · change post.toPanSemFinite.structs = state.toPanSemFinite.structs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.code = state.toPanSemFinite.code
      rw [hpost]
    · change post.toPanSemFinite.ffi.oracle = state.toPanSemFinite.ffi.oracle
      rw [hpost]
  cases hdestination : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
      destination with
  | none =>
      simp [hdestination] at hcanonical
      rcases hcanonical with ⟨_, hpost⟩
      exact hpreserved state.memory hpost.symm
  | some destinationValue =>
      cases destinationValue with
      | val destinationPayload =>
          cases destinationPayload with
          | word address =>
              cases hsource : @evalHOLExact width σ _ state.toPanSemFinite.toExact
                  (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
                  source with
              | none =>
                  simp [hdestination, hsource] at hcanonical
                  rcases hcanonical with ⟨_, hpost⟩
                  exact hpreserved state.memory hpost.symm
              | some sourceValue =>
                  cases sourceValue with
                  | val sourcePayload =>
                      cases sourcePayload with
                      | word value =>
                          cases hstore : @panMemStoreByteWord8HOL width _
                              state.toPanSemFinite.memory state.toPanSemFinite.memaddrs
                              (fun address => Classical.propDecidable
                                (state.toPanSemFinite.memaddrs address))
                              state.toPanSemFinite.be address (BitVec.setWidth 8 value) with
                          | none =>
                              simp [hdestination, hsource, hstore] at hcanonical
                              rcases hcanonical with ⟨_, hpost⟩
                              exact hpreserved state.memory hpost.symm
                          | some memory =>
                              simp [hdestination, hsource, hstore] at hcanonical
                              rcases hcanonical with ⟨_, hpost⟩
                              exact hpreserved memory hpost.symm
                  | rStruct _ | nStruct _ _ =>
                      simp [hdestination, hsource] at hcanonical
                      rcases hcanonical with ⟨_, hpost⟩
                      exact hpreserved state.memory hpost.symm
      | rStruct _ | nStruct _ _ =>
          simp [hdestination] at hcanonical
          rcases hcanonical with ⟨_, hpost⟩
          exact hpreserved state.memory hpost.symm

end Flapjack


/-! # The `If` induction case of HOL `evaluate_invariants`

The `If` conjunct of HOL `evaluate_ind` has a single induction hypothesis,
guarded by the condition evaluation, over the conditional program
`if w ≠ 0 then c1 else c2` at the input state; it is not split into two branch
hypotheses. The condition is evaluated once: a word selects the then branch for
nonzero and the else branch for zero, and every other value yields `Error` and
preserves the input state. The exact `evaluate_def` zero test is the swapped
`word = 0` form, so the branch run is transferred to HOL's
`if w ≠ 0 then c1 else c2`. -/

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsIfCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.ite condition thenBranch elseBranch : ProgHOL width) = (result, post) →
      (∀ (v1 : ValueHOL width) (v6 : HolWordLab width) (w : BitVec width),
        @evalHOLExact width σ _ state.toPanSemFinite.toExact
            (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
            condition = some v1 ∧
          v1 = .val v6 ∧ v6 = .word w →
        ∀ (branchResult : Option (PanSemResultExact width))
          (branchPost : PanPropsEvalStateFiniteExact width σ),
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
              (if w ≠ 0 then thenBranch else elseBranch : ProgHOL width) =
            (branchResult, branchPost) →
          branchPost.memaddrs = state.memaddrs ∧
          branchPost.shMemaddrs = state.shMemaddrs ∧
          branchPost.be = state.be ∧
          branchPost.eshapes = state.eshapes ∧
          branchPost.baseAddr = state.baseAddr ∧
          branchPost.structs = state.structs ∧
          branchPost.code = state.code ∧
          branchPost.ffi.oracle = state.ffi.oracle) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro condition thenBranch elseBranch state result post hRun ihIf
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.ite condition thenBranch elseBranch : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.ite condition thenBranch elseBranch : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.ite condition thenBranch elseBranch : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  have hpreserved (hpost : post.toPanSemFinite = state.toPanSemFinite) :
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
    constructor
    · change post.toPanSemFinite.memaddrs = state.toPanSemFinite.memaddrs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.shMemaddrs = state.toPanSemFinite.shMemaddrs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.be = state.toPanSemFinite.be
      rw [hpost]
    constructor
    · change post.toPanSemFinite.eshapes = state.toPanSemFinite.eshapes
      rw [hpost]
    constructor
    · change post.toPanSemFinite.baseAddr = state.toPanSemFinite.baseAddr
      rw [hpost]
    constructor
    · change post.toPanSemFinite.structs = state.toPanSemFinite.structs
      rw [hpost]
    constructor
    · change post.toPanSemFinite.code = state.toPanSemFinite.code
      rw [hpost]
    · change post.toPanSemFinite.ffi.oracle = state.toPanSemFinite.ffi.oracle
      rw [hpost]
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_ite] at hcanonical
  cases heval : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
      condition with
  | none =>
      simp [heval] at hcanonical
      rcases hcanonical with ⟨_, hpost⟩
      exact hpreserved hpost.symm
  | some value =>
      cases value with
      | val payload =>
          cases payload with
          | word word =>
              have hbranchSem :
                  PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
                      (if word ≠ 0 then thenBranch else elseBranch : ProgHOL width) =
                    (result, post.toPanSemFinite) := by
                by_cases hzero : word = 0
                · have hne : ¬ (word ≠ 0) := by simp [hzero]
                  simp only [heval] at hcanonical
                  rw [if_pos hzero] at hcanonical
                  rw [if_neg hne]
                  exact hcanonical
                · simp only [heval] at hcanonical
                  rw [if_neg hzero] at hcanonical
                  rw [if_pos hzero]
                  exact hcanonical
              have hbranchPair :
                  PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
                      (if word ≠ 0 then thenBranch else elseBranch : ProgHOL width) =
                    (result, post) := by
                have hbranch := congrArg
                  (fun output =>
                    (output.1, PanPropsEvalStateFiniteExact.ofPanSemFinite output.2))
                  hbranchSem
                simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hbranch
              exact ihIf (.val (.word word)) (.word word) word ⟨heval, rfl, rfl⟩
                result post hbranchPair
      | rStruct _ | nStruct _ _ =>
          simp [heval] at hcanonical
          rcases hcanonical with ⟨_, hpost⟩
          exact hpreserved hpost.symm

end Flapjack


/-! # The `Dec` induction case of HOL `evaluate_invariants`

HOL's generated `evaluate_ind` Dec conjunct supplies exactly one recursive
hypothesis: for every `value` with `eval s e = SOME value` and
`sh = shape_of value`, the body at `s with locals := s.locals⟨v ↦ value⟩`
preserves the state fields. This leaf takes precisely that guarded
value/shape hypothesis (the `evaluateInvariantsAtHOLFinite` predicate applied
to the `setVar`-bound state) and does not assume any stronger
arbitrary-state or clock-indexed IH. The initializer/shape failure clauses
preserve the state; on success the body hypothesis applies to the bound state,
and restoring the old local binding changes none of the eight invariant
fields. -/

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

namespace Flapjack

/-- Flapjack-specific alias spelling the single guarded recursive hypothesis of
HOL `evaluate_ind`'s Dec conjunct: for every `value` with `eval s e = SOME value`
and `sh = shape_of value`, the body preserves the state fields at the
`setVar`-bound state. Keeping this as an abbreviation means the tagged Dec leaf
names only the owning `PanPropsEvalStateFiniteExact` carrier. -/
private abbrev evaluateInvariantsDecBodyIH {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width)
    (state : PanPropsEvalStateFiniteExact width σ) (body : ProgHOL width) : Prop :=
  ∀ (value : ValueHOL width),
    @Flapjack.evalHOLExact width σ _ state.toPanSemFinite.toExact
        (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
        initializer = some value →
    shapeEqHOL shape (shapeOfHOLExact value) = true →
    evaluateInvariantsAtHOLFinite
      (PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.setVarHOLFinite name value state.toPanSemFinite))
      body

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsDecCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width)
      (body : ProgHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.dec name shape initializer body : ProgHOL width) = (result, post) →
      evaluateInvariantsDecBodyIH name shape initializer state body →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro name shape initializer body state result post hRun ihBody
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.dec name shape initializer body : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.dec name shape initializer body : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.dec name shape initializer body : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total] at hcanonical
  let hmem : DecidablePred state.toPanSemFinite.memaddrs :=
    fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address)
  cases hinit : @evalHOLExact width σ _ state.toPanSemFinite.toExact hmem initializer with
  | none =>
      simp [hinit, hmem] at hcanonical
      rcases hcanonical with ⟨_, hpost⟩
      have hstate : post = state := by
        simpa using congrArg PanPropsEvalStateFiniteExact.ofPanSemFinite hpost.symm
      subst post
      simp
  | some value =>
      by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value) = true
      · let bodyState := PanSemStateFiniteExact.setVarHOLFinite name value state.toPanSemFinite
        let bodyStateProps := PanPropsEvalStateFiniteExact.ofPanSemFinite bodyState
        let bodyOutput := PanSemStateFiniteExact.evaluateHOLFiniteState bodyState body
        let bodyPostProps := PanPropsEvalStateFiniteExact.ofPanSemFinite bodyOutput.2
        have hbodyRun :
            PanPropsEvalStateFiniteExact.evaluateHOLFinitePair bodyStateProps body =
              (bodyOutput.1, bodyPostProps) := by
          simp [bodyStateProps, bodyPostProps, bodyOutput,
            PanPropsEvalStateFiniteExact.evaluateHOLFinitePair]
        have hbodyIH := ihBody value hinit hshape
        have hbody := hbodyIH bodyOutput.1 bodyPostProps hbodyRun
        have hbody' :
            bodyOutput.2.memaddrs = state.toPanSemFinite.memaddrs ∧
            bodyOutput.2.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
            bodyOutput.2.be = state.toPanSemFinite.be ∧
            bodyOutput.2.eshapes = state.toPanSemFinite.eshapes ∧
            bodyOutput.2.baseAddr = state.toPanSemFinite.baseAddr ∧
            bodyOutput.2.structs = state.toPanSemFinite.structs ∧
            bodyOutput.2.code = state.toPanSemFinite.code ∧
            bodyOutput.2.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
          simpa [bodyStateProps, bodyPostProps, bodyState,
            PanPropsEvalStateFiniteExact.ofPanSemFinite,
            PanSemStateFiniteExact.setVarHOLFinite] using hbody
        let restored : PanSemStateFiniteExact width σ :=
          { bodyOutput.2 with locals :=
              (HolFiniteMapExact.resVarEq bodyOutput.2.locals
                (name, state.toPanSemFinite.locals.lookup name)) }
        have hpostRaw := congrArg Prod.snd hcanonical
        simp only [hinit, if_pos hshape] at hpostRaw
        have hpost : post.toPanSemFinite = restored := by
          simpa [restored, bodyState, bodyOutput,
            PanSemStateFiniteExact.setVarHOLFinite] using hpostRaw.symm
        rcases hbody' with ⟨hmem', hshared', hbe', heshapes', hbase', hstructs', hcode', horacle'⟩
        constructor
        · change post.toPanSemFinite.memaddrs = state.toPanSemFinite.memaddrs
          rw [hpost]
          simpa [restored] using hmem'
        constructor
        · change post.toPanSemFinite.shMemaddrs = state.toPanSemFinite.shMemaddrs
          rw [hpost]
          simpa [restored] using hshared'
        constructor
        · change post.toPanSemFinite.be = state.toPanSemFinite.be
          rw [hpost]
          simpa [restored] using hbe'
        constructor
        · change post.toPanSemFinite.eshapes = state.toPanSemFinite.eshapes
          rw [hpost]
          simpa [restored] using heshapes'
        constructor
        · change post.toPanSemFinite.baseAddr = state.toPanSemFinite.baseAddr
          rw [hpost]
          simpa [restored] using hbase'
        constructor
        · change post.toPanSemFinite.structs = state.toPanSemFinite.structs
          rw [hpost]
          simpa [restored] using hstructs'
        constructor
        · change post.toPanSemFinite.code = state.toPanSemFinite.code
          rw [hpost]
          simpa [restored] using hcode'
        · change post.toPanSemFinite.ffi.oracle = state.toPanSemFinite.ffi.oracle
          rw [hpost]
          simpa [restored] using horacle'
      · have hpostRaw := congrArg Prod.snd hcanonical
        simp only [hinit, if_neg hshape] at hpostRaw
        have hstate : post = state := by
          simpa using congrArg PanPropsEvalStateFiniteExact.ofPanSemFinite hpostRaw.symm
        subst post
        simp

end Flapjack


/-! # The `Seq` induction case of HOL `evaluate_invariants`

This case uses the exact generated `evaluate_ind` Seq conjunct: its first IH
is `P (first, state)`, and its second IH is available only for a run of
`first` returning `NONE`, at that run's post-state. The line-780 evaluator
rewrites `fix_clock_evaluate`, so the second command runs at that same
post-state. -/

namespace Flapjack

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsSeqCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (first second : ProgHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.seq first second : ProgHOL width) = (result, post) →
      (∀ (firstResult : Option (PanSemResultExact width))
        (firstPost : PanPropsEvalStateFiniteExact width σ),
        (firstResult, firstPost) =
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state first ∧
        firstResult = none →
        ∀ (secondResult : Option (PanSemResultExact width))
          (secondPost : PanPropsEvalStateFiniteExact width σ),
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair firstPost second =
            (secondResult, secondPost) →
          secondPost.memaddrs = firstPost.memaddrs ∧
          secondPost.shMemaddrs = firstPost.shMemaddrs ∧
          secondPost.be = firstPost.be ∧
          secondPost.eshapes = firstPost.eshapes ∧
          secondPost.baseAddr = firstPost.baseAddr ∧
          secondPost.structs = firstPost.structs ∧
          secondPost.code = firstPost.code ∧
          secondPost.ffi.oracle = firstPost.ffi.oracle) →
      (∀ (firstResult : Option (PanSemResultExact width))
        (firstPost : PanPropsEvalStateFiniteExact width σ),
        (firstResult, firstPost) =
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state first →
        firstPost.memaddrs = state.memaddrs ∧
        firstPost.shMemaddrs = state.shMemaddrs ∧
        firstPost.be = state.be ∧
        firstPost.eshapes = state.eshapes ∧
        firstPost.baseAddr = state.baseAddr ∧
        firstPost.structs = state.structs ∧
        firstPost.code = state.code ∧
        firstPost.ffi.oracle = state.ffi.oracle) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro first second state result post hRun ihSecond ihFirst
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.seq first second : ProgHOL width) = (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.seq first second : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.seq first second : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  rw [evaluateHOLFiniteState_seq_line780] at hcanonical
  let firstOutput := PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite first
  have hfirstRun :
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state first =
        (firstOutput.1, PanPropsEvalStateFiniteExact.ofPanSemFinite firstOutput.2) := by
    simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, firstOutput]
  have hfirst := ihFirst firstOutput.1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite firstOutput.2) hfirstRun.symm
  have hfirstFields :
      firstOutput.2.memaddrs = state.toPanSemFinite.memaddrs ∧
      firstOutput.2.shMemaddrs = state.toPanSemFinite.shMemaddrs ∧
      firstOutput.2.be = state.toPanSemFinite.be ∧
      firstOutput.2.eshapes = state.toPanSemFinite.eshapes ∧
      firstOutput.2.baseAddr = state.toPanSemFinite.baseAddr ∧
      firstOutput.2.structs = state.toPanSemFinite.structs ∧
      firstOutput.2.code = state.toPanSemFinite.code ∧
      firstOutput.2.ffi.oracle = state.toPanSemFinite.ffi.oracle := by
    simpa [PanPropsEvalStateFiniteExact.ofPanSemFinite,
      PanPropsEvalStateFiniteExact.toPanSemFinite] using hfirst
  cases hfirstResult : firstOutput.1 with
  | some result₁ =>
      have hpostRaw := congrArg Prod.snd hcanonical
      simp only [firstOutput, hfirstResult] at hpostRaw
      rcases hfirstFields with ⟨hmem, hshared, hbe, heshapes, hbase, hstructs, hcode, horacle⟩
      have hpostMem := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.memaddrs) hpostRaw
      have hpostShared := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.shMemaddrs) hpostRaw
      have hpostBe := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.be) hpostRaw
      have hpostShapes := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.eshapes) hpostRaw
      have hpostBase := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.baseAddr) hpostRaw
      have hpostStructs := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.structs) hpostRaw
      have hpostCode := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.code) hpostRaw
      have hpostOracle := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.ffi.oracle) hpostRaw
      simp only [PanPropsEvalStateFiniteExact.toPanSemFinite] at hpostMem hpostShared hpostBe hpostShapes hpostBase hpostStructs hpostCode hpostOracle
      constructor
      · exact hpostMem.symm.trans hmem
      constructor
      · exact hpostShared.symm.trans hshared
      constructor
      · exact hpostBe.symm.trans hbe
      constructor
      · exact hpostShapes.symm.trans heshapes
      constructor
      · exact hpostBase.symm.trans hbase
      constructor
      · exact hpostStructs.symm.trans hstructs
      constructor
      · exact hpostCode.symm.trans hcode
      · exact hpostOracle.symm.trans horacle
  | none =>
      let secondOutput := PanSemStateFiniteExact.evaluateHOLFiniteState firstOutput.2 second
      have hsecondRun :
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
              (PanPropsEvalStateFiniteExact.ofPanSemFinite firstOutput.2) second =
            (secondOutput.1, PanPropsEvalStateFiniteExact.ofPanSemFinite secondOutput.2) := by
        simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, secondOutput]
      have hsecondIH := ihSecond firstOutput.1
        (PanPropsEvalStateFiniteExact.ofPanSemFinite firstOutput.2)
        ⟨hfirstRun.symm, hfirstResult⟩
      have hsecond := hsecondIH secondOutput.1
        (PanPropsEvalStateFiniteExact.ofPanSemFinite secondOutput.2) hsecondRun
      have hsecondFields :
          secondOutput.2.memaddrs = firstOutput.2.memaddrs ∧
          secondOutput.2.shMemaddrs = firstOutput.2.shMemaddrs ∧
          secondOutput.2.be = firstOutput.2.be ∧
          secondOutput.2.eshapes = firstOutput.2.eshapes ∧
          secondOutput.2.baseAddr = firstOutput.2.baseAddr ∧
          secondOutput.2.structs = firstOutput.2.structs ∧
          secondOutput.2.code = firstOutput.2.code ∧
          secondOutput.2.ffi.oracle = firstOutput.2.ffi.oracle := by
        simpa [PanPropsEvalStateFiniteExact.ofPanSemFinite] using hsecond
      have hpostRaw := congrArg Prod.snd hcanonical
      simp only [firstOutput, hfirstResult] at hpostRaw
      rcases hfirstFields with ⟨hfirstMem, hfirstShared, hfirstBe, hfirstShapes,
        hfirstBase, hfirstStructs, hfirstCode, hfirstOracle⟩
      rcases hsecondFields with ⟨hmem, hshared, hbe, hshapes, hbase, hstructs, hcode, horacle⟩
      have hpostMem := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.memaddrs) hpostRaw
      have hpostShared := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.shMemaddrs) hpostRaw
      have hpostBe := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.be) hpostRaw
      have hpostShapes := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.eshapes) hpostRaw
      have hpostBase := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.baseAddr) hpostRaw
      have hpostStructs := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.structs) hpostRaw
      have hpostCode := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.code) hpostRaw
      have hpostOracle := congrArg
        (fun output : PanSemStateFiniteExact width σ => output.ffi.oracle) hpostRaw
      simp only [PanPropsEvalStateFiniteExact.toPanSemFinite] at hpostMem hpostShared hpostBe hpostShapes hpostBase hpostStructs hpostCode hpostOracle
      constructor
      · exact hpostMem.symm.trans (hmem.trans hfirstMem)
      constructor
      · exact hpostShared.symm.trans (hshared.trans hfirstShared)
      constructor
      · exact hpostBe.symm.trans (hbe.trans hfirstBe)
      constructor
      · exact hpostShapes.symm.trans (hshapes.trans hfirstShapes)
      constructor
      · exact hpostBase.symm.trans (hbase.trans hfirstBase)
      constructor
      · exact hpostStructs.symm.trans (hstructs.trans hfirstStructs)
      constructor
      · exact hpostCode.symm.trans (hcode.trans hfirstCode)
      · exact hpostOracle.symm.trans (horacle.trans hfirstOracle)

/-! # The `While` case of HOL `evaluate_invariants`

The HOL `evaluate_ind` While conjunct
(`scripts/hol-probes/pan_sem_evaluate_ind_probe.out`) has three IHs, each under
the guards `eval s e = SOME v2 ∧ v2 = Val v11 ∧ v11 = Word w ∧ w ≠ 0w ∧
s.clock ≠ 0`: `P (While e c, s1)` after the body at `dec_clock s` returns
`Continue`, `P (While e c, s1)` after it returns `NONE`, and `P (c, dec_clock s)`.
The case is stated with exactly those IHs at `P = evaluate_invariants`'s
conclusion. The While clause is `evaluate_def` at panSemScript.sml:630, used
through the tagged `fix_clock`-free rewrite. -/

/-- The eight `evaluate_invariants` fields of `post` against `pre`. -/
private def whileInvFields {width : Nat} {σ : Type} [NeZero width]
    (post pre : PanPropsEvalStateFiniteExact width σ) : Prop :=
  post.memaddrs = pre.memaddrs ∧ post.shMemaddrs = pre.shMemaddrs ∧ post.be = pre.be ∧
    post.eshapes = pre.eshapes ∧ post.baseAddr = pre.baseAddr ∧ post.structs = pre.structs ∧
    post.code = pre.code ∧ post.ffi.oracle = pre.ffi.oracle

private theorem whileInvFields_trans {width : Nat} {σ : Type} [NeZero width]
    {a b c : PanPropsEvalStateFiniteExact width σ} (h1 : whileInvFields a b)
    (h2 : whileInvFields b c) :
    whileInvFields a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8⟩

/-- The `While` leaf of HOL `evaluate_invariants` (`panPropsScript.sml:1150`) with
    the exact `evaluate_ind` While IHs. `eval s e` is the exact evaluator on
    `s.toPanSemFinite` with the classical address decision; `dec_clock s` is the
    record update `s with clock := s.clock - 1`, and `evaluate` is the pair
    evaluator `evaluateHOLFinitePair` over this carrier. Each IH and the
    conclusion are `P` unfolded: `∀res st. evaluate (p, t) = (res, st) ⇒` the
    eight invariant fields of `st` against `t`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsWhileCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (e : ExpHOL width) (c : ProgHOL width) (s : PanPropsEvalStateFiniteExact width σ),
      (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
          (res : Option (PanSemResultExact width)) (s1 : PanPropsEvalStateFiniteExact width σ)
          (v1 : PanSemResultExact width),
          @evalHOLExact width σ _ s.toPanSemFinite.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
            v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
            (res, s1) = PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
              { s with clock := s.clock - 1 } c ∧
            res = some v1 ∧ v1 = .continue →
          ∀ (res' : Option (PanSemResultExact width)) (st : PanPropsEvalStateFiniteExact width σ),
            PanPropsEvalStateFiniteExact.evaluateHOLFinitePair s1 (.while e c) = (res', st) →
            st.memaddrs = s1.memaddrs ∧ st.shMemaddrs = s1.shMemaddrs ∧ st.be = s1.be ∧
            st.eshapes = s1.eshapes ∧ st.baseAddr = s1.baseAddr ∧ st.structs = s1.structs ∧
            st.code = s1.code ∧ st.ffi.oracle = s1.ffi.oracle) ∧
      (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width)
          (res : Option (PanSemResultExact width)) (s1 : PanPropsEvalStateFiniteExact width σ),
          @evalHOLExact width σ _ s.toPanSemFinite.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
            v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 ∧
            (res, s1) = PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
              { s with clock := s.clock - 1 } c ∧
            res = none →
          ∀ (res' : Option (PanSemResultExact width)) (st : PanPropsEvalStateFiniteExact width σ),
            PanPropsEvalStateFiniteExact.evaluateHOLFinitePair s1 (.while e c) = (res', st) →
            st.memaddrs = s1.memaddrs ∧ st.shMemaddrs = s1.shMemaddrs ∧ st.be = s1.be ∧
            st.eshapes = s1.eshapes ∧ st.baseAddr = s1.baseAddr ∧ st.structs = s1.structs ∧
            st.code = s1.code ∧ st.ffi.oracle = s1.ffi.oracle) ∧
      (∀ (v2 : ValueHOL width) (v11 : HolWordLab width) (w : BitVec width),
          @evalHOLExact width σ _ s.toPanSemFinite.toExact
              (fun address => Classical.propDecidable (s.memaddrs address)) e = some v2 ∧
            v2 = .val v11 ∧ v11 = .word w ∧ w ≠ 0 ∧ s.clock ≠ 0 →
          ∀ (res' : Option (PanSemResultExact width)) (st : PanPropsEvalStateFiniteExact width σ),
            PanPropsEvalStateFiniteExact.evaluateHOLFinitePair { s with clock := s.clock - 1 } c =
              (res', st) →
            st.memaddrs = s.memaddrs ∧ st.shMemaddrs = s.shMemaddrs ∧ st.be = s.be ∧
            st.eshapes = s.eshapes ∧ st.baseAddr = s.baseAddr ∧ st.structs = s.structs ∧
            st.code = s.code ∧ st.ffi.oracle = s.ffi.oracle) →
      ∀ (res : Option (PanSemResultExact width)) (st : PanPropsEvalStateFiniteExact width σ),
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair s (.while e c) = (res, st) →
        st.memaddrs = s.memaddrs ∧ st.shMemaddrs = s.shMemaddrs ∧ st.be = s.be ∧
        st.eshapes = s.eshapes ∧ st.baseAddr = s.baseAddr ∧ st.structs = s.structs ∧
        st.code = s.code ∧ st.ffi.oracle = s.ffi.oracle := by
  classical
  intro e c s ⟨ihCont, ihNone, ihBody⟩ res st hRun
  change whileInvFields st s
  -- the pair evaluator is the canonical evaluator through the codec
  have hpair : ∀ (t : PanPropsEvalStateFiniteExact width σ) (p : ProgHOL width),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair t p =
        ((PanSemStateFiniteExact.evaluateHOLFiniteState t.toPanSemFinite p).1,
          PanPropsEvalStateFiniteExact.ofPanSemFinite
            (PanSemStateFiniteExact.evaluateHOLFiniteState t.toPanSemFinite p).2) := by
    intro t p; rfl
  have hdec :
      ({ s with clock := s.clock - 1 } : PanPropsEvalStateFiniteExact width σ).toPanSemFinite =
      PanSemStateFiniteExact.decClockHOLFinite s.toPanSemFinite := rfl
  have hsame : ∀ (t : PanSemStateFiniteExact width σ),
      t = s.toPanSemFinite → whileInvFields (PanPropsEvalStateFiniteExact.ofPanSemFinite t) s := by
    rintro t rfl
    simp [whileInvFields]
  rw [hpair] at hRun
  have hst := (Prod.mk.inj hRun).2.symm
  rcases hW : PanSemStateFiniteExact.evaluateHOLFiniteState s.toPanSemFinite (.while e c) with
    ⟨r, t⟩
  rw [hW] at hst
  subst hst
  have hdecFields :
    whileInvFields ({ s with clock := s.clock - 1 } : PanPropsEvalStateFiniteExact width σ) s := by
    simp [whileInvFields]
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite] at hW
  split at hW
  · rename_i w heval
    split at hW
    · rename_i hw
      split at hW
      · obtain ⟨_, rfl⟩ := Prod.mk.inj hW
        simp [whileInvFields, PanPropsEvalStateFiniteExact.ofPanSemFinite,
          PanPropsEvalStateFiniteExact.toPanSemFinite, PanSemStateFiniteExact.emptyLocalsHOLFinite]
      · rename_i hclk
        dsimp only at hW
        rcases hb : PanSemStateFiniteExact.evaluateHOLFiniteState
            (PanSemStateFiniteExact.decClockHOLFinite s.toPanSemFinite) c with ⟨br, bt⟩
        rw [hb] at hW
        have hbodyRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
            { s with clock := s.clock - 1 } c =
              (br, PanPropsEvalStateFiniteExact.ofPanSemFinite bt) := by
          rw [hpair, hdec, hb]
        have hbody : whileInvFields (PanPropsEvalStateFiniteExact.ofPanSemFinite bt) s :=
          whileInvFields_trans (ihBody _ _ w ⟨heval, rfl, rfl, hw, hclk⟩ br _ hbodyRun) hdecFields
        dsimp only at hW
        rcases br with _ | br
        · have hW' : PanSemStateFiniteExact.evaluateHOLFiniteState bt (.while e c) = (r, t) := hW
          have hloopRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
              (PanPropsEvalStateFiniteExact.ofPanSemFinite bt) (.while e c) =
              (r, PanPropsEvalStateFiniteExact.ofPanSemFinite t) := by
            rw [hpair, PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite, hW']
          exact whileInvFields_trans
            (ihNone _ _ w none _ ⟨heval, rfl, rfl, hw, hclk, hbodyRun.symm, rfl⟩
            r _ hloopRun) hbody
        · cases br with
          | «continue» =>
              have hW' :
                PanSemStateFiniteExact.evaluateHOLFiniteState bt (.while e c) = (r, t) := hW
              have hloopRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
                  (PanPropsEvalStateFiniteExact.ofPanSemFinite bt) (.while e c) =
                  (r, PanPropsEvalStateFiniteExact.ofPanSemFinite t) := by
                rw [hpair, PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite, hW']
              exact whileInvFields_trans (ihCont _ _ w _ _ .continue
                ⟨heval, rfl, rfl, hw, hclk, hbodyRun.symm, rfl, rfl⟩ r _ hloopRun) hbody
          | «break» =>
              obtain ⟨_, rfl⟩ := Prod.mk.inj hW
              exact hbody
          | error | timeOut | returned _ | exception _ _ | finalFfi _ =>
              obtain ⟨_, rfl⟩ := Prod.mk.inj hW
              exact hbody
    · obtain ⟨_, rfl⟩ := Prod.mk.inj hW
      exact hsame _ rfl
  · obtain ⟨_, rfl⟩ := Prod.mk.inj hW
    exact hsame _ rfl

end Flapjack


/-!
# The `Dec` induction case of HOL `evaluate_clock_sub`

This is a genuine recursive-induction case of `panPropsScript.sml:724` over
the exact finite-support PanProps carrier.  It keeps the source theorem's
clock/result hypotheses and adds only the induction hypothesis for the
recursive body.  The full theorem remains in `flapjack-4ac.4.60.1.1`.
-/

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

namespace Flapjack

/-- Flapjack-specific pair wrapper for the source `Seq` clause. This is not a
    separate HOL declaration: it follows from the canonical finite-state
    `evaluate_def` line-780 clause and the field-for-field PanProps/PanSem
    carrier codec. It exposes the same control flow to the clock-induction
    cases below. -/
theorem evaluateHOLFinitePair_seq {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (first second : ProgHOL width) :
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state (.seq first second) =
      (let firstOutput := PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state first
       match firstOutput.1 with
       | none => PanPropsEvalStateFiniteExact.evaluateHOLFinitePair firstOutput.2 second
       | some _ => firstOutput) := by
  classical
  unfold PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
  rw [evaluateHOLFiniteState_seq_line780]
  cases state.toPanSemFinite.evaluateHOLFiniteState first with
  | mk result post =>
      cases result <;> simp [PanPropsEvalStateFiniteExact.toPanSemFinite,
        PanPropsEvalStateFiniteExact.ofPanSemFinite]

/-- Flapjack-specific clock bound for the pair wrapper, derived from the
    canonical exact finite evaluator's clock theorem. -/
theorem evaluateHOLFinitePair_clock_le {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (program : ProgHOL width) :
    (PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state program).2.clock ≤
      state.clock := by
  have h := evaluateHOLFiniteState_clock_le state.toPanSemFinite program
  change (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite program).2.clock ≤
    state.clock
  exact h

/-- Flapjack-specific pair wrapper for the `While` clause of HOL
    `evaluate_def` (`panSemScript.sml:630`). HOL has no separate pair-wrapper
    declaration; this infrastructure exposes that exact clause through the
    PanProps finite-state codec for the recursive-induction proof. -/
theorem evaluateHOLFinitePair_while {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ) (condition : ExpHOL width)
    (body : ProgHOL width) :
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state (.while condition body) =
      (let canonical := state.toPanSemFinite
       let conditionResult := @PanSemStateFiniteExact.evalHOLFinite width σ _ canonical
         (fun address => Classical.propDecidable (canonical.memaddrs address)) condition
       let output : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ :=
         match conditionResult with
         | some (.val (.word word)) =>
             if word ≠ 0 then
               if canonical.clock = 0 then
                 (some .timeOut, PanSemStateFiniteExact.emptyLocalsHOLFinite canonical)
               else
                 let entry := PanSemStateFiniteExact.decClockHOLFinite canonical
                 let bodyOutput := PanSemStateFiniteExact.evaluateHOLFiniteState entry body
                 let fixed := PanSemStateFiniteExact.fixClockHOLFinite entry bodyOutput
                 match bodyOutput.1 with
                 | none => PanSemStateFiniteExact.evaluateHOLFiniteState fixed.2
                     (.while condition body)
                 | some .continue => PanSemStateFiniteExact.evaluateHOLFiniteState fixed.2
                     (.while condition body)
                 | some .break => (none, fixed.2)
                 | some result => (some result, fixed.2)
             else (none, canonical)
         | _ => (some .error, canonical)
       (output.1, PanPropsEvalStateFiniteExact.ofPanSemFinite output.2)) := by
  classical
  unfold PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_total]
  rfl

/-- Flapjack-specific projection of the Break branch of the exact source While
    clause (`panSemScript.sml:630`) through the PanProps pair codec. HOL has no
    separate pair-wrapper theorem. This helper only exposes that equation; it
    does not establish the `evaluate_clock_sub` induction case. -/
private theorem evaluateHOLFinitePair_while_breakOutput {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    (condition : ExpHOL width) (body : ProgHOL width) (word : BitVec width)
    (hGuard : @PanSemStateFiniteExact.evalHOLFinite width σ _ state.toPanSemFinite
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address)) condition =
      some (.val (.word word))) (hWord : word ≠ 0) (hClock : state.clock ≠ 0)
    (bodyPost : PanPropsEvalStateFiniteExact width σ)
    (hBody : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      { state with clock := state.clock - 1 } body =
        (some PanSemResultExact.break, bodyPost)) :
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state (.while condition body) =
      (none, PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.fixClockHOLFinite (width := width) (σ := σ)
          (β := Option (PanSemResultExact width))
          (PanSemStateFiniteExact.decClockHOLFinite (width := width) (σ := σ)
            state.toPanSemFinite)
          (some PanSemResultExact.break, bodyPost.toPanSemFinite)).2) := by
  classical
  letI : DecidablePred state.toPanSemFinite.memaddrs :=
    fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address)
  have hBodyResult := congrArg Prod.fst hBody
  have hBodyPost := congrArg Prod.snd hBody
  change (PanSemStateFiniteExact.evaluateHOLFiniteState
    ({ state with clock := state.clock - 1 }.toPanSemFinite) body).1 =
      some PanSemResultExact.break at hBodyResult
  change PanPropsEvalStateFiniteExact.ofPanSemFinite
    (PanSemStateFiniteExact.evaluateHOLFiniteState
      ({ state with clock := state.clock - 1 }.toPanSemFinite) body).2 = bodyPost at hBodyPost
  have hBodyPost' := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hBodyPost
  simp only [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] at hBodyPost'
  have hEntry : ({ state with clock := state.clock - 1 }.toPanSemFinite) =
      PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite := rfl
  rw [hEntry] at hBodyResult hBodyPost'
  have hBodyExact : PanSemStateFiniteExact.evaluateHOLFiniteState
      (PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite) body =
        (some PanSemResultExact.break, bodyPost.toPanSemFinite) := Prod.ext hBodyResult hBodyPost'
  rw [evaluateHOLFinitePair_while]
  dsimp only
  rw [hGuard]
  have hclock : ¬ state.toPanSemFinite.clock = 0 := by
    change state.clock ≠ 0
    exact hClock
  dsimp only
  rw [if_pos hWord, if_neg hclock]
  simp [hBodyExact]

/-- Flapjack-specific clock-subtraction identity for `dec_clock`: this is a
    finite-state arithmetic helper, not a separate HOL declaration. It
    records the `ck < clock` side condition needed to commute a lower-clock
    run's While body entry with HOL's one-tick decrement. -/
private theorem decClockHOLFinite_sub_clock {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ) (ck : Nat)
    (hck : ck < state.clock) :
    PanSemStateFiniteExact.decClockHOLFinite
        { state with clock := state.clock - ck } =
      { PanSemStateFiniteExact.decClockHOLFinite state with
        clock := (PanSemStateFiniteExact.decClockHOLFinite state).clock - ck } := by
  simp only [PanSemStateFiniteExact.decClockHOLFinite]
  congr 1
  omega

/-- Flapjack-specific clock-subtraction identity for `fix_clock`: when the
    body result clock is bounded by its entry clock, clamping after subtracting
    `ck` agrees with subtracting `ck` after the original clamp. This helper is
    derived from HOL `fix_clock_def`; HOL has no standalone subtraction lemma. -/
private theorem fixClockHOLFinite_sub_clock {width : Nat} {σ : Type} {β : Type}
    [NeZero width] (entry post : PanSemStateFiniteExact width σ)
    (result : β) (ck : Nat) (hpost : post.clock ≤ entry.clock) :
    (PanSemStateFiniteExact.fixClockHOLFinite
        { entry with clock := entry.clock - ck }
        (result, { post with clock := post.clock - ck })).2 =
      { (PanSemStateFiniteExact.fixClockHOLFinite entry (result, post)).2 with
        clock := (PanSemStateFiniteExact.fixClockHOLFinite entry (result, post)).2.clock - ck } := by
  have hhigh : ¬ entry.clock < post.clock := by omega
  have hlow : ¬ entry.clock - ck < post.clock - ck := by omega
  simp only [PanSemStateFiniteExact.fixClockHOLFinite, if_neg hhigh, if_neg hlow]

/-- Flapjack-specific bound for the exact source `While` clause. When its
    guard is a nonzero word and the body runs at the decremented entry clock,
    every resulting While state has a clock no greater than the body
    post-state clock. The recursive `NONE`/`Continue` cases use the exact
    evaluator clock bound; the terminal cases return the body post-state.
    This is proof infrastructure, not a standalone HOL
    declaration. -/
private theorem evaluateWhileOutputClock_le_bodyPost {width : Nat} {σ : Type}
    [NeZero width] (state : PanSemStateFiniteExact width σ)
    (condition : ExpHOL width) (body : ProgHOL width)
    (word : BitVec width) (hword : word ≠ 0) (hclock : state.clock ≠ 0)
    (hguard : @PanSemStateFiniteExact.evalHOLFinite width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address)) condition =
        some (.val (.word word)))
    (bodyResult : Option (PanSemResultExact width))
    (bodyPost : PanSemStateFiniteExact width σ)
    (hbody : PanSemStateFiniteExact.evaluateHOLFiniteState
      (PanSemStateFiniteExact.decClockHOLFinite state) body =
      (bodyResult, bodyPost)) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState state (.while condition body)).2.clock ≤
      bodyPost.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_fixClockRewrite]
  simp only [hguard, if_pos hword, if_neg hclock, hbody]
  cases bodyResult with
  | none =>
      exact evaluateHOLFiniteState_clock_le bodyPost (.while condition body)
  | some result =>
      cases result with
      | «continue» =>
          exact evaluateHOLFiniteState_clock_le bodyPost (.while condition body)
      | «break» | error | timeOut | returned _ | exception _ _ | finalFfi _ =>
          exact Nat.le_refl _

/-- Flapjack-specific projection of the canonical While clock bound to the
    pair-shaped PanProps evaluator. This helper has no HOL declaration. -/
private theorem evaluateWhilePairOutputClock_le_bodyPost {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    (condition : ExpHOL width) (body : ProgHOL width)
    (word : BitVec width) (hword : word ≠ 0) (hclock : state.clock ≠ 0)
    (hguard : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) condition =
        some (.val (.word word)))
    (bodyResult : Option (PanSemResultExact width))
    (bodyPost : PanPropsEvalStateFiniteExact width σ)
    (hbody : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      { state with clock := state.clock - 1 } body = (bodyResult, bodyPost)) :
    (PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
      (.while condition body)).2.clock ≤ bodyPost.clock := by
  letI : DecidablePred state.toPanSemFinite.memaddrs :=
    fun address => Classical.propDecidable (state.memaddrs address)
  have hguardFinite : state.toPanSemFinite.evalHOLFinite condition =
      some (.val (.word word)) := by
    rw [PanSemStateFiniteExact.evalHOLFinite_eq_toExact]
    exact hguard
  have hbodyCanonical : PanSemStateFiniteExact.evaluateHOLFiniteState
      (PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite) body =
        (bodyResult, bodyPost.toPanSemFinite) := by
    have hresult := congrArg Prod.fst hbody
    have hpost := congrArg Prod.snd hbody
    change (PanSemStateFiniteExact.evaluateHOLFiniteState
      ({ state with clock := state.clock - 1 }.toPanSemFinite) body).1 = bodyResult at hresult
    change PanPropsEvalStateFiniteExact.ofPanSemFinite
      (PanSemStateFiniteExact.evaluateHOLFiniteState
        ({ state with clock := state.clock - 1 }.toPanSemFinite) body).2 = bodyPost at hpost
    have hpost' := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hpost
    simp only [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] at hpost'
    have hinput : ({ state with clock := state.clock - 1 }.toPanSemFinite) =
        PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite := rfl
    rw [hinput] at hresult hpost'
    exact Prod.ext hresult hpost'
  have hbound := evaluateWhileOutputClock_le_bodyPost state.toPanSemFinite
    condition body word hword hclock hguardFinite bodyResult bodyPost.toPanSemFinite
    hbodyCanonical
  change (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
    (.while condition body)).2.clock ≤ bodyPost.clock
  simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanPropsEvalStateFiniteExact.toPanSemFinite] using hbound

/-- Flapjack-specific first-stage alignment lemma for the `While` case of HOL
    `evaluate_clock_sub`. It consumes the exact enclosing high While run, the
    high body run at `dec_clock state`, and the result-independent body IH
    generated by `evaluate_ind` (including that IH's non-timeout premise). It
    derives both clock bounds, gives the low body run with the same result and
    the body's post-state clock reduced by `ck`, and aligns the low `fix_clock`
    result with the high fixed body state clock-subtracted by `ck`. It has no
    standalone HOL declaration and therefore remains untagged. -/
private theorem evaluateClockSubWhileBodyRunAlignment {width : Nat} {σ : Type}
    [NeZero width] (condition : ExpHOL width) (body : ProgHOL width)
    (state : PanPropsEvalStateFiniteExact width σ)
    (v2 : ValueHOL width) (v11 : HolWordLab width) (word : BitVec width)
    (hguard : @evalHOLExact width σ _ state.toPanSemFinite.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) condition = some v2 ∧
      v2 = .val v11 ∧ v11 = .word word ∧ word ≠ 0 ∧ state.clock ≠ 0)
    (ihBody : ∀ (v2' : ValueHOL width) (v11' : HolWordLab width) (word' : BitVec width),
      @evalHOLExact width σ _ state.toPanSemFinite.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) condition = some v2' ∧
        v2' = .val v11' ∧ v11' = .word word' ∧ word' ≠ 0 ∧ state.clock ≠ 0 →
      ∀ (result : Option (PanSemResultExact width))
        (post : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
            { state with clock := state.clock - 1 } body =
          (result, { post with clock := post.clock + ck }) →
        result ≠ some .timeOut →
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
          { { state with clock := state.clock - 1 } with
              clock := (state.clock - 1) - ck } body = (result, post))
    (ck : Nat)
    (whileResult : Option (PanSemResultExact width))
    (whilePost : PanPropsEvalStateFiniteExact width σ)
    (hWhileRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
        (.while condition body) = (whileResult, { whilePost with clock := whilePost.clock + ck }))
    (result : Option (PanSemResultExact width))
    (bodyPost : PanPropsEvalStateFiniteExact width σ)
    (hBodyRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - 1 } body = (result, bodyPost))
    (hNotTimeout : result ≠ some .timeOut) :
    let bodyPostLow := { bodyPost with clock := bodyPost.clock - ck }
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { { state with clock := state.clock - ck } with
            clock := (state.clock - ck) - 1 } body = (result, bodyPostLow) ∧
      (PanSemStateFiniteExact.fixClockHOLFinite
          (PanSemStateFiniteExact.decClockHOLFinite
            ({ state with clock := state.clock - ck }.toPanSemFinite))
          (result, bodyPostLow.toPanSemFinite)).2 =
        { (PanSemStateFiniteExact.fixClockHOLFinite
            (PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite)
            (result, bodyPost.toPanSemFinite)).2 with
          clock := (PanSemStateFiniteExact.fixClockHOLFinite
            (PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite)
            (result, bodyPost.toPanSemFinite)).2.clock - ck } := by
  rcases hguard with ⟨hEval, hValue, hWord, hNonzero, hClock⟩
  have hGuardExact : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) condition =
        some (.val (.word word)) := by
    rw [hEval, hValue, hWord]
  have hPostClock : ck ≤ bodyPost.clock := by
    have hBound := evaluateWhilePairOutputClock_le_bodyPost state condition body word
      hNonzero hClock hGuardExact result bodyPost hBodyRun
    have hOutputClock : (PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
        (.while condition body)).2.clock = whilePost.clock + ck := by
      have h := congrArg
        (fun pair : Option (PanSemResultExact width) × PanPropsEvalStateFiniteExact width σ =>
          pair.2.clock) hWhileRun
      simpa using h
    omega
  have hBodyEntryClock : bodyPost.clock ≤ state.clock - 1 := by
    have hBound := evaluateHOLFinitePair_clock_le
      ({ state with clock := state.clock - 1 } : PanPropsEvalStateFiniteExact width σ) body
    rw [hBodyRun] at hBound
    change bodyPost.clock ≤ state.clock - 1 at hBound
    exact hBound
  have hEntryClock : ck < state.clock := by omega
  have hPostPair :
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
          { state with clock := state.clock - 1 } body =
        (result, { { bodyPost with clock := bodyPost.clock - ck } with
          clock := (bodyPost.clock - ck) + ck }) := by
    simpa [Nat.sub_add_cancel hPostClock] using hBodyRun
  have hLow := ihBody v2 v11 word
    ⟨hEval, hValue, hWord, hNonzero, hClock⟩ result
    { bodyPost with clock := bodyPost.clock - ck } ck hPostPair hNotTimeout
  have hEntrySub : (state.clock - ck) - 1 = (state.clock - 1) - ck := by omega
  have hLowRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      { { state with clock := state.clock - ck } with
          clock := (state.clock - ck) - 1 } body =
        (result, { bodyPost with clock := bodyPost.clock - ck }) := by
    simpa [hEntrySub] using hLow
  refine ⟨?_, ?_⟩
  · exact hLowRun
  · have hFixClockSub := fixClockHOLFinite_sub_clock
      (PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite)
      bodyPost.toPanSemFinite result ck (by
        simpa [PanPropsEvalStateFiniteExact.toPanSemFinite,
          PanSemStateFiniteExact.decClockHOLFinite] using hBodyEntryClock)
    have hDecClockSub := decClockHOLFinite_sub_clock state.toPanSemFinite ck hEntryClock
    have hLowEntry : PanSemStateFiniteExact.decClockHOLFinite
        ({ state with clock := state.clock - ck }.toPanSemFinite) =
          { PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite with
            clock := (PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite).clock - ck } := by
      simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hDecClockSub
    change (PanSemStateFiniteExact.fixClockHOLFinite
        (PanSemStateFiniteExact.decClockHOLFinite
          ({ state with clock := state.clock - ck }.toPanSemFinite))
        (result, ({ bodyPost with clock := bodyPost.clock - ck }).toPanSemFinite)).2 =
      { (PanSemStateFiniteExact.fixClockHOLFinite
          (PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite)
          (result, bodyPost.toPanSemFinite)).2 with
        clock := (PanSemStateFiniteExact.fixClockHOLFinite
          (PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite)
          (result, bodyPost.toPanSemFinite)).2.clock - ck }
    rw [hLowEntry]
    exact hFixClockSub

/-- Flapjack-specific state projection used by clock-sub induction: when a
    canonical PanSem post-state is the PanProps post-state with `ck` added to
    its clock, subtracting `ck` from that canonical state recovers the exact
    PanProps carrier image. This is representation bookkeeping, not a HOL
    declaration. -/
private theorem panSemFinite_subClock_eq_toPanProps
    {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    (post : PanSemStateFiniteExact width σ) (ck : Nat)
    (hPost : post = { state.toPanSemFinite with clock := state.clock + ck }) :
    { post with clock := post.clock - ck } = state.toPanSemFinite := by
  subst post
  cases state
  simp [PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega

/-- Flapjack-specific assembled Break-body branch for the While clock-sub
    proof. The condition and body equations are explicit constructor-split
    data extracted from an enclosing high run; they are not premises of HOL's
    `evaluate_clock_sub`. This helper consumes the generated body IH and the
    enclosing run to align both body and fixed clocks. It remains untagged
    until a theorem derives these split equations internally from the exact
    source run. -/
private theorem evaluateClockSubWhileBreakBodyProjection {width : Nat} {σ : Type}
    [NeZero width] (condition : ExpHOL width) (body : ProgHOL width)
    (state : PanPropsEvalStateFiniteExact width σ)
    (result : Option (PanSemResultExact width))
    (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat)
    (hWhileRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
        (.while condition body) = (result, { st with clock := st.clock + ck }))
    (hNotTimeout : result ≠ some .timeOut)
    (ihBody : ∀ (v2' : ValueHOL width) (v11' : HolWordLab width) (word' : BitVec width),
      @evalHOLExact width σ _ state.toPanSemFinite.toExact
          (fun address => Classical.propDecidable (state.memaddrs address)) condition = some v2' ∧
        v2' = .val v11' ∧ v11' = .word word' ∧ word' ≠ 0 ∧ state.clock ≠ 0 →
      ∀ (result' : Option (PanSemResultExact width))
        (post : PanPropsEvalStateFiniteExact width σ) (ck' : Nat),
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
            { state with clock := state.clock - 1 } body =
          (result', { post with clock := post.clock + ck' }) →
        result' ≠ some .timeOut →
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
          { { state with clock := state.clock - 1 } with
              clock := (state.clock - 1) - ck' } body = (result', post))
    (word : BitVec width)
    (hGuard : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) condition =
      some (.val (.word word))) (hWord : word ≠ 0) (hClock : state.clock ≠ 0)
    (bodyPost : PanPropsEvalStateFiniteExact width σ)
    (hBody : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      { state with clock := state.clock - 1 } body =
        (some .break, bodyPost)) :
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      { state with clock := state.clock - ck } (.while condition body) = (result, st) := by
  classical
  letI : DecidablePred state.toPanSemFinite.memaddrs :=
    fun address => Classical.propDecidable (state.memaddrs address)
  have hGuardFinite : state.toPanSemFinite.evalHOLFinite condition =
      some (.val (.word word)) := by
    rw [PanSemStateFiniteExact.evalHOLFinite_eq_toExact]
    exact hGuard
  have hHighBreak := evaluateHOLFinitePair_while_breakOutput state condition body word
    hGuardFinite hWord hClock bodyPost hBody
  have hRunBreak := hHighBreak.symm.trans hWhileRun
  rcases Prod.mk.inj hRunBreak with ⟨rfl, hHighPost⟩
  have hAlignment := evaluateClockSubWhileBodyRunAlignment condition body state
    (.val (.word word)) (.word word) word
    ⟨hGuard, rfl, rfl, hWord, hClock⟩ ihBody ck none st hWhileRun
    (some .break) bodyPost hBody (by simp)
  have hBodyEntryClock : bodyPost.clock ≤ state.clock - 1 := by
    have hBound := evaluateHOLFinitePair_clock_le
      ({ state with clock := state.clock - 1 } : PanPropsEvalStateFiniteExact width σ) body
    rw [hBody] at hBound
    change bodyPost.clock ≤ state.clock - 1 at hBound
    exact hBound
  have hPostClock : ck ≤ bodyPost.clock := by
    have hBound := evaluateWhilePairOutputClock_le_bodyPost state condition body word
      hWord hClock hGuard (some .break) bodyPost hBody
    have hOutputClock : (PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
        (.while condition body)).2.clock = st.clock + ck := by
      have h := congrArg
        (fun pair : Option (PanSemResultExact width) × PanPropsEvalStateFiniteExact width σ =>
          pair.2.clock) hWhileRun
      simpa using h
    rw [hOutputClock] at hBound
    omega
  have hLowClock : state.clock - ck ≠ 0 := by omega
  let lowState : PanPropsEvalStateFiniteExact width σ := { state with clock := state.clock - ck }
  let bodyPostLow : PanPropsEvalStateFiniteExact width σ :=
    { bodyPost with clock := bodyPost.clock - ck }
  let fixedHigh := PanSemStateFiniteExact.fixClockHOLFinite (width := width) (σ := σ)
      (β := Option (PanSemResultExact width))
      (PanSemStateFiniteExact.decClockHOLFinite (width := width) (σ := σ) state.toPanSemFinite)
      (some PanSemResultExact.break, bodyPost.toPanSemFinite)
  let fixedLow := PanSemStateFiniteExact.fixClockHOLFinite (width := width) (σ := σ)
      (β := Option (PanSemResultExact width))
      (PanSemStateFiniteExact.decClockHOLFinite (width := width) (σ := σ) lowState.toPanSemFinite)
      (some PanSemResultExact.break, bodyPostLow.toPanSemFinite)
  have hFixedHigh : fixedHigh.2 =
      ({ st with clock := st.clock + ck } : PanPropsEvalStateFiniteExact width σ).toPanSemFinite := by
    have h := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hHighPost
    simpa [fixedHigh, PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] using h
  have hFixedLow : fixedLow.2 = st.toPanSemFinite := by
    have h := hAlignment.2
    change fixedLow.2 = { fixedHigh.2 with clock := fixedHigh.2.clock - ck } at h
    rw [panSemFinite_subClock_eq_toPanProps st fixedHigh.2 ck hFixedHigh] at h
    exact h
  have hLowBody : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      { { state with clock := state.clock - ck } with
          clock := (state.clock - ck) - 1 } body = (some .break, bodyPostLow) := by
    simpa [bodyPostLow] using hAlignment.1
  have hLowBody' : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      { lowState with clock := lowState.clock - 1 } body = (some .break, bodyPostLow) := by
    change PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      { { state with clock := state.clock - ck } with
          clock := (state.clock - ck) - 1 } body = _
    exact hLowBody
  letI : DecidablePred lowState.toPanSemFinite.memaddrs :=
    fun address => Classical.propDecidable (lowState.memaddrs address)
  have hGuardLowFinite : lowState.toPanSemFinite.evalHOLFinite condition =
      some (.val (.word word)) := by
    change @evalHOLExact width σ _
      ({ state.toPanSemFinite.toExact with clock := state.clock - ck })
      (fun address => Classical.propDecidable (state.memaddrs address)) condition = _
    rw [evalHOLExact_upd_clock_eq state.toPanSemFinite.toExact condition (state.clock - ck)]
    exact hGuard
  have hLowBreak := evaluateHOLFinitePair_while_breakOutput lowState condition body word
    hGuardLowFinite hWord hLowClock bodyPostLow hLowBody'
  rw [hLowBreak]
  simp [lowState, fixedLow, hFixedLow,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite]

/-- Flapjack-specific projection of the condition-failure (error) branch of the
    exact source While clause (`panSemScript.sml:630`) through the PanProps pair
    codec: when the condition does not evaluate to a word value, both the source
    and clock-subtracted runs return `(some .error, state)`. HOL has no separate
    pair-wrapper theorem. This helper only exposes that equation; it does not
    establish the `evaluate_clock_sub` induction case. -/
private theorem evaluateClockSubWhileCondFailProjection {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width)
    (state : PanPropsEvalStateFiniteExact width σ)
    (result : Option (PanSemResultExact width))
    (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat)
    (hWhileRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
        (.while condition body : ProgHOL width) =
      (result, { st with clock := st.clock + ck }))
    (hFail : ∀ (w : BitVec width),
      @PanSemStateFiniteExact.evalHOLFinite width σ _ state.toPanSemFinite
        (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
        condition ≠ some (.val (.word w))) :
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
      { state with clock := state.clock - ck } (.while condition body) = (result, st) := by
  classical
  rw [evaluateHOLFinitePair_while] at hWhileRun
  rw [evaluateHOLFinitePair_while]
  dsimp only
  have hLowCondEq :
      @PanSemStateFiniteExact.evalHOLFinite width σ _
          ({ state with clock := state.clock - ck }.toPanSemFinite)
          (fun address => Classical.propDecidable
            (({ state with clock := state.clock - ck }.toPanSemFinite).memaddrs address))
          condition =
        @PanSemStateFiniteExact.evalHOLFinite width σ _ state.toPanSemFinite
          (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
          condition := by
    rw [PanSemStateFiniteExact.evalHOLFinite_eq_toExact,
        PanSemStateFiniteExact.evalHOLFinite_eq_toExact]
    exact evalHOLExact_upd_clock_eq state.toPanSemFinite.toExact condition (state.clock - ck)
  rw [hLowCondEq]
  cases hC : @PanSemStateFiniteExact.evalHOLFinite width σ _ state.toPanSemFinite
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
      condition with
  | none =>
      simp only [hC] at hWhileRun
      simp only [PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hWhileRun
      obtain ⟨hresult, hpost⟩ := Prod.mk.inj hWhileRun
      subst hresult
      have hst : st = { state with clock := state.clock - ck } := by
        cases st; cases state; simp_all [PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
      subst hst
      rfl
  | some value =>
      cases value with
      | val payload =>
          cases payload with
          | word word => exact absurd hC (hFail word)
      | rStruct f =>
          simp only [hC] at hWhileRun
          simp only [PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hWhileRun
          obtain ⟨hresult, hpost⟩ := Prod.mk.inj hWhileRun
          subst hresult
          have hst : st = { state with clock := state.clock - ck } := by
            cases st; cases state; simp_all [PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
          subst hst
          rfl
      | nStruct n f =>
          simp only [hC] at hWhileRun
          simp only [PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hWhileRun
          obtain ⟨hresult, hpost⟩ := Prod.mk.inj hWhileRun
          subst hresult
          have hst : st = { state with clock := state.clock - ck } := by
            cases st; cases state; simp_all [PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
          subst hst
          rfl

/-- Flapjack-specific projection of the word-zero branch of the exact source
    While clause (`panSemScript.sml:630`) through the PanProps pair codec: a
    word-`0` condition returns `(none, state)` without entering the body. HOL has
    no separate pair-wrapper theorem. This helper only exposes that equation; it
    does not establish the `evaluate_clock_sub` induction case. -/
private theorem evaluateClockSubWhileCondZeroProjection {width : Nat} {σ : Type} [NeZero width]
    (condition : ExpHOL width) (body : ProgHOL width)
    (state : PanPropsEvalStateFiniteExact width σ)
    (result : Option (PanSemResultExact width))
    (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat)
    (hWhileRun : PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
        (.while condition body) = (result, { st with clock := st.clock + ck }))
    (hZero : @PanSemStateFiniteExact.evalHOLFinite width σ _ state.toPanSemFinite
        (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
        condition = some (.val (.word 0))) :
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.while condition body) = (result, st) := by
  classical
  rw [evaluateHOLFinitePair_while] at hWhileRun
  rw [evaluateHOLFinitePair_while]
  dsimp only
  have hLowCondEq :
      @PanSemStateFiniteExact.evalHOLFinite width σ _
          ({ state with clock := state.clock - ck }).toPanSemFinite
          (fun address => Classical.propDecidable
            (({ state with clock := state.clock - ck }).toPanSemFinite.memaddrs address))
          condition =
        @PanSemStateFiniteExact.evalHOLFinite width σ _
          state.toPanSemFinite
          (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
          condition := by
    change @PanSemStateFiniteExact.evalHOLFinite width σ _
      ({ state.toPanSemFinite with clock := state.clock - ck })
      (fun address => Classical.propDecidable
        (({ state.toPanSemFinite with clock := state.clock - ck }).memaddrs address))
      condition = _
    exact evalHOLExact_upd_clock_eq state.toPanSemFinite.toExact condition (state.clock - ck)
  rw [hLowCondEq]
  simp only [hZero]
  simp only [hZero] at hWhileRun
  obtain ⟨hresult, hpost⟩ := Prod.mk.inj hWhileRun
  subst hresult
  have hpostClock : state.clock = st.clock + ck := by
    have h := congrArg (fun s : PanPropsEvalStateFiniteExact width σ => s.clock) hpost
    exact h
  have hst : st = { state with clock := state.clock - ck } := by
    cases st; cases state
    simp_all <;> omega
  subst hst
  rfl

/-- Genuine recursive-induction `Seq` case of HOL `evaluate_clock_sub`. The
    hypotheses are exactly the generated `evaluate_ind` IHs after instantiating
    its motive with the clock-subtraction property: the first-program IH is
    fixed at the source state, and the second-program IH is guarded by that
    first run returning `none`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubSeqCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (first second : ProgHOL width) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state (.seq first second) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      (∀ (firstResult : Option (PanSemResultExact width))
          (firstState : PanPropsEvalStateFiniteExact width σ),
        (firstResult, firstState) =
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state first →
        firstResult = none →
        ∀ (result' : Option (PanSemResultExact width))
          (st' : PanPropsEvalStateFiniteExact width σ) (ck' : Nat),
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair firstState second =
          (result', { st' with clock := st'.clock + ck' }) →
        result' ≠ some .timeOut →
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
          { firstState with clock := firstState.clock - ck' } second = (result', st')) →
      (∀ (result' : Option (PanSemResultExact width))
          (st' : PanPropsEvalStateFiniteExact width σ) (ck' : Nat),
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state first =
          (result', { st' with clock := st'.clock + ck' }) →
        result' ≠ some .timeOut →
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
          { state with clock := state.clock - ck' } first = (result', st')) →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck} (.seq first second) = (result, st) := by
  classical
  intro state result st ck hRun hNotTimeout ihSecond ihFirst
  rw [evaluateHOLFinitePair_seq] at hRun ⊢
  let firstOutput := PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state first
  cases hFirstResult : firstOutput.1 with
  | some firstResult =>
      have hresult : result = some firstResult := by
        have h := congrArg Prod.fst hRun
        simpa [firstOutput, hFirstResult] using h.symm
      subst result
      have hFirstPair : firstOutput = (some firstResult,
          { st with clock := st.clock + ck }) := by
        simpa [firstOutput, hFirstResult] using hRun
      have hFirstLow := ihFirst (some firstResult) st ck hFirstPair hNotTimeout
      simp [hFirstLow]
  | none =>
      have hSecondRun :
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair firstOutput.2 second =
            (result, { st with clock := st.clock + ck }) := by
        simpa [firstOutput, hFirstResult] using hRun
      have hSecondClock := evaluateHOLFinitePair_clock_le firstOutput.2 second
      have hOutputClock := congrArg
        (fun pair : Option (PanSemResultExact width) × PanPropsEvalStateFiniteExact width σ =>
          pair.2.clock) hSecondRun
      have hClockBound : ck ≤ firstOutput.2.clock := by
        have hExact :
            (PanPropsEvalStateFiniteExact.evaluateHOLFinitePair firstOutput.2 second).2.clock =
              st.clock + ck := by
          simpa using hOutputClock
        omega
      let middle : PanPropsEvalStateFiniteExact width σ :=
        { firstOutput.2 with clock := firstOutput.2.clock - ck }
      have hFirstPair : firstOutput = (none, { middle with clock := middle.clock + ck }) := by
        apply Prod.ext
        · exact hFirstResult
        · simp [middle, Nat.sub_add_cancel hClockBound]
      have hFirstLow := ihFirst none middle ck hFirstPair (by simp)
      have hFirstLow' :
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
            { state with clock := state.clock - ck } first = (none, middle) := by
        simpa [firstOutput, hFirstResult, middle] using hFirstLow
      have hFirstObserved : (none, firstOutput.2) =
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state first := by
        apply Prod.ext
        · simpa [firstOutput] using hFirstResult.symm
        · rfl
      have hSecondIH := ihSecond none firstOutput.2 hFirstObserved rfl
      have hSecondLow := hSecondIH result st ck hSecondRun hNotTimeout
      have hSecondLow' :
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair middle second = (result, st) := by
        simpa [middle] using hSecondLow
      simp [hFirstLow', hSecondLow']

set_option maxHeartbeats 4000000 in
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubDecCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL width) (body : ProgHOL width) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.dec name shape initializer body) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      (∀ (state' : PanPropsEvalStateFiniteExact width σ)
          (result' : Option (PanSemResultExact width))
          (st' : PanPropsEvalStateFiniteExact width σ) (ck' : Nat),
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state' body =
          (result', { st' with clock := st'.clock + ck' }) →
        result' ≠ some .timeOut →
        PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
          { state' with clock := state'.clock - ck' } body = (result', st')) →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.dec name shape initializer body) =
          (result, st) := by
  classical
  intro state result st ck hRun hne ihBody
  let highState := state.toPanSemFinite
  let highPost := ({ st with clock := st.clock + ck }).toPanSemFinite
  let lowState : PanPropsEvalStateFiniteExact width σ := { state with clock := state.clock - ck }
  let lowCanonical := lowState.toPanSemFinite
  let highMem : DecidablePred highState.memaddrs :=
    fun address => Classical.propDecidable (highState.memaddrs address)
  let lowMem : DecidablePred lowCanonical.memaddrs :=
    fun address => Classical.propDecidable (lowCanonical.memaddrs address)
  have hCanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState highState
          (.dec name shape initializer body) = (result, highPost) := by
    apply Prod.ext
    · have h := congrArg Prod.fst hRun
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, highState] using h
    · have h := congrArg (fun pair => pair.2.toPanSemFinite) hRun
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, highState, highPost] using h
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total] at hCanonical
  have hInitLow :
      @evalHOLExact width σ _ lowCanonical.toExact lowMem initializer =
        @evalHOLExact width σ _ highState.toExact highMem initializer := by
    change @evalHOLExact width σ _
      ({ highState with clock := lowState.clock }).toExact highMem initializer = _
    exact evalHOLExact_upd_clock_eq highState.toExact initializer lowState.clock
  cases hInit : @evalHOLExact width σ _ highState.toExact highMem initializer with
  | none =>
      simp [hInit] at hCanonical
      rcases hCanonical with ⟨hresult, hpost⟩
      subst result
      have hst : st = lowState := by
        cases st <;> simp_all [highState, highPost, lowState,
          PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
      subst st
      have hLowCanonical :
          PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
              (.dec name shape initializer body) = (some .error, lowCanonical) := by
        rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total]
        have hInitLowNone : @evalHOLExact width σ _ lowCanonical.toExact lowMem initializer = none := by
          simpa [hInitLow] using hInit
        simp [hInitLowNone]
      apply Prod.ext
      · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowState.toPanSemFinite
          (.dec name shape initializer body)).1 = some .error
        rw [hLowCanonical]
      · change PanPropsEvalStateFiniteExact.ofPanSemFinite
          (PanSemStateFiniteExact.evaluateHOLFiniteState lowState.toPanSemFinite
            (.dec name shape initializer body)).2 = lowState
        rw [hLowCanonical]
        exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite lowState
  | some value =>
      have hInitLowValue : @evalHOLExact width σ _ lowCanonical.toExact lowMem initializer = some value := by
        simp only [hInitLow, hInit]
      by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value) = true
      · simp [hInit, hshape] at hCanonical
        let bodyInputHigh := PanSemStateFiniteExact.setVarHOLFinite name value highState
        let bodyOutputHigh := PanSemStateFiniteExact.evaluateHOLFiniteState bodyInputHigh body
        have hBodyOuter :
            (bodyOutputHigh.1,
              { bodyOutputHigh.2 with
                locals := HolFiniteMapExact.resVarEq bodyOutputHigh.2.locals
                  (name, highState.locals.lookup name) }) = (result, highPost) := by
          simpa [bodyInputHigh, bodyOutputHigh] using hCanonical
        have hBodyResult : bodyOutputHigh.1 = result := congrArg Prod.fst hBodyOuter
        have hBodyRestored :
            { bodyOutputHigh.2 with
              locals := HolFiniteMapExact.resVarEq bodyOutputHigh.2.locals
                (name, highState.locals.lookup name) } = highPost :=
          congrArg Prod.snd hBodyOuter
        have hBodyClockBound : ck ≤ bodyOutputHigh.2.clock := by
          have hclock := congrArg
            (fun post : PanSemStateFiniteExact width σ => post.clock) hBodyRestored
          change bodyOutputHigh.2.clock = st.clock + ck at hclock
          omega
        let bodyInputProps := PanPropsEvalStateFiniteExact.ofPanSemFinite bodyInputHigh
        let bodyPostLowCanonical : PanSemStateFiniteExact width σ :=
          { bodyOutputHigh.2 with clock := bodyOutputHigh.2.clock - ck }
        let bodyPostLow := PanPropsEvalStateFiniteExact.ofPanSemFinite bodyPostLowCanonical
        have hBodyHigh :
            PanPropsEvalStateFiniteExact.evaluateHOLFinitePair bodyInputProps body =
              (bodyOutputHigh.1, { bodyPostLow with clock := bodyPostLow.clock + ck }) := by
          simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, bodyInputProps,
            bodyPostLow, bodyPostLowCanonical, bodyOutputHigh, bodyInputHigh,
            PanPropsEvalStateFiniteExact.toPanSemFinite,
            PanPropsEvalStateFiniteExact.ofPanSemFinite,
            Nat.sub_add_cancel hBodyClockBound]
        have hBodyNotTimeout : bodyOutputHigh.1 ≠ some .timeOut := by
          rw [hBodyResult]
          exact hne
        have hBodyLow := ihBody bodyInputProps bodyOutputHigh.1 bodyPostLow ck
          hBodyHigh hBodyNotTimeout
        let bodyInputLowProps : PanPropsEvalStateFiniteExact width σ :=
          { bodyInputProps with clock := bodyInputProps.clock - ck }
        have hBodyInputLowEq : bodyInputLowProps.toPanSemFinite =
            { bodyInputHigh with clock := bodyInputHigh.clock - ck } := by
          simp [bodyInputLowProps, bodyInputProps, bodyInputHigh,
            PanPropsEvalStateFiniteExact.toPanSemFinite,
            PanPropsEvalStateFiniteExact.ofPanSemFinite]
        have hBodyLowPair :
            (PanSemStateFiniteExact.evaluateHOLFiniteState bodyInputLowProps.toPanSemFinite body).1 =
                bodyOutputHigh.1 ∧
              PanPropsEvalStateFiniteExact.ofPanSemFinite
                (PanSemStateFiniteExact.evaluateHOLFiniteState bodyInputLowProps.toPanSemFinite body).2 =
                bodyPostLow := by
          have h := hBodyLow
          simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, bodyInputLowProps,
            bodyInputProps] using h
        have hBodyLowCanonical :
            PanSemStateFiniteExact.evaluateHOLFiniteState
                ({ bodyInputHigh with clock := bodyInputHigh.clock - ck }) body =
              (bodyOutputHigh.1, bodyPostLowCanonical) := by
          have hBodyLowPost := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hBodyLowPair.2
          have hBodyLowPost' :
              (PanSemStateFiniteExact.evaluateHOLFiniteState bodyInputLowProps.toPanSemFinite body).2 =
                bodyPostLowCanonical := by
            simpa [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite,
              bodyPostLow, bodyPostLowCanonical] using hBodyLowPost
          rw [← hBodyInputLowEq]
          apply Prod.ext
          · exact hBodyLowPair.1
          · exact hBodyLowPost'
        have hLowRestored :
            { bodyPostLowCanonical with
              locals := HolFiniteMapExact.resVarEq bodyPostLowCanonical.locals
                (name, lowCanonical.locals.lookup name) } = st.toPanSemFinite := by
          have h := congrArg
            (fun post : PanSemStateFiniteExact width σ =>
              { post with clock := post.clock - ck }) hBodyRestored
          simpa [bodyPostLowCanonical, highPost, highState, lowCanonical, lowState,
            PanPropsEvalStateFiniteExact.toPanSemFinite, Nat.sub_add_cancel hBodyClockBound]
            using h
        have hLowCanonical :
            PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                (.dec name shape initializer body) = (result, st.toPanSemFinite) := by
          rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total]
          have hInitLowValue' :
              @evalHOLExact width σ _ lowCanonical.toExact lowMem initializer = some value := hInitLowValue
          simp only [hInitLowValue', hshape, if_true]
          have hBodyInputEq :
              PanSemStateFiniteExact.setVarHOLFinite name value lowCanonical =
                { bodyInputHigh with clock := bodyInputHigh.clock - ck } := by
            simp [bodyInputHigh, highState, lowCanonical, lowState,
              PanSemStateFiniteExact.setVarHOLFinite,
              PanPropsEvalStateFiniteExact.toPanSemFinite]
          rw [hBodyInputEq, hBodyLowCanonical]
          simp [hBodyResult, hLowRestored]
        apply Prod.ext
        · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowState.toPanSemFinite
            (.dec name shape initializer body)).1 = result
          rw [hLowCanonical]
        · change PanPropsEvalStateFiniteExact.ofPanSemFinite
            (PanSemStateFiniteExact.evaluateHOLFiniteState lowState.toPanSemFinite
              (.dec name shape initializer body)).2 = st
          rw [hLowCanonical]
          simp [PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite]
      · simp [hInit, hshape] at hCanonical
        rcases hCanonical with ⟨hresult, hpost⟩
        subst result
        have hst : st = lowState := by
          cases st <;> simp_all [highState, highPost, lowState,
            PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
        subst st
        have hLowCanonical :
            PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                (.dec name shape initializer body) = (some .error, lowCanonical) := by
          rw [PanSemStateFiniteExact.evaluateHOLFiniteState_dec_total]
          have hInitLowValue' :
              @evalHOLExact width σ _ lowCanonical.toExact lowMem initializer = some value := hInitLowValue
          simp [hInitLowValue', hshape]
        apply Prod.ext
        · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowState.toPanSemFinite
            (.dec name shape initializer body)).1 = some .error
          rw [hLowCanonical]
        · change PanPropsEvalStateFiniteExact.ofPanSemFinite
            (PanSemStateFiniteExact.evaluateHOLFiniteState lowState.toPanSemFinite
              (.dec name shape initializer body)).2 = lowState
          rw [hLowCanonical]
          exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite lowState

/-! # The `If` induction case of HOL `evaluate_clock_sub`

HOL handles the `If` constructor in the generic final branch of its
induction proof and supplies a single guarded induction hypothesis over
`if w <> 0 then c1 else c2` at the same state.  This leaf keeps that
exact guarded IH and the theorem's original premisses. -/

set_option linter.unusedSimpArgs false in
private theorem evaluateHOLFinitePair_ite {width : Nat} {σ : Type} [NeZero width]
    (state : PanPropsEvalStateFiniteExact width σ)
    (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width) :
    PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
        (.ite condition thenBranch elseBranch) =
      (match @evalHOLExact width σ _ state.toPanSemFinite.toExact
          (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
          condition with
       | some (.val (.word word)) =>
           if word = 0 then PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state elseBranch
           else PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state thenBranch
       | _ => (some .error, state)) := by
  classical
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_ite,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite]
  cases h : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
      condition with
  | none =>
      simp only [h]
      rw [PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite]
  | some value =>
      cases value with
      | val payload =>
          cases payload with
          | word word =>
              simp only [h]
              by_cases hzero : word = 0
              · rw [if_pos hzero, if_pos hzero]
              · rw [if_neg hzero, if_neg hzero]
      | rStruct f =>
          simp only [h]
          rw [PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite]
      | nStruct n f =>
          simp only [h]
          rw [PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite]

set_option maxHeartbeats 4000000 in
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubIfCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (condition : ExpHOL width) (thenBranch elseBranch : ProgHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.ite condition thenBranch elseBranch : ProgHOL width) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      (∀ (v1 : ValueHOL width) (v6 : HolWordLab width) (w : BitVec width),
        @evalHOLExact width σ _ state.toPanSemFinite.toExact
            (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address))
            condition = some v1 ∧
          v1 = .val v6 ∧ v6 = .word w →
        ∀ (result2 : Option (PanSemResultExact width))
          (st2 : PanPropsEvalStateFiniteExact width σ) (ck2 : Nat),
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
              (if w ≠ 0 then thenBranch else elseBranch : ProgHOL width) =
            (result2, { st2 with clock := st2.clock + ck2 }) →
          result2 ≠ some .timeOut →
          PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
            { state with clock := state.clock - ck2 }
            (if w ≠ 0 then thenBranch else elseBranch : ProgHOL width) = (result2, st2)) →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.ite condition thenBranch elseBranch) =
          (result, st) := by
  classical
  intro condition thenBranch elseBranch state result st ck hRun hne ihIf
  let lowState : PanPropsEvalStateFiniteExact width σ := { state with clock := state.clock - ck }
  have hLowCondEq :
      @evalHOLExact width σ _ lowState.toPanSemFinite.toExact
          (fun address => Classical.propDecidable (lowState.toPanSemFinite.memaddrs address))
          condition =
        @evalHOLExact width σ _ state.toPanSemFinite.toExact
          (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address)) condition := by
    change @evalHOLExact width σ _
      ({ state.toPanSemFinite with clock := state.clock - ck }).toExact
      (fun address => Classical.propDecidable
        (({ state.toPanSemFinite with clock := state.clock - ck }).memaddrs address))
      condition = _
    exact evalHOLExact_upd_clock_eq state.toPanSemFinite.toExact condition (state.clock - ck)
  rw [evaluateHOLFinitePair_ite] at hRun
  rw [evaluateHOLFinitePair_ite]
  rw [hLowCondEq]
  generalize hCond : @evalHOLExact width σ _ state.toPanSemFinite.toExact
      (fun address => Classical.propDecidable (state.toPanSemFinite.memaddrs address)) condition = x
    at hRun ⊢
  cases x with
  | none =>
      dsimp only at hRun ⊢
      obtain ⟨hresult, hpost⟩ := Prod.mk.inj hRun
      subst hresult
      have hst : st = lowState := by
        cases st <;> simp_all [lowState, PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
      subst hst
      rfl
  | some value =>
      cases value with
      | val payload =>
          cases payload with
          | word word =>
              dsimp only at hRun ⊢
              have hBranchPair :
                  PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
                      (if word ≠ 0 then thenBranch else elseBranch : ProgHOL width) =
                    (result, { st with clock := st.clock + ck }) := by
                by_cases hzero : word = 0
                · rw [if_pos hzero] at hRun
                  rw [if_neg (by simp [hzero])]
                  exact hRun
                · rw [if_neg hzero] at hRun
                  rw [if_pos hzero]
                  exact hRun
              have hBranchLow := ihIf (.val (.word word)) (.word word) word
                ⟨hCond, rfl, rfl⟩ result st ck hBranchPair hne
              by_cases hzero : word = 0
              · rw [if_neg (by simp [hzero])] at hBranchLow
                rw [if_pos hzero]
                exact hBranchLow
              · rw [if_pos hzero] at hBranchLow
                rw [if_neg hzero]
                exact hBranchLow
      | rStruct f =>
          dsimp only at hRun ⊢
          obtain ⟨hresult, hpost⟩ := Prod.mk.inj hRun
          subst hresult
          have hst : st = lowState := by
            cases st <;> simp_all [lowState, PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
          subst hst
          rfl
      | nStruct n f =>
          dsimp only at hRun ⊢
          obtain ⟨hresult, hpost⟩ := Prod.mk.inj hRun
          subst hresult
          have hst : st = lowState := by
            cases st <;> simp_all [lowState, PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
          subst hst
          rfl


/-! # The `Skip` induction case of HOL `evaluate_clock_sub`

This leaf case keeps the theorem's original high-run equation and non-timeout
assumption.  The HOL `Skip` clause returns the unchanged state, so its clock
equation identifies the lower-clock input directly. -/

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubSkipCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state .skip =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } .skip = (result, st) := by
  classical
  intro state result st ck hRun _hne
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_skip,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hRun ⊢
  rcases Prod.mk.inj hRun with ⟨rfl, hState⟩
  subst state
  simp

/-- Genuine `Break` case of HOL `evaluate_clock_sub`. The source evaluator
    returns `(SOME Break,s)` without changing `s`, so the original run equation
    identifies the clock-subtracted input. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubBreakCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state .break =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } .break = (result, st) := by
  classical
  intro state result st ck hRun _hne
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_break,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hRun ⊢
  rcases Prod.mk.inj hRun with ⟨rfl, hState⟩
  subst state
  simp

/-- Genuine `Continue` case of HOL `evaluate_clock_sub`. The source evaluator
    returns `(SOME Continue,s)` without changing `s`, so the original run
    equation identifies the clock-subtracted input. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubContinueCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state .continue =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } .continue = (result, st) := by
  classical
  intro state result st ck hRun _hne
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_continue,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hRun ⊢
  rcases Prod.mk.inj hRun with ⟨rfl, hState⟩
  subst state
  simp

/-- Genuine `Annot` case of HOL `evaluate_clock_sub`. The annotation has no
    semantic effect, so this leaf uses the same direct clock-state argument as
    `Skip`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubAnnotCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (tag text : MlS)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state (.annot tag text) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.annot tag text) = (result, st) := by
  classical
  intro tag text state result st ck hRun _hne
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_annot,
    PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite] at hRun ⊢
  rcases Prod.mk.inj hRun with ⟨rfl, hState⟩
  subst state
  simp

/-- Genuine `Assign` case of HOL `evaluate_clock_sub`. HOL `evaluate_def`'s
    `Assign` clause (`panSemScript.sml:566-572`) evaluates the source
    expression, fails with `SOME Error` and the unchanged state when the
    lookup is invalid, and otherwise performs the keyed-variable write with
    `set_kvar`. The exact expression evaluator ignores the clock, validation
    reads only locals/globals, and `set_kvar` copies the clock from its input,
    so the clock-subtracted run reaches the same result and post-state. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubAssignCaseHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (kind : VarKind) (name : MlS) (source : ExpHOL width) :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.assign kind name source : ProgHOL width) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.assign kind name source) =
          (result, st) := by
  classical
  intro state result st ck hRun _hne
  let highState := state.toPanSemFinite
  let highPost := ({ st with clock := st.clock + ck }).toPanSemFinite
  let lowState : PanPropsEvalStateFiniteExact width σ := { state with clock := state.clock - ck }
  let lowCanonical := lowState.toPanSemFinite
  let highMem : DecidablePred highState.memaddrs :=
    fun address => Classical.propDecidable (highState.memaddrs address)
  let lowMem : DecidablePred lowCanonical.memaddrs :=
    fun address => Classical.propDecidable (lowCanonical.memaddrs address)
  have hCanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState highState
          (.assign kind name source) = (result, highPost) := by
    apply Prod.ext
    · have h := congrArg Prod.fst hRun
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, highState] using h
    · have h := congrArg (fun pair => pair.2.toPanSemFinite) hRun
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, highState, highPost] using h
  have hEvalLow :
      @evalHOLExact width σ _ lowCanonical.toExact lowMem source =
        @evalHOLExact width σ _ highState.toExact highMem source := by
    change @evalHOLExact width σ _
      ({ highState with clock := lowState.clock }).toExact highMem source = _
    exact evalHOLExact_upd_clock_eq highState.toExact source lowState.clock
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_assign] at hCanonical
  cases hEval : @evalHOLExact width σ _ highState.toExact highMem source with
  | none =>
      simp [hEval] at hCanonical
      rcases hCanonical with ⟨hresult, hpost⟩
      subst result
      have hst : st = lowState := by
        cases st <;> simp_all [highState, highPost, lowState,
          PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
      subst st
      have hLowCanonical :
          PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
              (.assign kind name source) = (some .error, lowCanonical) := by
        simp [PanSemStateFiniteExact.evaluateHOLFiniteState_assign, hEvalLow, hEval]
      apply Prod.ext
      · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
          (.assign kind name source)).1 = some .error
        rw [hLowCanonical]
      · change PanPropsEvalStateFiniteExact.ofPanSemFinite
          (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
            (.assign kind name source)).2 = lowState
        rw [hLowCanonical]
        exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite lowState
  | some value =>
      have hEvalLowValue :
          @evalHOLExact width σ _ lowCanonical.toExact lowMem source = some value := by
        simpa [hEvalLow] using hEval
      have hvalidEq :
          PanSemStateFiniteExact.isValidValueHOLFinite lowCanonical kind name value =
            PanSemStateFiniteExact.isValidValueHOLFinite highState kind name value := by
        cases kind <;> rfl
      by_cases hvalid :
          PanSemStateFiniteExact.isValidValueHOLFinite highState kind name value = true
      · have hvalidLow :
            PanSemStateFiniteExact.isValidValueHOLFinite lowCanonical kind name value = true := by
          rw [hvalidEq]; exact hvalid
        have hvalidLowExact :
            isValidValueHOLExact lowCanonical.toExact kind name value = true := by
          simpa only [PanSemStateFiniteExact.isValidValueHOLFinite_eq] using hvalidLow
        simp only [hEval, hvalid] at hCanonical
        rcases Prod.mk.inj hCanonical with ⟨hresult, hpost⟩
        subst result
        have hstateClock : state.clock = st.clock + ck := by
          have h := congrArg PanSemStateFiniteExact.clock hpost
          cases kind <;>
            simpa [highState, highPost, PanSemStateFiniteExact.setKvarHOLFinite,
              PanSemStateFiniteExact.setVarHOLFinite,
              PanSemStateFiniteExact.setGlobalHOLFinite,
              PanPropsEvalStateFiniteExact.toPanSemFinite] using h
        have hlowClock : lowCanonical.clock = st.clock := by
          simp only [lowCanonical, lowState,
            PanPropsEvalStateFiniteExact.toPanSemFinite]
          omega
        have hKvarCommute :
            PanSemStateFiniteExact.setKvarHOLFinite kind name value lowCanonical =
              { PanSemStateFiniteExact.setKvarHOLFinite kind name value highState with
                  clock := lowCanonical.clock } := by
          cases kind <;> rfl
        have hLowSecond : PanPropsEvalStateFiniteExact.ofPanSemFinite
            (PanSemStateFiniteExact.setKvarHOLFinite kind name value lowCanonical) = st := by
          rw [hKvarCommute]
          rw [show PanPropsEvalStateFiniteExact.ofPanSemFinite
                ({ PanSemStateFiniteExact.setKvarHOLFinite kind name value highState with
                    clock := lowCanonical.clock }) =
              { PanPropsEvalStateFiniteExact.ofPanSemFinite
                  (PanSemStateFiniteExact.setKvarHOLFinite kind name value highState) with
                  clock := lowCanonical.clock } from rfl]
          have hpostOf : PanPropsEvalStateFiniteExact.ofPanSemFinite
              (PanSemStateFiniteExact.setKvarHOLFinite kind name value highState) =
              { st with clock := st.clock + ck } := by
            rw [hpost]
            exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite _
          rw [hpostOf, hlowClock]
        have hLowCanonical :
            PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                (.assign kind name source) =
              (none,
                PanSemStateFiniteExact.setKvarHOLFinite kind name value lowCanonical) := by
          simp [PanSemStateFiniteExact.evaluateHOLFiniteState_assign, hEvalLowValue,
            hvalidLowExact]
        apply Prod.ext
        · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
            (.assign kind name source)).1 = none
          rw [hLowCanonical]
        · change PanPropsEvalStateFiniteExact.ofPanSemFinite
            (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
              (.assign kind name source)).2 = st
          rw [hLowCanonical]
          exact hLowSecond
      · have hinvalid :
            PanSemStateFiniteExact.isValidValueHOLFinite highState kind name value = false :=
          Bool.eq_false_iff.mpr hvalid
        have hvalidLowFalse :
            PanSemStateFiniteExact.isValidValueHOLFinite lowCanonical kind name value = false := by
          rw [hvalidEq]; exact hinvalid
        have hvalidLowFalseExact :
            isValidValueHOLExact lowCanonical.toExact kind name value = false := by
          simpa only [PanSemStateFiniteExact.isValidValueHOLFinite_eq] using hvalidLowFalse
        simp only [hEval, hinvalid] at hCanonical
        rcases Prod.mk.inj hCanonical with ⟨hresult, hpost⟩
        subst result
        have hst : st = lowState := by
          cases st <;> simp_all [highState, highPost, lowState,
            PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
        subst st
        have hLowCanonical :
            PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                (.assign kind name source) = (some .error, lowCanonical) := by
          simp [PanSemStateFiniteExact.evaluateHOLFiniteState_assign, hEvalLowValue,
            hvalidLowFalseExact]
        apply Prod.ext
        · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
            (.assign kind name source)).1 = some .error
          rw [hLowCanonical]
        · change PanPropsEvalStateFiniteExact.ofPanSemFinite
            (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
              (.assign kind name source)).2 = lowState
          rw [hLowCanonical]
          exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite lowState

/-- Genuine `Tick` case of HOL `evaluate_clock_sub`. The non-timeout premise
    rules out the zero-clock branch; on the positive branch both evaluations
    decrement the clock once. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubTickCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state .tick =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } .tick = (result, st) := by
  classical
  intro state result st ck hRun hne
  have hresult := congrArg Prod.fst hRun
  have hpost := congrArg Prod.snd hRun
  simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
    PanSemStateFiniteExact.evaluateHOLFiniteState_tick] at hresult hpost
  by_cases hclock : state.clock = 0
  · have hresult' : result = some .timeOut := by
      simpa [PanPropsEvalStateFiniteExact.toPanSemFinite, hclock] using hresult.symm
    exact (hne hresult').elim
  · have hresult' : result = none := by
      have hhighclock : state.toPanSemFinite.clock ≠ 0 := by
        simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hclock
      simpa [hhighclock] using hresult.symm
    clear hresult
    subst result
    have hpost' :
      PanPropsEvalStateFiniteExact.ofPanSemFinite
          (PanSemStateFiniteExact.decClockHOLFinite state.toPanSemFinite) =
          { st with clock := st.clock + ck } := by
      simpa only [PanPropsEvalStateFiniteExact.toPanSemFinite, hclock,
        if_false, PanSemStateFiniteExact.decClockHOLFinite] using hpost
    have hclockEq : state.clock - 1 = st.clock + ck := by
      simpa only [PanPropsEvalStateFiniteExact.toPanSemFinite,
        PanPropsEvalStateFiniteExact.ofPanSemFinite,
        PanSemStateFiniteExact.decClockHOLFinite] using
          congrArg PanPropsEvalStateFiniteExact.clock hpost'
    have hlow : state.clock - ck ≠ 0 := by omega
    clear hRun hpost
    have hfinal : { state with clock := state.clock - ck - 1 } = st := by
      cases state
      cases st
      simp_all [PanPropsEvalStateFiniteExact.ofPanSemFinite,
        PanPropsEvalStateFiniteExact.toPanSemFinite,
        PanSemStateFiniteExact.decClockHOLFinite]
      omega
    have hlowCanonical :
        ({ state with clock := state.clock - ck }).toPanSemFinite.clock ≠ 0 := by
      simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hlow
    change
      ((PanSemStateFiniteExact.evaluateHOLFiniteState
          ({ state with clock := state.clock - ck }.toPanSemFinite) .tick).1,
        PanPropsEvalStateFiniteExact.ofPanSemFinite
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            ({ state with clock := state.clock - ck }.toPanSemFinite) .tick).2) =
        (none, st)
    rw [PanSemStateFiniteExact.evaluateHOLFiniteState_tick]
    rw [if_neg hlowCanonical]
    simpa [PanSemStateFiniteExact.decClockHOLFinite,
      PanPropsEvalStateFiniteExact.toPanSemFinite,
      PanPropsEvalStateFiniteExact.ofPanSemFinite] using
      congrArg (fun finalState =>
        ((none : Option (PanSemResultExact width)), finalState)) hfinal

/-- Genuine recursive-induction `Return` case of HOL `evaluate_clock_sub`.
    The exact expression evaluator ignores the clock; the source's return/error
    branches then differ only by the clock field. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubReturnCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (expression : ExpHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state (.return expression) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.return expression) = (result, st) := by
  classical
  intro expression state result st ck hRun hne
  let highState := state.toPanSemFinite
  let highPost := ({ st with clock := st.clock + ck }).toPanSemFinite
  let lowState : PanPropsEvalStateFiniteExact width σ := { state with clock := state.clock - ck }
  let lowCanonical := lowState.toPanSemFinite
  let highMem : DecidablePred highState.memaddrs :=
    fun address => Classical.propDecidable (highState.memaddrs address)
  let lowMem : DecidablePred lowCanonical.memaddrs :=
    fun address => Classical.propDecidable (lowCanonical.memaddrs address)
  have hCanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState highState (.return expression) =
        (result, highPost) := by
    apply Prod.ext
    · have h := congrArg Prod.fst hRun
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, highState] using h
    · have h := congrArg (fun pair => pair.2.toPanSemFinite) hRun
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, highState, highPost] using h
  have hEvalLow :
      @evalHOLExact width σ _ lowCanonical.toExact lowMem expression =
        @evalHOLExact width σ _ highState.toExact highMem expression := by
    change @evalHOLExact width σ _
      ({ highState with clock := lowState.clock }).toExact highMem expression = _
    exact evalHOLExact_upd_clock_eq highState.toExact expression lowState.clock
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_return] at hCanonical
  cases hEval : @evalHOLExact width σ _ highState.toExact highMem expression with
  | none =>
      simp [hEval] at hCanonical
      rcases hCanonical with ⟨hresult, hpost⟩
      subst result
      have hst : st = lowState := by
        cases st <;> simp_all [highState, highPost, lowState,
          PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
      subst st
      have hLowCanonical :
          PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
              (.return expression) = (some .error, lowCanonical) := by
        simp [PanSemStateFiniteExact.evaluateHOLFiniteState_return, hEvalLow, hEval]
      apply Prod.ext
      · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
          (.return expression)).1 = some .error
        rw [hLowCanonical]
      · change PanPropsEvalStateFiniteExact.ofPanSemFinite
          (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
            (.return expression)).2 = lowState
        rw [hLowCanonical]
        exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite lowState
  | some value =>
      have hEvalLowValue :
          @evalHOLExact width σ _ lowCanonical.toExact lowMem expression = some value := by
        simpa [hEvalLow] using hEval
      by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL highState.structs
          (shapeOfHOLExact value) ≤ 32
      · simp [hEval, hsize] at hCanonical
        rcases hCanonical with ⟨hresult, hpost⟩
        have hresult' : some (.returned value) = result := hresult
        subst result
        have hsizeLow :
            Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL lowCanonical.structs
              (shapeOfHOLExact value) ≤ 32 := by
          simpa [lowCanonical, lowState, highState,
            PanPropsEvalStateFiniteExact.toPanSemFinite] using hsize
        have hLowState :
            PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                (.return expression) = (some (.returned value), st.toPanSemFinite) := by
          rw [PanSemStateFiniteExact.evaluateHOLFiniteState_return]
          simp only [hEvalLowValue, hsizeLow, if_pos]
          have hRestored :
              PanSemStateFiniteExact.emptyLocalsHOLFinite lowCanonical = st.toPanSemFinite := by
            cases state <;> cases st <;>
              simp_all [highState, highPost, lowState, lowCanonical,
                PanPropsEvalStateFiniteExact.toPanSemFinite,
                PanSemStateFiniteExact.emptyLocalsHOLFinite] <;> omega
          exact Prod.ext rfl hRestored
        apply Prod.ext
        · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
            (.return expression)).1 = some (.returned value)
          rw [hLowState]
        · change PanPropsEvalStateFiniteExact.ofPanSemFinite
            (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
              (.return expression)).2 = st
          rw [hLowState]
          simp [PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite]
      · simp [hEval, hsize] at hCanonical
        rcases hCanonical with ⟨hresult, hpost⟩
        have hresult' : some .error = result := hresult
        subst result
        have hst : st = lowState := by
          cases st <;> simp_all [highState, highPost, lowState,
            PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
        subst st
        have hsizeLow :
            ¬ Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL lowCanonical.structs
              (shapeOfHOLExact value) ≤ 32 := by
          simpa [lowCanonical, lowState, highState,
            PanPropsEvalStateFiniteExact.toPanSemFinite] using hsize
        have hLowCanonical :
            PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                (.return expression) = (some .error, lowCanonical) := by
          rw [PanSemStateFiniteExact.evaluateHOLFiniteState_return]
          simp [hEvalLowValue, hsizeLow]
        apply Prod.ext
        · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
            (.return expression)).1 = some .error
          rw [hLowCanonical]
        · change PanPropsEvalStateFiniteExact.ofPanSemFinite
            (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
              (.return expression)).2 = lowState
          rw [hLowCanonical]
          exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite lowState

/-! ## Unchanged event logs determine the complete FFI state

HOL `io_events_eq_imp_ffi_eq` (`panPropsScript.sml:974-1019`) quantifies in
order over program, initial state, result, and final state. Its premises are a
successful evaluation equation and equality of the initial/final FFI event
lists; it concludes equality of the complete FFI records. The local state
carrier below exists so the four `|->` fields and their roundtrip witness are
owned by this PanProps module, as required by its representation qualifier.
`evaluatePanPropsHOLFiniteState` is only the field-for-field codec around the
canonical finite PanSem evaluator. The proof transports its successful result
to the exact broad recursive dispatcher, applies the kernel-checked recursive
event/FFI invariant, and translates the unchanged FFI field back. -/

/-- PanProps-side representation adapter: execute the canonical finite PanSem
    evaluator and convert its output state through the field-for-field local
    carrier codec. It adds no evaluator behavior. -/
noncomputable def evaluatePanPropsHOLFiniteState {width : Nat} {σ : Type}
    [NeZero width] (state : PanPropsEvalStateFiniteExact width σ)
    (program : ProgHOL width) :
    Option (PanSemResultExact width) × PanPropsEvalStateFiniteExact width σ :=
  let output := PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite program
  (output.1, PanPropsEvalStateFiniteExact.ofPanSemFinite output.2)

/-- HOL `io_events_eq_imp_ffi_eq` (`panPropsScript.sml:974`): for the exact
    finite-map Pan state, successful evaluation and equal endpoint `io_events`
    imply equality of the complete FFI state, including the oracle and
    host-state fields. The state quantifiers use this module's canonical
    `HolFiniteMapExact` translation and roundtrip witness; the word index uses
    the standard positive-width `BitVec` translation. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "io_events_eq_imp_ffi_eq" 974
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem ioEventsEqImpFfiEqHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (program : ProgHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      evaluatePanPropsHOLFiniteState state program = (result, post) →
      state.ffi.ioEvents = post.ffi.ioEvents → post.ffi = state.ffi := by
  classical
  intro program state result post heval hevents
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite program =
        (result, post.toPanSemFinite) := by
    apply Prod.ext
    · simpa [evaluatePanPropsHOLFiniteState] using congrArg Prod.fst heval
    · simpa [evaluatePanPropsHOLFiniteState] using
        congrArg PanPropsEvalStateFiniteExact.toPanSemFinite (congrArg Prod.snd heval)
  let context : PanSemStateFiniteExact.FiniteEvalContext width σ :=
    ⟨state.toPanSemFinite,
      fun address => Classical.propDecidable (state.memaddrs address),
      fun address => Classical.propDecidable (state.shMemaddrs address)⟩
  obtain ⟨postContext, hrecursive, hpost⟩ :=
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
      state.toPanSemFinite program context rfl (result, post.toPanSemFinite) hcanonical
  have hprojection :=
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext_projection program context
  rw [hrecursive] at hprojection
  simp only [Option.map_some] at hprojection
  have hbroad :
      evalPanSemRecursiveCallContextHOLExact program context.toExact =
        some (result, postContext.toExact) := by
    simpa using hprojection.symm
  have heventsBroad :
      context.toExact.state.ffi.ioEvents =
        postContext.toExact.state.ffi.ioEvents := by
    simpa [context, PanPropsEvalStateFiniteExact.toPanSemFinite,
      PanSemStateFiniteExact.toExact, PanPropsEvalStateFiniteExact.toExact,
      PanSemStateFiniteExact.FiniteEvalContext.toExact, hpost] using hevents
  have hffiBroad := evalPanSemRecursiveCallContextHOLExact_ffi_eq_of_ioEvents_eq
    program context.toExact (result, postContext.toExact) hbroad heventsBroad
  have hffi : state.ffi = post.ffi := by
    simpa [context, PanPropsEvalStateFiniteExact.toPanSemFinite,
      PanSemStateFiniteExact.toExact, PanPropsEvalStateFiniteExact.toExact,
      PanSemStateFiniteExact.FiniteEvalContext.toExact, hpost] using hffiBroad
  exact hffi.symm
/-- Genuine nonrecursive `Raise` case of HOL `evaluate_clock_sub`. The exact
    expression evaluator and the exception-shape lookup are unchanged by the
    clock update; the successful branch clears locals and the error branches
    preserve the state, exactly as `evaluate_def` specifies. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_clock_sub"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateClockSubRaiseCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (exceptionId : MlS) (expression : ExpHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ) (ck : Nat),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state (.raise exceptionId expression) =
        (result, { st with clock := st.clock + ck }) →
      result ≠ some .timeOut →
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
        { state with clock := state.clock - ck } (.raise exceptionId expression) = (result, st) := by
  classical
  intro exceptionId expression state result st ck hRun _hne
  let highState := state.toPanSemFinite
  let highPost := ({ st with clock := st.clock + ck }).toPanSemFinite
  let lowState : PanPropsEvalStateFiniteExact width σ := { state with clock := state.clock - ck }
  let lowCanonical := lowState.toPanSemFinite
  let highMem : DecidablePred highState.memaddrs :=
    fun address => Classical.propDecidable (highState.memaddrs address)
  let lowMem : DecidablePred lowCanonical.memaddrs :=
    fun address => Classical.propDecidable (lowCanonical.memaddrs address)
  have hCanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState highState (.raise exceptionId expression) =
        (result, highPost) := by
    apply Prod.ext
    · have h := congrArg Prod.fst hRun
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, highState] using h
    · have h := congrArg (fun pair => pair.2.toPanSemFinite) hRun
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair, highState, highPost] using h
  have hEvalLow :
      @evalHOLExact width σ _ lowCanonical.toExact lowMem expression =
        @evalHOLExact width σ _ highState.toExact highMem expression := by
    change @evalHOLExact width σ _
      ({ highState with clock := lowState.clock }).toExact highMem expression = _
    exact evalHOLExact_upd_clock_eq highState.toExact expression lowState.clock
  have hShapeLow : lowCanonical.eshapes.lookup exceptionId = highState.eshapes.lookup exceptionId := by
    rfl
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_raise] at hCanonical
  cases hShape : highState.eshapes.lookup exceptionId with
  | none =>
      simp [hShape] at hCanonical
      rcases hCanonical with ⟨hresult, hpost⟩
      subst result
      have hst : st = lowState := by
        cases st <;> simp_all [highState, highPost, lowState,
          PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
      subst st
      have hLowCanonical :
          PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
              (.raise exceptionId expression) = (some .error, lowCanonical) := by
        simp [PanSemStateFiniteExact.evaluateHOLFiniteState_raise, hShapeLow, hShape]
      apply Prod.ext
      · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
          (.raise exceptionId expression)).1 = some .error
        rw [hLowCanonical]
      · change PanPropsEvalStateFiniteExact.ofPanSemFinite
          (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
            (.raise exceptionId expression)).2 = lowState
        rw [hLowCanonical]
        exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite lowState
  | some shape =>
      cases hEval : @evalHOLExact width σ _ highState.toExact highMem expression with
      | none =>
          simp [hShape, hEval] at hCanonical
          rcases hCanonical with ⟨hresult, hpost⟩
          subst result
          have hst : st = lowState := by
            cases st <;> simp_all [highState, highPost, lowState,
              PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
          subst st
          have hLowCanonical :
              PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                  (.raise exceptionId expression) = (some .error, lowCanonical) := by
            simp [PanSemStateFiniteExact.evaluateHOLFiniteState_raise,
              hShapeLow, hShape, hEvalLow, hEval]
          apply Prod.ext
          · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
              (.raise exceptionId expression)).1 = some .error
            rw [hLowCanonical]
          · change PanPropsEvalStateFiniteExact.ofPanSemFinite
              (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                (.raise exceptionId expression)).2 = lowState
            rw [hLowCanonical]
            exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite lowState
      | some value =>
          have hEvalLow :
              @evalHOLExact width σ _ lowCanonical.toExact lowMem expression = some value := by
            simpa [hEvalLow] using hEval
          by_cases heq : shapeOfHOLExact value = shape
          · by_cases hsize : Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
                highState.structs (shapeOfHOLExact value) ≤ 32
            · have hguard : shapeOfHOLExact value = shape ∧
                  Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL highState.structs
                    (shapeOfHOLExact value) ≤ 32 := ⟨heq, hsize⟩
              simp only [hShape, hEval] at hCanonical
              change @ite _ _ (Classical.propDecidable
                (shapeOfHOLExact value = shape ∧
                  Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL highState.structs
                    (shapeOfHOLExact value) ≤ 32))
                (some (.exception exceptionId value),
                  PanSemStateFiniteExact.emptyLocalsHOLFinite highState)
                (some .error, highState) = (result, highPost) at hCanonical
              rw [if_pos hguard] at hCanonical
              rcases Prod.mk.inj hCanonical with ⟨hresult, hpost⟩
              subst result
              clear hCanonical hRun
              have hsizeLow :
                  Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL lowCanonical.structs
                    (shapeOfHOLExact value) ≤ 32 := by
                simpa [lowCanonical, lowState, highState,
                  PanPropsEvalStateFiniteExact.toPanSemFinite] using hsize
              have hLowCanonical :
                  PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                      (.raise exceptionId expression) =
                    (some (.exception exceptionId value), st.toPanSemFinite) := by
                rw [PanSemStateFiniteExact.evaluateHOLFiniteState_raise]
                simp only [hShapeLow, hShape, hEvalLow]
                rw [heq]
                change @ite _ _ (Classical.propDecidable
                  (shape = shape ∧
                    Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL lowCanonical.structs
                      shape ≤ 32))
                  (some (PanSemResultExact.exception exceptionId value),
                    PanSemStateFiniteExact.emptyLocalsHOLFinite lowCanonical)
                  (some PanSemResultExact.error, lowCanonical) =
                  (some (PanSemResultExact.exception exceptionId value), st.toPanSemFinite)
                have hRestored :
                    PanSemStateFiniteExact.emptyLocalsHOLFinite lowCanonical =
                      st.toPanSemFinite := by
                  cases state <;> cases st <;>
                    simp_all [highState, highPost, lowState, lowCanonical,
                      PanPropsEvalStateFiniteExact.toPanSemFinite,
                      PanSemStateFiniteExact.emptyLocalsHOLFinite] <;> omega
                rw [if_pos ⟨rfl, by simpa [heq] using hsizeLow⟩]
                exact Prod.ext rfl hRestored
              apply Prod.ext
              · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                  (.raise exceptionId expression)).1 = some (.exception exceptionId value)
                rw [hLowCanonical]
              · change PanPropsEvalStateFiniteExact.ofPanSemFinite
                  (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                    (.raise exceptionId expression)).2 = st
                rw [hLowCanonical]
                simp [PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite]
            · have hguard : ¬ (shapeOfHOLExact value = shape ∧
                  Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL highState.structs
                    (shapeOfHOLExact value) ≤ 32) := by
                intro hcondition
                exact hsize hcondition.2
              simp only [hShape, hEval] at hCanonical
              change @ite _ _ (Classical.propDecidable
                (shapeOfHOLExact value = shape ∧
                  Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL highState.structs
                    (shapeOfHOLExact value) ≤ 32))
                (some (.exception exceptionId value),
                  PanSemStateFiniteExact.emptyLocalsHOLFinite highState)
                (some .error, highState) = (result, highPost) at hCanonical
              rw [if_neg hguard] at hCanonical
              rcases Prod.mk.inj hCanonical with ⟨hresult, hpost⟩
              subst result
              clear hCanonical hRun
              have hsizeLow : ¬ Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL
                  lowCanonical.structs (shapeOfHOLExact value) ≤ 32 := by
                intro hle
                have hstructs : lowCanonical.structs = highState.structs := rfl
                rw [hstructs] at hle
                exact hsize hle
              have hst : st = lowState := by
                cases st <;> simp_all [highState, highPost, lowState,
                  PanPropsEvalStateFiniteExact.toPanSemFinite]
              subst st
              have hLowCanonical :
                  PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                      (.raise exceptionId expression) = (some .error, lowCanonical) := by
                rw [PanSemStateFiniteExact.evaluateHOLFiniteState_raise]
                simp only [hShapeLow, hShape, hEvalLow]
                have hguardLow : ¬ (shapeOfHOLExact value = shape ∧
                    Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL lowCanonical.structs
                      (shapeOfHOLExact value) ≤ 32) := by
                  intro hcondition
                  exact hsizeLow hcondition.2
                change @ite _ _ (Classical.propDecidable
                  (shapeOfHOLExact value = shape ∧
                    Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL lowCanonical.structs
                      (shapeOfHOLExact value) ≤ 32))
                  (some (PanSemResultExact.exception exceptionId value),
                    PanSemStateFiniteExact.emptyLocalsHOLFinite lowCanonical)
                  (some PanSemResultExact.error, lowCanonical) =
                  (some PanSemResultExact.error, lowCanonical)
                rw [if_neg hguardLow]
              apply Prod.ext
              · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                  (.raise exceptionId expression)).1 = some .error
                rw [hLowCanonical]
              · change PanPropsEvalStateFiniteExact.ofPanSemFinite
                  (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                    (.raise exceptionId expression)).2 = lowState
                rw [hLowCanonical]
                exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite lowState
          · have hguard : ¬ (shapeOfHOLExact value = shape ∧
                Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL highState.structs
                  (shapeOfHOLExact value) ≤ 32) := by
              simp [heq]
            simp only [hShape, hEval] at hCanonical
            change @ite _ _ (Classical.propDecidable
              (shapeOfHOLExact value = shape ∧
                Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL highState.structs
                  (shapeOfHOLExact value) ≤ 32))
              (some (.exception exceptionId value),
                PanSemStateFiniteExact.emptyLocalsHOLFinite highState)
              (some .error, highState) = (result, highPost) at hCanonical
            rw [if_neg hguard] at hCanonical
            rcases Prod.mk.inj hCanonical with ⟨hresult, hpost⟩
            subst result
            clear hCanonical hRun
            have hst : st = lowState := by
              cases st <;> simp_all [highState, highPost, lowState,
                PanPropsEvalStateFiniteExact.toPanSemFinite] <;> omega
            subst st
            have hLowCanonical :
                PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                    (.raise exceptionId expression) = (some .error, lowCanonical) := by
              rw [PanSemStateFiniteExact.evaluateHOLFiniteState_raise]
              simp [hShapeLow, hShape, hEvalLow, heq]
            apply Prod.ext
            · change (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                (.raise exceptionId expression)).1 = some .error
              rw [hLowCanonical]
            · change PanPropsEvalStateFiniteExact.ofPanSemFinite
                (PanSemStateFiniteExact.evaluateHOLFiniteState lowCanonical
                  (.raise exceptionId expression)).2 = lowState
              rw [hLowCanonical]
              exact PanPropsEvalStateFiniteExact.ofPanSemFinite_toPanSemFinite lowState
end Flapjack


/-! # The `ShMemLoad` induction case of HOL `evaluate_invariants`

HOL `ShMemLoad` (`sh_mem_load_def`) returns Error with the input state, or
calls the shared-memory FFI and then either clears locals (`FinalFFI`) or writes
the loaded word to the destination variable together with the returned FFI
state. `call_FFI` keeps the oracle, so all eight invariant fields are
preserved. -/

open Flapjack.Pancake.PanLang (ExpHOL MlS ProgHOL)

namespace Flapjack

/-- The eight `evaluate_invariants` fields for one `ShMemLoad` step of the
    canonical finite evaluator. Untagged infrastructure for the tagged
    `ShMemLoad` case. -/
theorem shMemLoadStepFieldsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (operator : OpSize) (kind : VarKind)
    (name : MlS) (address : ExpHOL width) :
    let post := (PanSemStateFiniteExact.evaluateHOLFiniteState state
      (.shMemLoad operator kind name address : ProgHOL width)).2
    post.memaddrs = state.memaddrs ∧ post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧ post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧ post.structs = state.structs ∧
      post.code = state.code ∧ post.ffi.oracle = state.ffi.oracle := by
  classical
  intro post
  have hstep : ∀ (kind : VarKind) (addr : RiscV.Word width) (nb : Nat),
      let q := (@PanSemStateFiniteExact.shMemLoadHOLFiniteExact width σ _ state
        (fun current => Classical.propDecidable (state.shMemaddrs current))
        kind name addr nb).2
      q.memaddrs = state.memaddrs ∧ q.shMemaddrs = state.shMemaddrs ∧
        q.be = state.be ∧ q.eshapes = state.eshapes ∧
        q.baseAddr = state.baseAddr ∧ q.structs = state.structs ∧
        q.code = state.code ∧ q.ffi.oracle = state.ffi.oracle := by
    intro kind addr nb q
    simp only [q, PanSemStateFiniteExact.shMemLoadHOLFiniteExact]
    split <;> split
    all_goals
      first
      | (simp; done)
      | (split
         · simp [PanSemStateFiniteExact.emptyLocalsHOLFinite]
         · rename_i newFfi newBytes hcall
           have horacle := callFFIHOL_ret_oracle state.ffi _ _ _ newFfi newBytes hcall
           cases kind <;>
             simp [PanSemStateFiniteExact.setKvarFfiHOLFinite,
               PanSemStateFiniteExact.setKvarHOLFinite, PanSemStateFiniteExact.setVarHOLFinite,
               PanSemStateFiniteExact.setGlobalHOLFinite, horacle])
  simp only [post]
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_shMemLoad_source]
  split
  · split
    · exact hstep kind _ _
    · simp
  · simp

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsShMemLoadCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (operator : OpSize) (kind : VarKind) (name : MlS) (address : ExpHOL width)
      (state : PanPropsEvalStateFiniteExact width σ)
      (result : Option (PanSemResultExact width))
      (post : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair state
          (.shMemLoad operator kind name address : ProgHOL width) = (result, post) →
      post.memaddrs = state.memaddrs ∧
      post.shMemaddrs = state.shMemaddrs ∧
      post.be = state.be ∧
      post.eshapes = state.eshapes ∧
      post.baseAddr = state.baseAddr ∧
      post.structs = state.structs ∧
      post.code = state.code ∧
      post.ffi.oracle = state.ffi.oracle := by
  classical
  intro operator kind name address state result post hRun
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.shMemLoad operator kind name address : ProgHOL width) =
        (result, post.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.shMemLoad operator kind name address : ProgHOL width)).1 = result ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
          (.shMemLoad operator kind name address : ProgHOL width)).2 = post.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  have hpost : post.toPanSemFinite =
      (PanSemStateFiniteExact.evaluateHOLFiniteState state.toPanSemFinite
        (.shMemLoad operator kind name address : ProgHOL width)).2 :=
    (Prod.mk.inj hcanonical).2.symm
  have hfields := shMemLoadStepFieldsHOLFinite state.toPanSemFinite operator kind name address
  simp only at hfields
  rw [← hpost] at hfields
  simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hfields

end Flapjack


/-! # The `ShMemStore` induction case of HOL `evaluate_invariants`

HOL `ShMemStore` (`sh_mem_store_def`) returns Error with the input state, or
calls the shared-memory FFI and then returns the input state (`FinalFFI`) or the
input state with the returned FFI state. `call_FFI` keeps the oracle, so all
eight invariant fields are preserved. -/

open Flapjack.Pancake.PanLang (ExpHOL MlS ProgHOL)

namespace Flapjack

/-- `sh_mem_store` returns either its input state or the input state with only
    `ffi` replaced by an FFI state with the same oracle. Untagged infrastructure. -/
private theorem shMemStoreHOLExact_shape {width : Nat} {σ : Type} [NeZero width]
    (st : PanSemStateExact width σ) [DecidablePred st.shMemaddrs]
    (w a : RiscV.Word width) (nb : Nat) :
    (∃ r0, shMemStoreHOLExact st w a nb = (r0, st)) ∨
      ∃ r0 f, shMemStoreHOLExact st w a nb = (r0, { st with ffi := f }) ∧
        f.oracle = st.ffi.oracle := by
  rcases hq : shMemStoreHOLExact st w a nb with ⟨r0, q⟩
  unfold shMemStoreHOLExact at hq
  split at hq <;> split at hq
  all_goals
    first
    | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq; exact Or.inl ⟨_, rfl⟩)
    | (split at hq
       · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq; exact Or.inl ⟨_, rfl⟩
       · rename_i newFfi newBytes hcall
         obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq
         exact Or.inr ⟨_, newFfi, rfl, callFFIHOL_ret_oracle st.ffi _ _ _ newFfi newBytes hcall⟩)

/-- The eight `evaluate_invariants` fields for one `ShMemStore` step of the
    canonical finite evaluator. Untagged infrastructure for the tagged
    `ShMemStore` case. -/
theorem shMemStoreStepFieldsHOLFinite {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (op : OpSize) (ad e : ExpHOL width) :
    let post := (PanSemStateFiniteExact.evaluateHOLFiniteState s
      (.shMemStore op ad e : ProgHOL width)).2
    post.memaddrs = s.memaddrs ∧ post.shMemaddrs = s.shMemaddrs ∧
      post.be = s.be ∧ post.eshapes = s.eshapes ∧
      post.baseAddr = s.baseAddr ∧ post.structs = s.structs ∧
      post.code = s.code ∧ post.ffi.oracle = s.ffi.oracle := by
  classical
  intro post
  simp only [post]
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_shMemStore_total]
  dsimp only
  split
  · rename_i addr bytes _ _
    rcases @shMemStoreHOLExact_shape width σ _ s.toExact
        (fun key => Classical.propDecidable (s.shMemaddrs key)) bytes addr (nbOpHOL op) with
      ⟨r0, hG⟩ | ⟨r0, f, hG, hor⟩
    · simp [hG, PanSemStateFiniteExact.ofExact, PanSemStateFiniteExact.toExact]
    · simp [hG, hor, PanSemStateFiniteExact.ofExact, PanSemStateFiniteExact.toExact]
  · simp

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsShMemStoreCaseHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (op : OpSize) (ad e : ExpHOL width)
      (s : PanPropsEvalStateFiniteExact width σ)
      (res : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair s
          (.shMemStore op ad e : ProgHOL width) = (res, st) →
      st.memaddrs = s.memaddrs ∧
      st.shMemaddrs = s.shMemaddrs ∧
      st.be = s.be ∧
      st.eshapes = s.eshapes ∧
      st.baseAddr = s.baseAddr ∧
      st.structs = s.structs ∧
      st.code = s.code ∧
      st.ffi.oracle = s.ffi.oracle := by
  classical
  intro op ad e s res st hRun
  have hcanonical :
      PanSemStateFiniteExact.evaluateHOLFiniteState s.toPanSemFinite
          (.shMemStore op ad e : ProgHOL width) =
        (res, st.toPanSemFinite) := by
    have hpair := congrArg
      (fun output => (output.1, PanPropsEvalStateFiniteExact.toPanSemFinite output.2)) hRun
    have hpair' :
        (PanSemStateFiniteExact.evaluateHOLFiniteState s.toPanSemFinite
          (.shMemStore op ad e : ProgHOL width)).1 = res ∧
        (PanSemStateFiniteExact.evaluateHOLFiniteState s.toPanSemFinite
          (.shMemStore op ad e : ProgHOL width)).2 = st.toPanSemFinite := by
      simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using hpair
    exact Prod.ext hpair'.1 hpair'.2
  have hpost : st.toPanSemFinite =
      (PanSemStateFiniteExact.evaluateHOLFiniteState s.toPanSemFinite
        (.shMemStore op ad e : ProgHOL width)).2 :=
    (Prod.mk.inj hcanonical).2.symm
  have hfields := shMemStoreStepFieldsHOLFinite s.toPanSemFinite op ad e
  simp only at hfields
  rw [← hpost] at hfields
  simpa [PanPropsEvalStateFiniteExact.toPanSemFinite] using hfields

end Flapjack


/-! # The `DecCall` case of HOL `evaluate_invariants`

The HOL `evaluate_ind` DecCall conjunct
(`scripts/hol-probes/pan_sem_evaluate_ind_probe.out`, as ported in the tagged
`evaluateIndHOL`) has two IHs: the continuation IH
`P (prog1, set_var rt retv (st with locals := s.locals))` after the callee run
`evaluate (prog, dec_clock s with locals := newlocals) = (SOME (Return retv), st)`
with both shape checks, and the callee IH
`P (prog, dec_clock s with locals := newlocals)`, both under the argument,
`lookup_code`, and nonzero-clock guards. The case is stated with exactly these
IHs, with HOL's TFL binders, at `P = evaluate_invariants`'s conclusion
(`evaluateInvariantsAtHOLFinite`). The binder conventions are the reviewed ones
of the `Call` case: `OPT_MMAP (eval s)` is `List.mapM` of the exact evaluator
with the classical address decision, and `dec_clock s with locals := newlocals`
is `callEntryStateHOLFinite`. -/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

/-- HOL's DecCall callee IH (`P (prog, dec_clock s with locals := newlocals)`) at
    `P = evaluateInvariantsAtHOLFinite`, binder for binder. -/
private abbrev evaluateInvariantsDecCallCalleeIH {width : Nat} {σ : Type}
    [NeZero width] (fname : MlS) (argexps : List (ExpHOL width))
    (s : PanPropsEvalStateFiniteExact width σ) : Prop :=
  ∀ (args : List (ValueHOL width))
    (v2 : ProgHOL width × (HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL))
    (prog : ProgHOL width)
    (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (return_sh : ShapeHOL),
    argexps.mapM (fun expression =>
      PanSemStateFiniteExact.evalHOLFinite s.toPanSemFinite
        (h := fun address => Classical.propDecidable
          (s.toPanSemFinite.memaddrs address)) expression) = some args →
    PanSemStateFiniteExact.lookupCodeHOLFinite s.toPanSemFinite.code.lookup
      fname args = some (v2.1, v2.2.1, v2.2.2) →
    v2 = (prog, v7) →
    v7 = (newlocals, return_sh) →
    s.toPanSemFinite.clock ≠ 0 →
    evaluateInvariantsAtHOLFinite
      (PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.callEntryStateHOLFinite s.toPanSemFinite newlocals)) prog

/-- HOL's DecCall continuation IH
    (`P (prog1, set_var rt retv (st with locals := s.locals))`) at
    `P = evaluateInvariantsAtHOLFinite`, binder for binder. -/
private abbrev evaluateInvariantsDecCallContIH {width : Nat} {σ : Type}
    [NeZero width] (rt : MlS) (shape : ShapeHOL) (fname : MlS)
    (argexps : List (ExpHOL width)) (prog1 : ProgHOL width)
    (s : PanPropsEvalStateFiniteExact width σ) : Prop :=
  ∀ (args : List (ValueHOL width))
    (v2 : ProgHOL width × (HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL))
    (prog : ProgHOL width)
    (v7 : HolFiniteMapExact MlS (ValueHOL width) × ShapeHOL)
    (newlocals : HolFiniteMapExact MlS (ValueHOL width))
    (return_sh : ShapeHOL)
    (eval_prog : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ)
    (v : Option (PanSemResultExact width))
    (st : PanSemStateFiniteExact width σ)
    (v3 : PanSemResultExact width) (retv : ValueHOL width),
    argexps.mapM (fun expression =>
      PanSemStateFiniteExact.evalHOLFinite s.toPanSemFinite
        (h := fun address => Classical.propDecidable
          (s.toPanSemFinite.memaddrs address)) expression) = some args →
    PanSemStateFiniteExact.lookupCodeHOLFinite s.toPanSemFinite.code.lookup
      fname args = some (v2.1, v2.2.1, v2.2.2) →
    v2 = (prog, v7) →
    v7 = (newlocals, return_sh) →
    s.toPanSemFinite.clock ≠ 0 →
    eval_prog = PanSemStateFiniteExact.evaluateHOLFiniteState
      (PanSemStateFiniteExact.callEntryStateHOLFinite s.toPanSemFinite newlocals) prog →
    eval_prog = (v, st) →
    v = some v3 →
    v3 = .returned retv →
    shapeOfHOLExact retv = shape →
    shapeOfHOLExact retv = return_sh →
    evaluateInvariantsAtHOLFinite
      (PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.setVarHOLFinite rt retv
          { st with locals := s.toPanSemFinite.locals })) prog1

/-- The eight invariant fields of a canonical post-state against a canonical
    pre-state. -/
private abbrev decCallFields {width : Nat} {σ : Type} [NeZero width]
    (post pre : PanSemStateFiniteExact width σ) : Prop :=
  post.memaddrs = pre.memaddrs ∧ post.shMemaddrs = pre.shMemaddrs ∧ post.be = pre.be ∧
    post.eshapes = pre.eshapes ∧ post.baseAddr = pre.baseAddr ∧ post.structs = pre.structs ∧
    post.code = pre.code ∧ post.ffi.oracle = pre.ffi.oracle

private theorem decCallFields_trans {width : Nat} {σ : Type} [NeZero width]
    {a b c : PanSemStateFiniteExact width σ} (h1 : decCallFields a b)
    (h2 : decCallFields b c) : decCallFields a c := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8⟩

/-- An `evaluateInvariantsAtHOLFinite` fact at `ofPanSemFinite q` gives the
    fields of the canonical run from `q`. -/
private theorem decCallFields_of_at {width : Nat} {σ : Type} [NeZero width]
    (q : PanSemStateFiniteExact width σ) (p : ProgHOL width)
    (hat : evaluateInvariantsAtHOLFinite (PanPropsEvalStateFiniteExact.ofPanSemFinite q) p) :
    decCallFields (PanSemStateFiniteExact.evaluateHOLFiniteState q p).2 q := by
  have h := hat (PanSemStateFiniteExact.evaluateHOLFiniteState q p).1
    (PanPropsEvalStateFiniteExact.ofPanSemFinite
      (PanSemStateFiniteExact.evaluateHOLFiniteState q p).2)
    (by simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair])
  simpa [PanPropsEvalStateFiniteExact.ofPanSemFinite, decCallFields] using h

@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsDecCallCaseHOLFinite {width : Nat} {σ : Type}
    [NeZero width] :
    ∀ (rt : MlS) (shape : ShapeHOL) (fname : MlS) (argexps : List (ExpHOL width))
      (prog1 : ProgHOL width) (s : PanPropsEvalStateFiniteExact width σ)
      (res : Option (PanSemResultExact width))
      (st : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair s
          (.decCall rt shape fname argexps prog1 : ProgHOL width) = (res, st) →
      evaluateInvariantsDecCallContIH rt shape fname argexps prog1 s →
      evaluateInvariantsDecCallCalleeIH fname argexps s →
      st.memaddrs = s.memaddrs ∧
      st.shMemaddrs = s.shMemaddrs ∧
      st.be = s.be ∧
      st.eshapes = s.eshapes ∧
      st.baseAddr = s.baseAddr ∧
      st.structs = s.structs ∧
      st.code = s.code ∧
      st.ffi.oracle = s.ffi.oracle := by
  classical
  intro rt shape fname argexps prog1 s res st hRun ihCont ihBody
  have hRun' : ((PanSemStateFiniteExact.evaluateHOLFiniteState s.toPanSemFinite
      (.decCall rt shape fname argexps prog1)).1,
      PanPropsEvalStateFiniteExact.ofPanSemFinite
        (PanSemStateFiniteExact.evaluateHOLFiniteState s.toPanSemFinite
          (.decCall rt shape fname argexps prog1)).2) = (res, st) := hRun
  have hst := (Prod.mk.inj hRun').2.symm
  suffices key : decCallFields (PanSemStateFiniteExact.evaluateHOLFiniteState s.toPanSemFinite
      (.decCall rt shape fname argexps prog1)).2 s.toPanSemFinite by
    subst hst
    simpa [PanPropsEvalStateFiniteExact.ofPanSemFinite,
      PanPropsEvalStateFiniteExact.toPanSemFinite, decCallFields] using key
  rcases hW : PanSemStateFiniteExact.evaluateHOLFiniteState s.toPanSemFinite
      (.decCall rt shape fname argexps prog1) with ⟨r, t⟩
  show decCallFields t s.toPanSemFinite
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_decCall_fixClockRewrite] at hW
  have hsame : decCallFields s.toPanSemFinite s.toPanSemFinite := by simp [decCallFields]
  cases hargs : PanSemStateFiniteExact.evalListHOLFinite s.toPanSemFinite
      (h := fun address => Classical.propDecidable (s.toPanSemFinite.memaddrs address))
      argexps with
  | none =>
      rw [hargs] at hW
      obtain ⟨_, rfl⟩ := Prod.mk.inj hW
      exact hsame
  | some values =>
  rw [hargs] at hW
  dsimp only at hW
  cases hlk : PanSemStateFiniteExact.lookupCodeHOLFinite s.toPanSemFinite.code.lookup
      fname values with
  | none =>
      rw [hlk] at hW
      obtain ⟨_, rfl⟩ := Prod.mk.inj hW
      exact hsame
  | some triple =>
  obtain ⟨prog, newlocals, rsh⟩ := triple
  rw [hlk] at hW
  dsimp only at hW
  by_cases hclk : s.toPanSemFinite.clock = 0
  · rw [if_pos hclk] at hW
    obtain ⟨_, rfl⟩ := Prod.mk.inj hW
    simp [decCallFields, PanSemStateFiniteExact.emptyLocalsHOLFinite]
  rw [if_neg hclk] at hW
  try dsimp only at hW
  have hmap : argexps.mapM (fun expression =>
      PanSemStateFiniteExact.evalHOLFinite s.toPanSemFinite
        (h := fun address => Classical.propDecidable
          (s.toPanSemFinite.memaddrs address)) expression) = some values := by
    rw [← evalListHOLFinite_eq_mapM]; exact hargs
  have hentry : decCallFields
      (PanSemStateFiniteExact.callEntryStateHOLFinite s.toPanSemFinite newlocals)
      s.toPanSemFinite := by
    simp [decCallFields, PanSemStateFiniteExact.callEntryStateHOLFinite]
  have hbody := decCallFields_trans
    (decCallFields_of_at _ prog (ihBody values (prog, newlocals, rsh) prog (newlocals, rsh)
      newlocals rsh hmap hlk rfl rfl hclk)) hentry
  rcases hb : PanSemStateFiniteExact.evaluateHOLFiniteState
      (PanSemStateFiniteExact.callEntryStateHOLFinite s.toPanSemFinite newlocals) prog with
    ⟨br, bt⟩
  rw [hb] at hW hbody
  dsimp only at hW hbody
  rcases br with _ | br
  · obtain ⟨_, rfl⟩ := Prod.mk.inj hW
    exact hbody
  cases br with
  | returned retv =>
      dsimp only at hW
      by_cases hsh : (shapeEqHOL (shapeOfHOLExact retv) shape &&
          shapeEqHOL (shapeOfHOLExact retv) rsh) = true
      · rw [if_pos hsh] at hW
        simp only [Bool.and_eq_true] at hsh
        have h1 : shapeOfHOLExact retv = shape := (shapeEqHOL_eq_true _ _).mp hsh.1
        have h2 : shapeOfHOLExact retv = rsh := (shapeEqHOL_eq_true _ _).mp hsh.2
        obtain ⟨_, rfl⟩ := Prod.mk.inj hW
        have hcont := decCallFields_of_at _ prog1
          (ihCont values (prog, newlocals, rsh) prog (newlocals, rsh) newlocals rsh
            (some (.returned retv), bt) (some (.returned retv)) bt (.returned retv) retv
            hmap hlk rfl rfl hclk hb.symm rfl rfl rfl h1 h2)
        have hset : decCallFields
            (PanSemStateFiniteExact.setVarHOLFinite rt retv
              { bt with locals := s.toPanSemFinite.locals }) bt := by
          simp [decCallFields, PanSemStateFiniteExact.setVarHOLFinite]
        have hfin := decCallFields_trans (decCallFields_trans hcont hset) hbody
        simpa [decCallFields] using hfin
      · rw [if_neg hsh] at hW
        obtain ⟨_, rfl⟩ := Prod.mk.inj hW
        exact hbody
  | error | «break» | «continue» =>
      obtain ⟨_, rfl⟩ := Prod.mk.inj hW
      exact hbody
  | timeOut | exception _ _ | finalFfi _ =>
      obtain ⟨_, rfl⟩ := Prod.mk.inj hW
      simpa [decCallFields, PanSemStateFiniteExact.emptyLocalsHOLFinite] using hbody

end Flapjack


/-! # Assembled HOL `evaluate_invariants`

`panPropsScript.sml:1150` proves `evaluate_invariants` by `recInduct
evaluate_ind`. The assembly applies the tagged `evaluateIndHOL` (HOL
`evaluate_ind`) to `P (p, u) := evaluateInvariantsAtHOLFinite (ofPanSemFinite u) p`
and discharges each of its 21 conjuncts with the tagged constructor leaf above,
translating each HOL IH to the leaf's premise through the field-for-field
PanProps codec. -/

namespace Flapjack

open Flapjack.Pancake.PanLang (MlS ShapeHOL ExpHOL ProgHOL)

/-- The predicate `P` of HOL's `recInduct evaluate_ind` for `evaluate_invariants`,
    over the canonical carrier. -/
private abbrev evaluateInvariantsIndP {width : Nat} {σ : Type} [NeZero width]
    (pu : ProgHOL width × PanSemStateFiniteExact width σ) : Prop :=
  evaluateInvariantsAtHOLFinite (PanPropsEvalStateFiniteExact.ofPanSemFinite pu.2) pu.1

private theorem evaluateInvariantsIndP_all {width : Nat} {σ : Type} [NeZero width] :
    ∀ (p : ProgHOL width) (u : PanSemStateFiniteExact width σ), evaluateInvariantsIndP (p, u) := by
  classical
  refine evaluateIndHOL (evaluateInvariantsIndP (width := width) (σ := σ))
    ⟨?skip, ?dec, ?assign, ?prim, ?store, ?store32, ?storeByte, ?shLoad, ?shStore, ?seq, ?ite,
      ?brk, ?cont, ?whl, ?ret, ?rai, ?tick, ?annot, ?call, ?decCall, ?ext⟩
  case skip => exact fun s => evaluateInvariantsSkipCaseHOLFinite _
  case assign => exact fun vk v src s => evaluateInvariantsAssignCaseHOLFinite vk v src _
  case prim => exact fun v pop es s => evaluateInvariantsPrimitiveCaseHOLFinite v pop es _
  case store => exact fun d src s => evaluateInvariantsStoreCaseHOLFinite d src _
  case store32 => exact fun d src s => evaluateInvariantsStore32CaseHOLFinite d src _
  case storeByte => exact fun d src s => evaluateInvariantsStoreByteCaseHOLFinite d src _
  case shLoad => exact fun op vk v ad s => evaluateInvariantsShMemLoadCaseHOLFinite op vk v ad _
  case shStore => exact fun op ad e s => evaluateInvariantsShMemStoreCaseHOLFinite op ad e _
  case brk => exact fun s => evaluateInvariantsBreakCaseHOLFinite _
  case cont => exact fun s => evaluateInvariantsContinueCaseHOLFinite _
  case ret => exact fun e s => evaluateInvariantsReturnCaseHOLFinite e _
  case rai => exact fun eid e s => evaluateInvariantsRaiseCaseHOLFinite eid e _
  case tick => exact fun s => evaluateInvariantsTickCaseHOLFinite _
  case annot => exact fun v0 v1 s => evaluateInvariantsAnnotCaseHOLFinite v0 v1 _
  case ext => exact fun f a b c d s => evaluateInvariantsExtCallCaseHOLFinite f a b c d _
  case seq =>
    intro c1 c2 s ⟨ih2, ih1⟩ res post hRun
    refine evaluateInvariantsSeqCaseHOLFinite c1 c2 _ res post hRun ?_ ?_
    · intro fr fp ⟨hfp, hfr⟩
      have hfp' : fp = PanPropsEvalStateFiniteExact.ofPanSemFinite
          (PanSemStateFiniteExact.evaluateHOLFiniteState s c1).2 := by
        have := congrArg Prod.snd hfp
        simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using this
      have hfr' : fr = (PanSemStateFiniteExact.evaluateHOLFiniteState s c1).1 := by
        have := congrArg Prod.fst hfp
        simpa [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair] using this
      subst hfp'
      exact ih2 fr _ ⟨by rw [hfr'], hfr⟩
    · intro fr fp hfp
      exact ih1 fr fp hfp.symm
  case ite =>
    intro e c1 c2 s ih res post hRun
    refine evaluateInvariantsIfCaseHOLFinite e c1 c2 _ res post hRun ?_
    intro v1 v6 w hh
    exact ih v1 v6 w (by simpa using hh)
  case dec =>
    intro v sh e prog s ih res post hRun
    refine evaluateInvariantsDecCaseHOLFinite v sh e prog _ res post hRun ?_
    intro value hv hsh
    exact ih value ⟨by simpa using hv, (shapeEqHOL_eq_true _ _).mp hsh⟩
  case whl =>
    intro e c s ⟨ihc, ihn, ihb⟩ res post hRun
    have hdecS : ({ PanPropsEvalStateFiniteExact.ofPanSemFinite s with
        clock := (PanPropsEvalStateFiniteExact.ofPanSemFinite s).clock - 1 } :
        PanPropsEvalStateFiniteExact width σ) =
        PanPropsEvalStateFiniteExact.ofPanSemFinite s.decClockHOLFinite := rfl
    have hpairDec : ∀ (r : Option (PanSemResultExact width))
        (s1 : PanPropsEvalStateFiniteExact width σ),
        (r, s1) = PanPropsEvalStateFiniteExact.evaluateHOLFinitePair
          { PanPropsEvalStateFiniteExact.ofPanSemFinite s with
            clock := (PanPropsEvalStateFiniteExact.ofPanSemFinite s).clock - 1 } c →
        (r, (PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c).2) =
            PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c ∧
          s1 = PanPropsEvalStateFiniteExact.ofPanSemFinite
            (PanSemStateFiniteExact.evaluateHOLFiniteState s.decClockHOLFinite c).2 := by
      intro r s1 h
      rw [hdecS] at h
      simp only [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite, Prod.mk.injEq] at h
      exact ⟨by rw [h.1], h.2⟩
    refine evaluateInvariantsWhileCaseHOLFinite e c _ ⟨?_, ?_, ?_⟩ res post hRun
    · intro v2 v11 w r s1 v1 ⟨he, h2, h3, hw, hck, hrun, hr, hv1⟩
      obtain ⟨hrun', rfl⟩ := hpairDec r s1 hrun
      exact ihc v2 v11 w r _ v1 ⟨by simpa using he, h2, h3, hw, hck, hrun', hr, hv1⟩
    · intro v2 v11 w r s1 ⟨he, h2, h3, hw, hck, hrun, hr⟩
      obtain ⟨hrun', rfl⟩ := hpairDec r s1 hrun
      exact ihn v2 v11 w r _ ⟨by simpa using he, h2, h3, hw, hck, hrun', hr⟩
    · intro v2 v11 w ⟨he, h2, h3, hw, hck⟩ r st hst
      rw [hdecS] at hst
      exact ihb v2 v11 w ⟨by simpa using he, h2, h3, hw, hck⟩ r st hst
  case call =>
    intro caltyp fname argexps s ⟨ihH, ihB⟩ res post hRun
    refine evaluateInvariantsCallCaseHOLFinite caltyp fname argexps _ res post hRun ?_ ?_
    · intro args v7 prog v12 newlocals return_sh eval_prog v4 st v8 eid exn v v1 v2 v3 eid' v5
        evar p sh hmap hlk h7 h12 hck hev1 hev2 hv4 hv8 hct hv hv2 hv3 hv5 heid hsh hexn hvalid
      have hargs : s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address)) argexps =
          some args := by
        rw [evalListHOLFinite_eq_mapM]; exact hmap
      exact ihH args v7 prog v12 newlocals return_sh eval_prog v4 st v8 eid exn v v1 v2 v3 eid'
        v5 evar p sh ⟨hargs, by simpa using hlk, h7, h12, hck, hev1, hev2, hv4, hv8, hct, hv,
          hv2, hv3, hv5, heid, by simpa using hsh, hexn, by simpa using hvalid⟩
    · intro args v7 prog v12 newlocals return_sh hmap hlk h7 h12 hck
      have hargs : s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address)) argexps =
          some args := by
        rw [evalListHOLFinite_eq_mapM]; exact hmap
      exact ihB args v7 prog v12 newlocals return_sh ⟨hargs, by simpa using hlk, h7, h12, hck⟩
  case decCall =>
    intro rt shape fname argexps prog1 s ⟨ihC, ihB⟩ res post hRun
    refine evaluateInvariantsDecCallCaseHOLFinite rt shape fname argexps prog1 _ res post hRun
      ?_ ?_
    · intro args v2 prog v7 newlocals return_sh eval_prog v st v3 retv hmap hlk h2 h7 hck hev1
        hev2 hv hv3 hs1 hs2
      have hargs : s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address)) argexps =
          some args := by
        rw [evalListHOLFinite_eq_mapM]; exact hmap
      exact ihC args v2 prog v7 newlocals return_sh eval_prog v st v3 retv
        ⟨hargs, by simpa using hlk, h2, h7, hck, hev1, hev2, hv, hv3, hs1, hs2⟩
    · intro args v2 prog v7 newlocals return_sh hmap hlk h2 h7 hck
      have hargs : s.evalListHOLFinite
          (h := fun address => Classical.propDecidable (s.memaddrs address)) argexps =
          some args := by
        rw [evalListHOLFinite_eq_mapM]; exact hmap
      exact ihB args v2 prog v7 newlocals return_sh ⟨hargs, by simpa using hlk, h2, h7, hck⟩


/-- Exact port of HOL `panProps$evaluate_invariants` (`panPropsScript.sml:1150-1158`):
    `∀p t res st. evaluate (p,t) = (res,st) ⇒ st.memaddrs = t.memaddrs ∧
    st.sh_memaddrs = t.sh_memaddrs ∧ st.be = t.be ∧ st.eshapes = t.eshapes ∧
    st.base_addr = t.base_addr ∧ st.structs = t.structs ∧ st.code = t.code ∧
    st.ffi.oracle = t.ffi.oracle`. `evaluate` is the pair evaluator
    `evaluateHOLFinitePair` (the tagged total `evaluateHOLFiniteState` through the
    field-for-field PanProps codec). The proof is HOL's `recInduct evaluate_ind`:
    the tagged `evaluateIndHOL`, with each conjunct discharged by the tagged
    constructor leaf above. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "evaluate_invariants" 1150
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateInvariantsHOLFinite {width : Nat} {σ : Type} [NeZero width] :
    ∀ (p : ProgHOL width) (t : PanPropsEvalStateFiniteExact width σ)
      (res : Option (PanSemResultExact width)) (st : PanPropsEvalStateFiniteExact width σ),
      PanPropsEvalStateFiniteExact.evaluateHOLFinitePair t p = (res, st) →
      st.memaddrs = t.memaddrs ∧
      st.shMemaddrs = t.shMemaddrs ∧
      st.be = t.be ∧
      st.eshapes = t.eshapes ∧
      st.baseAddr = t.baseAddr ∧
      st.structs = t.structs ∧
      st.code = t.code ∧
      st.ffi.oracle = t.ffi.oracle := by
  intro p t res st h
  have hall := evaluateInvariantsIndP_all p t.toPanSemFinite res st
    (by simpa using h)
  simpa using hall

end Flapjack
