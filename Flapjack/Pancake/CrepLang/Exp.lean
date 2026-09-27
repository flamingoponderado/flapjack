import Flapjack.Pancake.CrepLang
import Flapjack.Basis.Pure.MlString

/-!
Exact width-indexed carrier for the Crepe expression syntax.

`cakeml/pancake/crepLangScript.sml:26-37` defines

```
Datatype:
  exp = Const ('a word)
      | Var varname
      | Load exp
      | Load32 exp
      | LoadByte exp
      | LoadGlob  (5 word)
      | Op binop (exp list)
      | Crepop crepop (exp list)
      | Cmp cmp exp exp
      | Shift shift exp exp
      | BaseAddr
      | TopAddr
```

The production `Flapjack.CrepExp (α)` in `Flapjack/Pancake/CrepLang.lean` is
generic over `α` and therefore a strict generalisation of HOL's word-indexed
`exp`; it stays untagged. `CrepExpHOL` is the exact carrier: the word type is
`BitVec width` with `[NeZero width]`, exactly as HOL's `'a word` becomes a
non-empty `BitVec` dimension.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString

/-- Exact port of `crepLang$exp` (`cakeml/pancake/crepLangScript.sml:26-37`):
the `'a word` payload is the width-indexed `BitVec width` and `varname` is
`Nat`. -/
@[hol "cakeml/pancake/crepLangScript.sml" "exp"]
inductive CrepExpHOL (width : Nat) [NeZero width] where
  | const (value : BitVec width)
  | var (name : Nat)
  | load (address : CrepExpHOL width)
  | load32 (address : CrepExpHOL width)
  | loadByte (address : CrepExpHOL width)
  | loadGlob (address : BitVec 5)
  | op (operator : BinOp) (args : List (CrepExpHOL width))
  | crepOp (operator : CrepOp) (args : List (CrepExpHOL width))
  | cmp (operator : Cmp) (left right : CrepExpHOL width)
  | shift (operator : Shift) (left right : CrepExpHOL width)
  | baseAddr
  | topAddr
  deriving Repr

/-- Production-to-HOL direction: forget the exact carrier. -/
def crepExpToHOL {width : Nat} [NeZero width] : CrepExp (BitVec width) → CrepExpHOL width
  | .const value => .const value
  | .var name => .var name
  | .load address => .load (crepExpToHOL address)
  | .load32 address => .load32 (crepExpToHOL address)
  | .loadByte address => .loadByte (crepExpToHOL address)
  | .loadGlob address => .loadGlob address
  | .op operator args => .op operator (args.map crepExpToHOL)
  | .crepOp operator args => .crepOp operator (args.map crepExpToHOL)
  | .cmp operator left right => .cmp operator (crepExpToHOL left) (crepExpToHOL right)
  | .shift operator left right => .shift operator (crepExpToHOL left) (crepExpToHOL right)
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr
termination_by e => sizeOf e
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (rename_i h; simp_all only [CrepExp.op.sizeOf_spec, CrepExp.crepOp.sizeOf_spec];
       have := List.sizeOf_lt_of_mem h; omega)

/-- HOL-to-production direction: the exact carrier is a `CrepExp` at the same
width. -/
def crepExpOfHOL {width : Nat} [NeZero width] : CrepExpHOL width → CrepExp (BitVec width)
  | .const value => .const value
  | .var name => .var name
  | .load address => .load (crepExpOfHOL address)
  | .load32 address => .load32 (crepExpOfHOL address)
  | .loadByte address => .loadByte (crepExpOfHOL address)
  | .loadGlob address => .loadGlob address
  | .op operator args => .op operator (args.map crepExpOfHOL)
  | .crepOp operator args => .crepOp operator (args.map crepExpOfHOL)
  | .cmp operator left right => .cmp operator (crepExpOfHOL left) (crepExpOfHOL right)
  | .shift operator left right => .shift operator (crepExpOfHOL left) (crepExpOfHOL right)
  | .baseAddr => .baseAddr
  | .topAddr => .topAddr
termination_by e => sizeOf e
decreasing_by
  simp_wf
  all_goals first
    | decreasing_trivial
    | (rename_i h; simp_all only [CrepExpHOL.op.sizeOf_spec, CrepExpHOL.crepOp.sizeOf_spec];
       have := List.sizeOf_lt_of_mem h; omega)

mutual
  /-- Exact-carrier port of HOL `crepLang$var_cexp_def` for `CrepExpHOL`.
  It lives beside the exact `CrepExpHOL` syntax carrier, matching the source
  script's `crepLangScript.sml` counterpart.  It is expected to agree with the
  production width-indexed `crepExpVarsW` under the `crepExpToHOL` codec
  (`crepExpVarsW e = crepExpVarsHOL (crepExpToHOL e)`); that bridge is tracked
  by a follow-up bead (flapjack-jlj3.3). -/
  @[hol "cakeml/pancake/crepLangScript.sml" "var_cexp_def"]
  def crepExpVarsHOL {width : Nat} [NeZero width] : CrepExpHOL width → List Nat
    | .const _ => []
    | .var name => [name]
    | .load address | .load32 address | .loadByte address => crepExpVarsHOL address
    | .loadGlob _ => []
    | .op _ expressions | .crepOp _ expressions => crepExpVarsHOLList expressions
    | .cmp _ left right | .shift _ left right =>
        crepExpVarsHOL left ++ crepExpVarsHOL right
    | .baseAddr | .topAddr => []

  /-- Flapjack-only list recursion helper for the exact `var_cexp` port; HOL
  has no separately named list helper declaration. -/
  def crepExpVarsHOLList {width : Nat} [NeZero width] :
      List (CrepExpHOL width) → List Nat
    | [] => []
    | expression :: expressions =>
        crepExpVarsHOL expression ++ crepExpVarsHOLList expressions
end

/-- Flapjack-only recursion bridge between the helper and `List.flatMap`; no
separate HOL declaration. -/
theorem crepExpVarsHOLList_eq_flatMap {width : Nat} [NeZero width]
    (expressions : List (CrepExpHOL width)) :
    crepExpVarsHOLList expressions = expressions.flatMap crepExpVarsHOL := by
  induction expressions with
  | nil => rfl
  | cons expression expressions ih => simp [crepExpVarsHOLList, ih]

@[simp] theorem crepExpToHOL_crepExpOfHOL {width : Nat} [NeZero width] :
    (e : CrepExpHOL width) → crepExpToHOL (crepExpOfHOL e) = e := by
  intro e
  fun_induction crepExpOfHOL e <;> simp_all [crepExpToHOL]
  case case7 operator args ih =>
    have h : List.map (crepExpToHOL ∘ crepExpOfHOL) args = List.map id args :=
      List.map_congr_left (fun x hx => ih x hx)
    simpa [Function.comp_apply] using h
  case case8 operator args ih =>
    have h : List.map (crepExpToHOL ∘ crepExpOfHOL) args = List.map id args :=
      List.map_congr_left (fun x hx => ih x hx)
    simpa [Function.comp_apply] using h

@[simp] theorem crepExpOfHOL_crepExpToHOL {width : Nat} [NeZero width] :
    (e : CrepExp (BitVec width)) → crepExpOfHOL (crepExpToHOL e) = e := by
  intro e
  fun_induction crepExpToHOL e <;> simp_all [crepExpOfHOL]
  case case7 operator args ih =>
    have h : List.map (crepExpOfHOL ∘ crepExpToHOL) args = List.map id args :=
      List.map_congr_left (fun x hx => ih x hx)
    simpa [Function.comp_apply] using h
  case case8 operator args ih =>
    have h : List.map (crepExpOfHOL ∘ crepExpToHOL) args = List.map id args :=
      List.map_congr_left (fun x hx => ih x hx)
    simpa [Function.comp_apply] using h

/-! Exact width-indexed port of HOL `crepLang$load_shape_def` over the faithful
    `CrepExpHOL` carrier. Keep the production `loadShapeBytesW` adapter
    untagged; `loadShapeBytesHOLW_toProduction` below proves that its output is
    the decoded result of this exact definition. -/
@[hol "cakeml/pancake/crepLangScript.sml" "load_shape_def" (words_as_type_indexed_bitvec)]
def loadShapeBytesHOLW {width : Nat} [NeZero width]
    (address : BitVec width) (count : Nat) (value : CrepExpHOL width) :
    List (CrepExpHOL width) :=
  match count with
  | 0 => []
  | count + 1 =>
      let loaded := if address == 0 then .load value
        else .load (.op .add [value, .const address])
      loaded :: loadShapeBytesHOLW
        (address + BitVec.ofNat width (width / 8)) count value
termination_by count

/-- The executed production width wrapper agrees with exact HOL
    `load_shape_def` after decoding its exact `CrepExpHOL` result. -/
theorem loadShapeBytesHOLW_toProduction {width : Nat} [NeZero width]
    (address : BitVec width) (count : Nat) (value : CrepExpHOL width) :
    (loadShapeBytesHOLW address count value).map crepExpOfHOL =
    loadShapeBytesW address count (crepExpOfHOL value) := by
  induction count generalizing address with
  | zero => simp [loadShapeBytesHOLW, loadShapeBytesW, loadShapeBytes]
  | succ count ih =>
      simp only [loadShapeBytesHOLW, loadShapeBytesW, loadShapeBytes,
        List.map_cons]
      rw [ih]
      congr 1
      simp only [beq_iff_eq]
      by_cases hzero : address = 0
      · rw [if_pos hzero, if_pos hzero]
        simp [crepExpOfHOL]
      · rw [if_neg hzero, if_neg hzero]
        simp [crepExpOfHOL]

end Flapjack
