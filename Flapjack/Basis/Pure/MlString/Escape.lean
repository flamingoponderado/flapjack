module

public import Flapjack.Basis.Pure.MlString.Ops
public import Flapjack.Misc.AppList

@[expose] public section

/-!
# Cake `mlstring` escaping and `app_list` optimisation

Lean counterparts of the escaping helpers, the `app_list_ann` annotation
datatype, its size-driven annotation pass and `empty_ffi` from
`cakeml/basis/pure/mlstringScript.sml`.  HOL `char` literals are `BitVec 8`
values and `strlit s` is `.implode (ofString s).explode`, and `misc$append` is
`appListAppend` (`Flapjack/Misc/AppList.lean`).
-/

namespace Flapjack.Basis.Pure.MlString

open MlString Flapjack.Basis.Pure.MlList

/-- Original `char_escape_seq_def`: the escape sequence of a character, if any. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "char_escape_seq_def"]
def charEscapeSeq (c : HolChar) : Option MlString :=
  if c = 9 then some (ofString "\\t")
  else if c = 10 then some (ofString "\\n")
  else if c = 92 then some (ofString "\\\\")
  else if c = 34 then some (ofString "\\\"")
  else none

/-- Original `char_escaped_def`: the characters an escape sequence expands to. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "char_escaped_def"]
def charEscaped (c : HolChar) : List HolChar :=
  match charEscapeSeq c with
  | none => [c]
  | some s => explode s

/-- Original `escape_str_def`: a quoted string with its characters escaped. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "escape_str_def"]
def escapeStr (s : MlString) : MlString :=
  .implode ((ofString "\"").explode ++ ((explode s).map charEscaped).flatten ++
    (ofString "\"").explode)

/-- Original `escape_char_def`: a quoted character with its escape sequence. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "escape_char_def"]
def escapeChar (c : HolChar) : MlString :=
  .implode ((ofString "#\"").explode ++ charEscaped c ++ (ofString "\"").explode)

/-- Original `ALL_DISTINCT_MAP_implode`: distinct strings stay distinct. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "ALL_DISTINCT_MAP_implode"]
theorem nodup_map_implode (ls : List (List HolChar)) (h : ls.Nodup) :
    (ls.map MlString.implode).Nodup := by
  induction ls with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro hm
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
    have hyx : y = x := by simpa using congrArg explode hxy
    exact h.1 (hyx ▸ hy)

/-- Original `ALL_DISTINCT_MAP_explode`: exploding is distinctness-preserving. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "ALL_DISTINCT_MAP_explode"]
theorem nodup_map_explode_iff (ls : List MlString) :
    (ls.map explode).Nodup ↔ ls.Nodup := by
  constructor
  · intro h
    induction ls with
    | nil => exact List.nodup_nil
    | cons x xs ih =>
      rw [List.map_cons, List.nodup_cons] at h
      rw [List.nodup_cons]
      refine ⟨?_, ih h.2⟩
      intro hx
      exact h.1 (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h
    induction ls with
    | nil => exact List.nodup_nil
    | cons x xs ih =>
      rw [List.nodup_cons] at h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih h.2⟩
      intro hm
      obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hm
      have hyx : y = x := (explode_inj y x).mp hxy
      exact h.1 (hyx ▸ hy)

/-- HOL `app_list_ann = BigList ('a list) | BigAppend app_list_ann app_list_ann
| Small ('a app_list)`. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "app_list_ann"]
inductive AppListAnn (α : Type) where
  /-- HOL `BigList ('a list)`. -/
  | bigList (values : List α) : AppListAnn α
  /-- HOL `BigAppend app_list_ann app_list_ann`. -/
  | bigAppend (left right : AppListAnn α) : AppListAnn α
  /-- HOL `Small ('a app_list)`. -/
  | small (value : AppList α) : AppListAnn α
  deriving Repr

/-- Original `sum_sizes_def`: the accumulated string size of a list. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "sum_sizes_def"]
def sumSizes : List MlString → Nat → Nat
  | [], k => k
  | l :: ls, k => sumSizes ls (strlen l + k)

/-- The `size_limit` overload of the source is the local `2048`. -/
def appListSizeLimit : Nat := 2048

/-- Original `make_app_list_ann_def`: annotate small and large concatenations. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "make_app_list_ann_def"]
def makeAppListAnn : AppList MlString → AppListAnn MlString × Nat
  | .nil => (.small .nil, 0)
  | .append l1 l2 =>
    let (x1, n1) := makeAppListAnn l1
    let (x2, n2) := makeAppListAnn l2
    let n := n1 + n2
    if n < appListSizeLimit then (.small (.append l1 l2), n)
    else (.bigAppend x1 x2, n)
  | .list ls =>
    let n := sumSizes ls 0
    if n < appListSizeLimit then (.small (.list ls), n)
    else (.bigList ls, n)

/-- Original `shrink_def`: drop the annotations, keeping the tree shape. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "shrink_def"]
def shrink : AppListAnn MlString → AppList MlString
  | .small t => .list [concat (appListAppend t)]
  | .bigList ls => .list ls
  | .bigAppend l1 l2 => .append (shrink l1) (shrink l2)

/-- Original `str_app_list_opt_def`: annotate, then shrink back. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "str_app_list_opt_def"]
def strAppListOpt (l : AppList MlString) : AppList MlString :=
  let (t, _) := makeAppListAnn l
  shrink t

/-- Original `concat_sing`: a one-element concatenation is its element. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "concat_sing"]
theorem concat_sing (x : MlString) : concat [x] = x := by
  cases x
  simp [concat]

/-- Original `str_app_list_opt_thm`: annotating and shrinking keeps the
    concatenated characters. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "str_app_list_opt_thm"]
theorem strAppListOpt_concat (l : AppList MlString) :
    concat (appListAppend (strAppListOpt l)) = concat (appListAppend l) := by
  induction l with
  | nil =>
      simp [strAppListOpt, makeAppListAnn, shrink, appListAppend, appendAux, concat]
  | append l1 l2 ih1 ih2 =>
      generalize h1 : makeAppListAnn l1 = a1
      obtain ⟨x1, n1⟩ := a1
      generalize h2 : makeAppListAnn l2 = a2
      obtain ⟨x2, n2⟩ := a2
      simp only [strAppListOpt, makeAppListAnn, h1, h2]
      by_cases hn : n1 + n2 < appListSizeLimit
      · rw [if_pos hn]
        dsimp only
        simp only [shrink, appListAppend, appendAux, concat, List.map_cons, List.map_nil,
          List.flatten_cons, List.flatten_nil, List.append_nil]
      · rw [if_neg hn]
        dsimp only
        simp only [shrink]
        rw [(appListAppend_thm_sameType (shrink x1) (shrink x2) ([] : List MlString)).1]
        rw [(appListAppend_thm_sameType l1 l2 ([] : List MlString)).1]
        rw [concat_append, concat_append]
        have hs1 : strAppListOpt l1 = shrink x1 := by
          simp only [strAppListOpt, h1]
        have hs2 : strAppListOpt l2 = shrink x2 := by
          simp only [strAppListOpt, h2]
        rw [← hs1, ← hs2, ih1, ih2]
  | list ls =>
      generalize h : makeAppListAnn (.list ls) = a
      obtain ⟨x, n⟩ := a
      simp only [strAppListOpt, makeAppListAnn]
      split
      · simp only [shrink, appListAppend, appendAux, concat, List.map_cons, List.map_nil,
          List.flatten_cons, List.flatten_nil, List.append_nil]
      · simp only [shrink, appListAppend, appendAux, concat]

/-- Original `empty_ffi_def`: the empty FFI call has no result. -/
@[hol "cakeml/basis/pure/mlstringScript.sml" "empty_ffi_def"]
def emptyFfi (_s : MlString) : Unit := ()

end Flapjack.Basis.Pure.MlString
