module

public import Flapjack.Compiler.Backend.WordToStackRegFormat
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Flapjack.Compiler.Backend.WordToStack.Proofs.ALookupMap
public import Flapjack.Compiler.Backend.WordToStack.Proofs.StackSuffix
public import Flapjack.Compiler.Backend.WordAlloc.Proofs.RemoveDead
public import Flapjack.Misc.ListEl
public import Flapjack.Misc.Option
public import Mathlib.Data.List.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# Small helper lemmas of `word_to_stackProofScript.sml`

The HOL Word-to-Stack correctness script keeps a group of small generic
support facts (definition unfoldings, arithmetic, list/option and quantifier
lemmas) that its `comp_correct` proof uses throughout. This module ports that
group beside the other theorem groups of the counterpart. Each declaration is
tagged with its original HOL name; the renderings (`holHd`, `holEl`, `holLast`,
`holThe`) follow the reviewed HOL `ARB` conventions.
-/

namespace Flapjack.WordToStackProofs

open Flapjack
open Flapjack.Compiler.Backend.WordToStackRegFormat
open Flapjack.Compiler.Backend.WordToStack
open Flapjack.Compiler.Backend.StackLang (ProgM)
open Flapjack.WordAlloc

/-- Exact HOL `copy_ret_F` (`word_to_stackProofScript.sml:88-96`): in the
non-perf configuration `handler_slots F = 3`, so the return-copy program
unfolds with `f + 3`. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "copy_ret_F"]
theorem copyRetF {α β γ : Type} (isHandle : Bool) (k f : Nat) (f' : γ)
    (vs : List β) (kont : ProgM α) :
    copyRet false isHandle (k, f, f') vs kont =
      let n := numStackRet k vs
      if n = 0 then kont
      else .seq (copyRetAux k (if isHandle then f + 3 else f) n) (seqStackFree n kont) := by
  rfl

/-- Exact HOL `LASTN_HD` (`word_to_stackProofScript.sml:291-301`): the head of a
suffix is the corresponding element, with HOL's unspecified values for the
empty suffix and the past-the-end index. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LASTN_HD"
  (total_function_inhabitants := [α])]
theorem lastNHd {α : Type} [Nonempty α] (ls : List α) (x : Nat) (hx : x ≤ ls.length) :
    holHd (wordSemLastN x ls) = holEl (ls.length - x) ls := by
  cases x with
  | zero =>
    have hdrop : wordSemLastN 0 ls = [] := by
      rw [lastNDrop2]
      simp [List.drop_eq_nil_of_le]
    rw [hdrop]
    simp [holHd, holEl_of_length_le]
  | succ n =>
    have hk : ls.length - (n + 1) < ls.length := by omega
    rw [lastNDrop2, List.drop_eq_getElem_cons hk, holEl_eq_getElem _ _ hk]
    simp [holHd]

/-- Exact HOL `EL_REVERSE_REWRITE` (`word_to_stackProofScript.sml:2601-2606`):
reversed indexing inside a suffix. HOL's single conjunction premise
`n < LENGTH l ∧ k < n` is kept as one hypothesis in HOL's order. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EL_REVERSE_REWRITE"
  (total_function_inhabitants := [α])]
theorem elReverseRewrite {α : Type} [Nonempty α] (l : List α) (n k : Nat)
    (h : n < l.length ∧ k < n) :
    holEl (l.length - n + k) l = holEl (n - k - 1) l.reverse := by
  obtain ⟨hn, hk⟩ := h
  have h1 : l.length - n + k < l.length := by omega
  have h2 : n - k - 1 < l.reverse.length := by
    simp
    omega
  rw [holEl_eq_getElem _ _ h1, holEl_eq_getElem _ _ h2]
  rw [List.getElem_reverse]
  congr 1
  omega

/-- Exact HOL `ALOOKUP_IFF_MEM` (`word_to_stackProofScript.sml:2628-2632`): with
distinct keys, a successful lookup is exactly membership of the pair. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "ALOOKUP_IFF_MEM"]
theorem alookupIffMem {α β : Type} (l : List (α × β)) (q : α) (r : β)
    (hd : (l.map Prod.fst).Nodup) :
    keyLookup l q = some r ↔ (q, r) ∈ l := by
  classical
  induction l with
  | nil => simp [keyLookup, holAlookup]
  | cons entry l ih =>
    rcases entry with ⟨a, b⟩
    have hdcons : (a :: l.map Prod.fst).Nodup := by simpa using hd
    have hnot : a ∉ l.map Prod.fst := (List.nodup_cons.mp hdcons).1
    have hd' : (l.map Prod.fst).Nodup := (List.nodup_cons.mp hdcons).2
    by_cases hqa : q = a
    · rw [hqa]
      have hlook : keyLookup ((a, b) :: l) a = some b := by
        simp [keyLookup, holAlookup]
      constructor
      · intro hlk
        rw [hlook] at hlk
        have hrb : b = r := Option.some.inj hlk
        subst hrb
        exact List.mem_cons_self ..
      · intro hmem
        rcases List.mem_cons.mp hmem with hhead | htail
        · have hrb : r = b := (Prod.mk.inj hhead).2
          rw [hlook, hrb]
        · exact absurd (List.mem_map.mpr ⟨(a, r), htail, rfl⟩) hnot
    · have haq : a ≠ q := fun h => hqa h.symm
      simp only [keyLookup, holAlookup, if_neg haq]
      constructor
      · intro hlk
        exact List.mem_cons_of_mem (a, b) ((ih hd').mp hlk)
      · intro hmem
        rcases List.mem_cons.mp hmem with hhead | htail
        · exact absurd (Prod.mk.inj hhead).1 hqa
        · exact (ih hd').mpr htail

/-- Exact HOL `LAST_add_ret_loc` (`word_to_stackProofScript.sml:3307-3311`): the
appended return location does not change the last argument. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "LAST_add_ret_loc"]
theorem lastAddRetLoc {width : Nat} [NeZero width] {β γ δ : Type}
    (ret : Option (β × γ × δ × Nat × Nat)) (args' : List (WordLocW width))
    (hne : args' ≠ []) :
    holLast (wordSemAddRetLoc ret args') = holLast args' := by
  cases ret with
  | none => rfl
  | some r =>
    rcases r with ⟨a, b, c, l1, l2⟩
    cases args' with
    | nil => simp at hne
    | cons x xs =>
      cases xs with
      | nil => simp [wordSemAddRetLoc, holLastCons]
      | cons y zs => simp [wordSemAddRetLoc, holLastCons]

/-- Exact HOL `MAP_o_THE_FILTER_IS_SOME` (`word_to_stackProofScript.sml:3431-3435`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_o_THE_FILTER_IS_SOME"
  (total_function_inhabitants := [α, β])]
theorem mapOTheFilterIsSome {α β : Type} [Nonempty α] [Nonempty β] (f : β → α)
    (ls : List (Option β)) :
    (ls.filter Option.isSome).map (fun o => f (holThe o)) =
      (ls.filter Option.isSome).map (fun o => holThe (Option.map f o)) := by
  induction ls with
  | nil => rfl
  | cons o ls ih =>
    cases o with
    | none => simpa using ih
    | some x => simpa [holThe] using ih

/-- Exact HOL `MAP_OPTION_MAP_FILTER_IS_SOME`
(`word_to_stackProofScript.sml:3438-3442`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_OPTION_MAP_FILTER_IS_SOME"]
theorem mapOptionMapFilterIsSome {α : Type} (f : α → α) (ls : List (Option α)) :
    (ls.filter Option.isSome).map (Option.map f) =
      (ls.map (Option.map f)).filter Option.isSome := by
  induction ls with
  | nil => rfl
  | cons o ls ih =>
    cases o with
    | none => simpa using ih
    | some x => simpa using ih

/-- Exact HOL `MAP_FILTER_IS_SOME` (`word_to_stackProofScript.sml:3445-3449`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAP_FILTER_IS_SOME"
  (total_function_inhabitants := [β])]
theorem mapFilterIsSome {α β : Type} [Nonempty β] (f : Option β → α)
    (ls : List (Option β)) :
    (ls.filter Option.isSome).map f =
      (ls.filter Option.isSome).map (fun o => f (some (holThe o))) := by
  induction ls with
  | nil => rfl
  | cons o ls ih =>
    cases o with
    | none => simpa using ih
    | some x => simpa [holThe] using ih

/-- Exact HOL `PAIR_MAP_SOME_SWAP` (`word_to_stackProofScript.sml:3484-3487`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "PAIR_MAP_SOME_SWAP"]
theorem pairMapSomeSwap {α β γ δ : Type} (f : α → γ) (g : β → δ) :
    Prod.map some some ∘ Prod.map f g =
      Prod.map (Option.map f) (Option.map g) ∘ Prod.map some some := by
  funext p
  rcases p with ⟨a, b⟩
  rfl

/-- Exact HOL `IS_SOME_o_OPTION_MAP` (`word_to_stackProofScript.sml:3490-3493`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "IS_SOME_o_OPTION_MAP"]
theorem isSomeOptionMap {α β : Type} (f : α → β) :
    Option.isSome ∘ Option.map f = Option.isSome := by
  funext o
  cases o <;> rfl

/-- HOL `OPTION_MAP2` (`optionTheory`): `OPTION_MAP2 f (SOME x) (SOME y) =
SOME (f x y)`, otherwise `NONE`. Untagged Flapjack rendering: the HOL source is
outside `cakeml/`, and the tree otherwise carries only the `num`
specializations `wordSemOptionAdd` and `wordSemOptionMax`. -/
def optionMap2 {α β γ : Type} (f : α → β → γ) : Option α → Option β → Option γ
  | some x, some y => some (f x y)
  | _, _ => none

/-- Exact HOL `IS_SOME_OPTION_MAP2_EQ` (`word_to_stackProofScript.sml:5439-5443`):
`OPTION_MAP2` is defined exactly when both arguments are. The typed capture
(`f :β -> γ -> α`, `A :β option`, `B :γ option`) fixes the binder order
`f`, `A`, `B`; HOL's single `⇔` conclusion carries its `∧` on the right, so
there is no premise to group. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "IS_SOME_OPTION_MAP2_EQ"]
theorem isSomeOptionMap2Eq {α β γ : Type} (f : β → γ → α) (A : Option β) (B : Option γ) :
    (optionMap2 f A B).isSome ↔ A.isSome ∧ B.isSome := by
  cases A <;> cases B <;> simp [optionMap2]

/-- Exact HOL `DROP_SUB` (`word_to_stackProofScript.sml:5446-5452`): a suffix of a
prefix is the front part of the suffix. Binders follow the typed capture
(`a`, `ls`, `b`) and HOL's single conjunction premise `a ≤ LENGTH ls ∧ b ≤ a`
is one hypothesis in HOL's order. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_SUB"]
theorem dropSub {α : Type} (a : Nat) (ls : List α) (b : Nat)
    (h : a ≤ ls.length ∧ b ≤ a) :
    ls.drop (a - b) = (ls.take a).drop (a - b) ++ ls.drop a := by
  obtain ⟨ha, hb⟩ := h
  rw [← List.take_append_drop a ls]
  rw [List.drop_append_of_le_length]
  · simp
  · rw [List.length_take]
    omega

/-- Exact HOL `DROP_SUB2` (`word_to_stackProofScript.sml:5456-5462`): HOL's single
conjunction premise `b ≤ a ∧ a = LENGTH ls` is one hypothesis in HOL's order. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "DROP_SUB2"]
theorem dropSub2 {α : Type} (a : Nat) (ls : List α) (b : Nat)
    (h : b ≤ a ∧ a = ls.length) :
    ∃ rest, ls.drop (a - b) = rest ∧ rest.length = b := by
  obtain ⟨hb, ha⟩ := h
  refine ⟨ls.drop (a - b), rfl, ?_⟩
  rw [List.length_drop]
  omega

/-- Exact HOL `SUB_ADD_EQ` (`word_to_stackProofScript.sml:6600-6603`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SUB_ADD_EQ"]
theorem subAddEq (a b : Nat) (h : a ≤ b) : a + (b - a) = b := by
  omega

/-- Exact HOL `EXISTS_PULL_FORALL1` (`word_to_stackProofScript.sml:6925-6929`):
the quantifier swap under a value equality guard. HOL's `Abbrev` is the
identity marker, so the guard is the plain equality. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EXISTS_PULL_FORALL1"]
theorem existsPullForall1 {α β : Type} (P : β) (Q : α → β → Prop) :
    (∃ x, ∀ y, y = P → Q x y) ↔ (∀ y, y = P → ∃ x, Q x y) := by
  constructor
  · rintro ⟨x, hx⟩ y hy
    exact ⟨x, hx y hy⟩
  · intro h
    obtain ⟨x, hx⟩ := h P rfl
    refine ⟨x, ?_⟩
    intro y hy
    subst hy
    exact hx

/-- Exact HOL `EXISTS_PULL_FORALL2` (`word_to_stackProofScript.sml:6931-6935`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EXISTS_PULL_FORALL2"]
theorem existsPullForall2 {α β γ : Type} (P : β × γ) (Q : α → β → γ → Prop) :
    (∃ x, ∀ y z, P = (y, z) → Q x y z) ↔
      (∀ y z, P = (y, z) → ∃ x, Q x y z) := by
  constructor
  · rintro ⟨x, hx⟩ y z hp
    exact ⟨x, hx y z hp⟩
  · intro h
    obtain ⟨p, q⟩ := P
    obtain ⟨x, hx⟩ := h p q rfl
    refine ⟨x, ?_⟩
    intro y z hyz
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hyz
    exact hx

/-- Exact HOL `EXISTS_PULL_FORALL3` (`word_to_stackProofScript.sml:6937-6941`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EXISTS_PULL_FORALL3"]
theorem existsPullForall3 {α β γ δ : Type} (P : β × γ × δ)
    (Q : α → β → γ → δ → Prop) :
    (∃ x, ∀ y z a, P = (y, z, a) → Q x y z a) ↔
      (∀ y z a, P = (y, z, a) → ∃ x, Q x y z a) := by
  constructor
  · rintro ⟨x, hx⟩ y z a hp
    exact ⟨x, hx y z a hp⟩
  · intro h
    obtain ⟨p, q, r⟩ := P
    obtain ⟨x, hx⟩ := h p q r rfl
    refine ⟨x, ?_⟩
    intro y z a hyz
    simp only [Prod.mk.injEq] at hyz
    obtain ⟨rfl, rfl, rfl⟩ := hyz
    exact hx

/-- Exact HOL `SUB_SUB_SUB_MAX` (`word_to_stackProofScript.sml:7589-7593`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SUB_SUB_SUB_MAX"]
theorem subSubSubMax (a b c : Nat) : a - b - (c - b) = a - Nat.max b c := by
  have hsum : b + (c - b) = Nat.max b c := by
    rcases Nat.le_total b c with h | h
    · rw [Nat.add_sub_cancel' h]
      simp [h]
    · rw [Nat.sub_eq_zero_of_le h, Nat.add_zero]
      simp [h]
  rw [← hsum, Nat.sub_sub]

/-- Exact HOL `MAX_LE` (`word_to_stackProofScript.sml:7596-7599`). -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "MAX_LE"]
theorem maxLe (a b : Nat) (h : a ≤ b) : Nat.max a b = b := by
  simp [h]

/-- Exact HOL `EVEN_DIV_2_props` (`word_to_stackProofScript.sml:10944-10955`):
halving is injective on even numbers and keeps them nonzero. HOL's single
conjunction premise `a MOD 2 = 0 ∧ b MOD 2 = 0` is one hypothesis in HOL's
order. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "EVEN_DIV_2_props"]
theorem evenDiv2Props (a b : Nat) (h : a % 2 = 0 ∧ b % 2 = 0) :
    (a ≠ b → a / 2 ≠ b / 2) ∧ (a ≠ 0 → a / 2 ≠ 0) := by
  obtain ⟨ha, hb⟩ := h
  constructor
  · intro hne hdiv
    exact hne (by omega)
  · intro hne hdiv
    exact hne (by omega)

/-- Exact HOL `with_same_locals` (`word_to_stackProofScript.sml:3127`): rewriting
`locals` with its own value leaves the wordSem state unchanged. The typed
capture (`(s :(α, β, γ) state) with locals := s.locals = s`) has a single state
binder and an identity statement. The carrier `WordSemStateFiniteExact width C F`
carries `[NeZero width]` and mentions `BitVec width` in its `memory` field, so the
only carrier difference is the standard type-indexed word translation; `locals`
is an `Spt` (sptree), not a HOL `|->` finite map, so no finite-map qualifier
applies. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "with_same_locals"
  (words_as_type_indexed_bitvec)]
theorem withSameLocalsWordSem {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) :
    ({ s with locals := s.locals } : WordSemStateFiniteExact width C F) = s := by
  rfl

/-- Exact HOL `map_var_def` (`word_to_stackProofScript.sml:4054-4062`): renaming
the variables of an expression. The typed capture
(`map_var_def_typed`) states the six source equations; Lean's constructor order
(`const`, `var`, `lookup`, `load`, `op`, `shift`) differs from HOL's clause order
(`Var`, `Load`, `Op`, `Shift`, `Const`, `Lookup`) but the equation set is the
same. The value type is the reviewed `exp` carrier's `α` parameter, exactly as
in that carrier's own reviewed row, so no width-indexed carrier occurs in this
definition's signature. The `op` clause recurses through `List.map`, so the
definition uses a `sizeOf` measure rather than structural recursion. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "map_var_def"]
def mapVar {α : Type} (f : Nat → Nat) : WordLangExpHOL α → WordLangExpHOL α
  | .const c => .const c
  | .var n => .var (f n)
  | .lookup s => .lookup s
  | .load e => .load (mapVar f e)
  | .op wop ls => .op wop (ls.map (mapVar f))
  | .shift sh e1 e2 => .shift sh (mapVar f e1) (mapVar f e2)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  · have h := List.sizeOf_lt_of_mem (by assumption)
    omega
  all_goals omega

end Flapjack.WordToStackProofs
