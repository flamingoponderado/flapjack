import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Flapjack.Basis.Pure.MlList

/-!
# Exact HOL `wordSem` environment and stack helpers

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml:472-612`
(bead `flapjack-h29l.4`): `call_env`, `list_rearrange`, `key_val_compare`,
`env_to_list`, `push_env`, `pop_env`, the local `push_env_clock`/`pop_env_clock`,
`jump_exc`, `cut_names`, `cut_envs`, `cut_env`, `cut_state`, and
`cut_state_opt`.  These are over the tagged `WordSemStateFiniteExact`, with
the carrier translations of its `state` port (qualifier
`fmap_as_finite_support := [fpRegs, store]` and the same-module witness
below).

HOL standard-library operations are rendered by untagged Flapjack
infrastructure:
* `sptree` `toAList`, `fromAList`, `union` and `inter`: `sptToAList`,
  `sptFromAList`, `sptUnion` and `sptInter`;
* `domain s SUBSET domain t`: the decidable `sptSubsetLive` of the loopSem
  `cut_state` port;
* `OPTION_MAP2 MAX` and `OPTION_MAP2 $+`: `wordSemOptionMax` and
  `wordSemOptionAdd`;
* `LASTN n l = REVERSE (TAKE n (REVERSE l))`, `GENLIST f n`, and `EL`;
* `BIJ f (count n) (count n)`: the bounded `wordSemBijCount`.

`fromList2` is the tagged `sptFromList2`, and `mllist$sort` is the tagged
`Basis.Pure.MlList.sort`.
-/

namespace Flapjack

namespace WordSemEnvSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged state helpers of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEnvSupport

/-- HOL `OPTION_MAP2 MAX` (`optionTheory`) on `num option`.  Untagged Flapjack
    helper. -/
def wordSemOptionMax : Option Nat → Option Nat → Option Nat
  | some x, some y => some (max x y)
  | _, _ => none

/-- HOL `pred_set$BIJ f (count n) (count n)` (`pred_setScript.sml`, `BIJ_DEF`,
    `INJ_DEF`, `SURJ_DEF`).  The map sends `count n` into itself, is injective
    on `count n`, and hits every element of `count n`.  All quantifiers are
    bounded, so the proposition is decidable.  Untagged Flapjack helper (HOL
    source outside `cakeml/`). -/
def wordSemBijCount (f : Nat → Nat) (n : Nat) : Prop :=
  ((∀ x, x < n → f x < n) ∧ (∀ x, x < n → ∀ y, y < n → f x = f y → x = y)) ∧
    ((∀ x, x < n → f x < n) ∧ (∀ x, x < n → ∃ y, y < n ∧ f y = x))

instance wordSemBijCountDecidable (f : Nat → Nat) (n : Nat) :
    Decidable (wordSemBijCount f n) := by
  unfold wordSemBijCount
  infer_instance

/-- HOL `rich_list$LASTN_def`: `LASTN n xs = REVERSE (TAKE n (REVERSE xs))`.
    Untagged Flapjack helper (HOL source outside `cakeml/`). -/
def wordSemLastN {α : Type} (n : Nat) (xs : List α) : List α :=
  ((xs.reverse).take n).reverse

namespace WordSemStateFiniteExact

/-- Exact HOL `call_env_def` (`wordSemScript.sml:472-477`):
    `call_env args size s = s with <| locals := fromList2 args; locals_size :=
    size; stack_max := OPTION_MAP2 MAX s.stack_max (OPTION_MAP2 $+
    (stack_size s.stack) size) |>`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def callEnv {width : Nat} [NeZero width] {C : Type} {F : Type}
    (args : List (WordLocW width)) (size : Option Nat)
    (state : WordSemStateFiniteExact width C F) : WordSemStateFiniteExact width C F :=
  { state with
    locals := sptFromList2 args
    localsSize := size
    stackMax := wordSemOptionMax state.stackMax
      (wordSemOptionAdd (wordSemStackSize state.stack) size) }

end WordSemStateFiniteExact

/-- Exact HOL `list_rearrange_def` (`wordSemScript.sml:479-488`): if `mover`
    is a bijection of `count (LENGTH xs)`, return `GENLIST (\i. EL (mover i)
    xs) (LENGTH xs)`, otherwise return `xs` unchanged.  The guard puts every
    index `mover i` below `LENGTH xs`, and that bound proof is used for the
    index, so `EL` is never applied out of range (where HOL leaves it
    unspecified). -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "list_rearrange_def"]
def wordSemListRearrange {α : Type} (mover : Nat → Nat) (xs : List α) : List α :=
  if h : wordSemBijCount mover xs.length then
    (List.range xs.length).attach.map
      (fun ⟨i, hi⟩ => xs[mover i]'(h.1.1 i (List.mem_range.mp hi)))
  else xs

/-- Exact HOL `key_val_compare_def` (`wordSemScript.sml:492-501`):
    `(a > a') ∨ (a = a' ∧ case b of Word x => (case b' of Word y => x <= y | _
    => T) | Loc a b => case b' of Loc a' b' => (a > a') ∨ (a = a' ∧ b >= b') |
    _ => F)`.  HOL `<=` on words is the signed order, which is `BitVec.sle`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "key_val_compare_def"
  (words_as_type_indexed_bitvec)]
def wordSemKeyValCompare {width : Nat} [NeZero width]
    (x y : Nat × WordLocW width) : Bool :=
  let (a, b) := x
  let (a', b') := y
  decide (a > a') ||
    (decide (a = a') &&
      match b with
      | .word x => (match b' with | .word y => BitVec.sle x y | _ => true)
      | .loc a b => match b' with
        | .loc a' b' => decide (a > a') || (decide (a = a') && decide (b ≥ b'))
        | _ => false)

/-- Exact HOL `env_to_list_def` (`wordSemScript.sml:507-515`): sort `toAList
    env` with `key_val_compare`, rearrange by `bij_seq 0`, and return the
    shifted sequence `\n. bij_seq (n + 1)`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "env_to_list_def"
  (words_as_type_indexed_bitvec)]
def wordSemEnvToList {width : Nat} [NeZero width] (env : Spt (WordLocW width))
    (bijSeq : Nat → Nat → Nat) : List (Nat × WordLocW width) × (Nat → Nat → Nat) :=
  let mover := bijSeq 0
  let permute := fun n => bijSeq (n + 1)
  let l := sptToAList env
  let l := Basis.Pure.MlList.sort wordSemKeyValCompare l
  let l := wordSemListRearrange mover l
  (l, permute)

namespace WordSemStateFiniteExact

/-- Exact HOL `push_env_def` (`wordSemScript.sml:517-536`).  The kept-alive
    environments come from `cut_envs`: `FST envs` is saved as the non-GC list
    `toAList`, and `SND envs` goes through `env_to_list` with `s.permute`.
    `NONE` pushes a frame without a handler.  `SOME (w, h, l1, l2)` pushes the
    handler `SOME (s.handler, l1, l2)` and sets `handler := LENGTH s.stack`.
    In both cases `stack_max := OPTION_MAP2 MAX s.stack_max (stack_size stack)`
    and `permute` is updated. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def pushEnv {width : Nat} [NeZero width] {C : Type} {F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width)) :
    Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat) →
      WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F
  | none, state =>
      let l0 := sptToAList envs.1
      let (l, permute) := wordSemEnvToList envs.2 state.permute
      let stack := WordSemStackFrame.stackFrame state.localsSize l0 l none :: state.stack
      { state with
        stack := stack
        stackMax := wordSemOptionMax state.stackMax (wordSemStackSize stack)
        permute := permute }
  | some (_, _, l1, l2), state =>
      let l0 := sptToAList envs.1
      let (l, permute) := wordSemEnvToList envs.2 state.permute
      let handler := some (state.handler, l1, l2)
      let stack := WordSemStackFrame.stackFrame state.localsSize l0 l handler :: state.stack
      { state with
        stack := stack
        stackMax := wordSemOptionMax state.stackMax (wordSemStackSize stack)
        permute := permute
        handler := state.stack.length }

/-- Exact HOL `pop_env_def` (`wordSemScript.sml:538-547`).  Pop the top frame
    and restore `locals := union (fromAList e) (fromAList e0)` and
    `locals_size := m`.  A frame with a handler `SOME (n, _, _)` also restores
    `handler := n`.  An empty stack gives `NONE`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def popEnv {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : WordSemStateFiniteExact width C F) : Option (WordSemStateFiniteExact width C F) :=
  match state.stack with
  | .stackFrame m e0 e none :: xs =>
      some { state with
        locals := sptUnion (sptFromAList e) (sptFromAList e0), stack := xs, localsSize := m }
  | .stackFrame m e0 e (some (n, _, _)) :: xs =>
      some { state with
        locals := sptUnion (sptFromAList e) (sptFromAList e0), stack := xs, localsSize := m,
        handler := n }
  | _ => none

/-- Exact HOL local `push_env_clock` (`wordSemScript.sml:549-555`):
    `(push_env env b s).clock = s.clock`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem pushEnv_clock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (env : Spt (WordLocW width) × Spt (WordLocW width))
    (b : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) :
    (pushEnv env b s).clock = s.clock := by
  rcases b with _ | ⟨_, _, _, _⟩ <;> rfl

/-- Exact HOL local `pop_env_clock` (`wordSemScript.sml:557-563`):
    `pop_env s = SOME s1 ⇒ s1.clock = s.clock`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem popEnv_clock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s s1 : WordSemStateFiniteExact width C F) :
    popEnv s = some s1 → s1.clock = s.clock := by
  unfold popEnv
  split
  · intro h; cases h; rfl
  · intro h; cases h; rfl
  · intro h; cases h

/-- Exact HOL `jump_exc_def` (`wordSemScript.sml:565-576`).  When `s.handler <
    LENGTH s.stack`, inspect `LASTN (s.handler + 1) s.stack`.  If its head
    frame has a handler `SOME (n, l1, l2)`, return the state with `handler :=
    n`, the frame's `locals` union, `stack := xs` and `locals_size := m`,
    together with `l1` and `l2`.  Otherwise return `NONE`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def jumpExc {width : Nat} [NeZero width] {C : Type} {F : Type}
    (state : WordSemStateFiniteExact width C F) :
    Option (WordSemStateFiniteExact width C F × Nat × Nat) :=
  if state.handler < state.stack.length then
    match wordSemLastN (state.handler + 1) state.stack with
    | .stackFrame m e0 e (some (n, l1, l2)) :: xs =>
        some ({ state with
          handler := n
          locals := sptUnion (sptFromAList e) (sptFromAList e0)
          stack := xs
          localsSize := m }, l1, l2)
    | _ => none
  else none

end WordSemStateFiniteExact

/-- Exact HOL `cut_names_def` (`wordSemScript.sml:578-583`):
    `cut_names name_set env = if domain name_set SUBSET domain env then SOME
    (inter env name_set) else NONE`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "cut_names_def"]
def wordSemCutNames {α β : Type}
    (nameSet : Spt α) (env : Spt β) : Option (Spt β) :=
  if LoopSemStateFiniteExact.sptSubsetLive nameSet env then some (sptInter env nameSet)
  else none

/-- Exact HOL `cut_envs_def` (`wordSemScript.sml:585-590`): cut both name sets
    of a `cutsets` pair, failing if either cut fails. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "cut_envs_def"]
def wordSemCutEnvs {β : Type}
    (nameSets : WordLangCutsetsHOL) (env : Spt β) :
    Option (Spt β × Spt β) :=
  match wordSemCutNames nameSets.1 env, wordSemCutNames nameSets.2 env with
  | some e1, some e2 => some (e1, e2)
  | _, _ => none

/-- Exact HOL `cut_env_def` (`wordSemScript.sml:592-597`):
    `case cut_envs name_sets env of SOME (e1, e2) => SOME (union e2 e1) | _ =>
    NONE`. -/
@[hol "cakeml/compiler/backend/semantics/wordSemScript.sml" "cut_env_def"]
def wordSemCutEnv {β : Type}
    (nameSets : WordLangCutsetsHOL) (env : Spt β) :
    Option (Spt β) :=
  match wordSemCutEnvs nameSets env with
  | some (e1, e2) => some (sptUnion e2 e1)
  | _ => none

namespace WordSemStateFiniteExact

/-- Exact HOL `cut_state_def` (`wordSemScript.sml:600-605`):
    `case cut_env names s.locals of NONE => NONE | SOME env => SOME (s with
    locals := env)`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def cutState {width : Nat} [NeZero width] {C : Type} {F : Type}
    (names : WordLangCutsetsHOL) (state : WordSemStateFiniteExact width C F) :
    Option (WordSemStateFiniteExact width C F) :=
  match wordSemCutEnv names state.locals with
  | none => none
  | some env => some { state with locals := env }

/-- Exact HOL `cut_state_opt_def` (`wordSemScript.sml:607-612`):
    `case names of NONE => SOME s | SOME names => cut_state names s`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def cutStateOpt {width : Nat} [NeZero width] {C : Type} {F : Type}
    (names : Option WordLangCutsetsHOL) (state : WordSemStateFiniteExact width C F) :
    Option (WordSemStateFiniteExact width C F) :=
  match names with
  | none => some state
  | some names => cutState names state

end WordSemStateFiniteExact

end Flapjack
