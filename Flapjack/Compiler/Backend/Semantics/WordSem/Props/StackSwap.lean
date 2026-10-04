import Flapjack.Compiler.Backend.Semantics.WordSem.Props.StackEq
import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport

/-!
# wordProps stack-swap lemmas

Counterpart of `cakeml/compiler/backend/semantics/wordPropsScript.sml:1889-2160`:
symmetry and transitivity of `s_key_eq`/`s_val_eq`, their length facts, and the
garbage-collector and `push_env`/`pop_env` stack-swap theorems over the exact
WordSem carriers.
-/

namespace Flapjack

namespace WordSemStackEq

namespace StackSwapWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end StackSwapWitnesses

open StackSwapWitnesses

/-- Exact HOL `s_frame_key_eq_trans` (`wordPropsScript.sml:1889-1894`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_key_eq_trans"
  (words_as_type_indexed_bitvec)]
theorem sFrameKeyEqTrans {width : Nat} [NeZero width] :
    ∀ a b c : WordSemStackFrame width, sFrameKeyEq a b ∧ sFrameKeyEq b c → sFrameKeyEq a c := by
  rintro ⟨n1, l01, l1, h1⟩ ⟨n2, l02, l2, h2⟩ ⟨n3, l03, l3, h3⟩ ⟨hab, hbc⟩
  rw [sFrameKeyEqDef2] at hab hbc ⊢
  obtain ⟨a1, a2, a3, a4⟩ := hab
  obtain ⟨b1, b2, b3, b4⟩ := hbc
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4⟩

/-- Exact HOL `s_key_eq_trans` (`wordPropsScript.sml:1898-1903`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_trans"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqTrans {width : Nat} [NeZero width] :
    ∀ a b c : List (WordSemStackFrame width), sKeyEq a b ∧ sKeyEq b c → sKeyEq a c := by
  intro a
  induction a with
  | nil =>
      rintro b c ⟨hab, hbc⟩
      cases b with
      | nil => exact hbc
      | cons _ _ => exact absurd hab (by simp [sKeyEq])
  | cons x xs ih =>
      rintro b c ⟨hab, hbc⟩
      cases b with
      | nil => exact absurd hab (by simp [sKeyEq])
      | cons y ys =>
          cases c with
          | nil => exact absurd hbc (by simp [sKeyEq])
          | cons z zs =>
              exact ⟨ih ys zs ⟨hab.1, hbc.1⟩, sFrameKeyEqTrans x y z ⟨hab.2, hbc.2⟩⟩

/-- Exact HOL `s_frame_val_eq_trans` (`wordPropsScript.sml:1907-1912`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_eq_trans"
  (words_as_type_indexed_bitvec)]
theorem sFrameValEqTrans {width : Nat} [NeZero width] :
    ∀ a b c : WordSemStackFrame width, sFrameValEq a b ∧ sFrameValEq b c → sFrameValEq a c := by
  rintro ⟨n1, l01, l1, h1⟩ ⟨n2, l02, l2, h2⟩ ⟨n3, l03, l3, h3⟩ ⟨hab, hbc⟩
  rw [sFrameValEqDef2] at hab hbc ⊢
  obtain ⟨a1, a2, a3⟩ := hab
  obtain ⟨b1, b2, b3⟩ := hbc
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩

/-- Exact HOL `s_val_eq_trans` (`wordPropsScript.sml:1916-1921`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_trans"
  (words_as_type_indexed_bitvec)]
theorem sValEqTrans {width : Nat} [NeZero width] :
    ∀ a b c : List (WordSemStackFrame width), sValEq a b ∧ sValEq b c → sValEq a c := by
  intro a
  induction a with
  | nil =>
      rintro b c ⟨hab, hbc⟩
      cases b with
      | nil => exact hbc
      | cons _ _ => exact absurd hab (by simp [sValEq])
  | cons x xs ih =>
      rintro b c ⟨hab, hbc⟩
      cases b with
      | nil => exact absurd hab (by simp [sValEq])
      | cons y ys =>
          cases c with
          | nil => exact absurd hbc (by simp [sValEq])
          | cons z zs =>
              exact ⟨ih ys zs ⟨hab.1, hbc.1⟩, sFrameValEqTrans x y z ⟨hab.2, hbc.2⟩⟩

/-- Exact HOL `s_frame_key_eq_sym` (`wordPropsScript.sml:1927-1932`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_key_eq_sym"
  (words_as_type_indexed_bitvec)]
theorem sFrameKeyEqSym {width : Nat} [NeZero width] :
    ∀ a b : WordSemStackFrame width, sFrameKeyEq a b ↔ sFrameKeyEq b a := by
  rintro ⟨n1, l01, l1, h1⟩ ⟨n2, l02, l2, h2⟩
  rw [sFrameKeyEqDef2, sFrameKeyEqDef2]
  constructor <;> rintro ⟨a1, a2, a3, a4⟩ <;> exact ⟨a1.symm, a2.symm, a3.symm, a4.symm⟩

/-- Exact HOL `s_key_eq_sym` (`wordPropsScript.sml:1936-1944`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_sym"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqSym {width : Nat} [NeZero width] :
    ∀ a b : List (WordSemStackFrame width), sKeyEq a b ↔ sKeyEq b a := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [sKeyEq]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [sKeyEq]
      | cons y ys =>
          show (sKeyEq xs ys ∧ sFrameKeyEq x y) ↔ (sKeyEq ys xs ∧ sFrameKeyEq y x)
          rw [ih ys, sFrameKeyEqSym x y]

/-- Exact HOL `s_frame_val_eq_sym` (`wordPropsScript.sml:1947-1952`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_frame_val_eq_sym"
  (words_as_type_indexed_bitvec)]
theorem sFrameValEqSym {width : Nat} [NeZero width] :
    ∀ a b : WordSemStackFrame width, sFrameValEq a b ↔ sFrameValEq b a := by
  rintro ⟨n1, l01, l1, h1⟩ ⟨n2, l02, l2, h2⟩
  rw [sFrameValEqDef2, sFrameValEqDef2]
  constructor <;> rintro ⟨a1, a2, a3⟩ <;> exact ⟨a1.symm, a2.symm, a3.symm⟩

/-- Exact HOL `s_val_eq_sym` (`wordPropsScript.sml:1955-1963`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_sym"
  (words_as_type_indexed_bitvec)]
theorem sValEqSym {width : Nat} [NeZero width] :
    ∀ a b : List (WordSemStackFrame width), sValEq a b ↔ sValEq b a := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [sValEq]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [sValEq]
      | cons y ys =>
          show (sValEq xs ys ∧ sFrameValEq x y) ↔ (sValEq ys xs ∧ sFrameValEq y x)
          rw [ih ys, sFrameValEqSym x y]

/-- Exact HOL `s_val_eq_length` (`wordPropsScript.sml:2145-2150`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_length"
  (words_as_type_indexed_bitvec)]
theorem sValEqLength {width : Nat} [NeZero width] :
    ∀ s t : List (WordSemStackFrame width), sValEq s t → s.length = t.length := by
  intro s
  induction s with
  | nil => intro t h; cases t <;> simp_all [sValEq]
  | cons x xs ih =>
      intro t h
      cases t with
      | nil => exact absurd h (by simp [sValEq])
      | cons y ys => simp [ih ys h.1]

/-- Exact HOL `s_key_eq_length` (`wordPropsScript.sml:2152-2157`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_key_eq_length"
  (words_as_type_indexed_bitvec)]
theorem sKeyEqLength {width : Nat} [NeZero width] :
    ∀ s t : List (WordSemStackFrame width), sKeyEq s t → s.length = t.length := by
  intro s
  induction s with
  | nil => intro t h; cases t <;> simp_all [sKeyEq]
  | cons x xs ih =>
      intro t h
      cases t with
      | nil => exact absurd h (by simp [sKeyEq])
      | cons y ys => simp [ih ys h.1]

private theorem mapFstZipTake {α β : Type} (l : List (α × β)) (xs : List β)
    (h : l.length ≤ xs.length) :
    ((l.map Prod.fst).zip (xs.take l.length)).map Prod.fst = l.map Prod.fst := by
  rw [List.map_fst_zip]
  simp [h]

/-- Exact HOL `dec_stack_stack_key_eq` (`wordPropsScript.sml:1993-2000`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "dec_stack_stack_key_eq"
  (words_as_type_indexed_bitvec)]
theorem decStackStackKeyEq {width : Nat} [NeZero width] :
    ∀ (wl : List (WordLocW width)) (st st' : List (WordSemStackFrame width)),
      wordSemDecStack wl st = some st' → sKeyEq st st' := by
  intro wl st
  induction st generalizing wl with
  | nil =>
      intro st' h
      cases wl with
      | nil =>
          simp only [wordSemDecStack, Option.some.injEq] at h
          subst h; simp [sKeyEq]
      | cons _ _ => simp [wordSemDecStack] at h
  | cons fr rest ih =>
      intro st' h
      rcases fr with ⟨n, l0, l, handler⟩
      simp only [wordSemDecStack] at h
      split at h
      · cases h
      · rename_i hlen
        cases hd : wordSemDecStack (wl.drop l.length) rest with
        | none => rw [hd] at h; cases h
        | some s =>
            rw [hd] at h
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨ih _ s hd, ?_⟩
            rw [sFrameKeyEqDef2]
            exact ⟨(mapFstZipTake l wl (by omega)).symm, rfl, rfl, rfl⟩

/-- Exact HOL `gc_s_key_eq` (`wordPropsScript.sml:2004-2009`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem gcSKeyEq {width : Nat} [NeZero width] {C F : Type} :
    ∀ (s x : WordSemStateFiniteExact width C F),
      WordSemStateFiniteExact.gc s = some x → sKeyEq s.stack x.stack := by
  intro s x h
  unfold WordSemStateFiniteExact.gc at h
  simp only at h
  split at h
  · cases h
  · rename_i wl m st _
    split at h
    · cases h
    · rename_i stack hd
      simp only [Option.some.injEq] at h
      subst h
      exact decStackStackKeyEq wl s.stack stack hd

/-- Exact HOL `s_val_eq_enc_stack` (`wordPropsScript.sml:2012-2018`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_enc_stack"
  (words_as_type_indexed_bitvec)]
theorem sValEqEncStack {width : Nat} [NeZero width] :
    ∀ st st' : List (WordSemStackFrame width), sValEq st st' →
      wordSemEncStack st = wordSemEncStack st' := by
  intro st
  induction st with
  | nil => intro st' h; cases st' with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [sValEq])
  | cons x xs ih =>
      intro st' h
      cases st' with
      | nil => exact absurd h (by simp [sValEq])
      | cons y ys =>
          obtain ⟨hr, hf⟩ := h
          rcases x with ⟨n, l0, l, hx⟩
          rcases y with ⟨n', l0', l', hy⟩
          rw [sFrameValEqDef2] at hf
          simp only [wordSemEncStack, hf.1, ih ys hr]

/-- Exact HOL `s_val_eq_dec_stack` (`wordPropsScript.sml:2020-2033`). -/
@[hol "cakeml/compiler/backend/semantics/wordPropsScript.sml" "s_val_eq_dec_stack"
  (words_as_type_indexed_bitvec)]
theorem sValEqDecStack {width : Nat} [NeZero width] :
    ∀ (q : List (WordLocW width)) (st st' x : List (WordSemStackFrame width)),
      sValEq st st' ∧ wordSemDecStack q st = some x →
      ∃ y, wordSemDecStack q st' = some y ∧ sValEq x y := by
  intro q st
  induction st generalizing q with
  | nil =>
      rintro st' x ⟨hv, hd⟩
      cases st' with
      | nil => exact ⟨x, hd, by
          cases q with
          | nil => simp only [wordSemDecStack, Option.some.injEq] at hd; subst hd; simp [sValEq]
          | cons _ _ => simp [wordSemDecStack] at hd⟩
      | cons _ _ => exact absurd hv (by simp [sValEq])
  | cons fr rest ih =>
      rintro st' x ⟨hv, hd⟩
      cases st' with
      | nil => exact absurd hv (by simp [sValEq])
      | cons fr' rest' =>
          obtain ⟨hvr, hvf⟩ := hv
          rcases fr with ⟨n, l0, l, h⟩
          rcases fr' with ⟨n', l0', l', h'⟩
          rw [sFrameValEqDef2] at hvf
          obtain ⟨hsnd, rfl, rfl⟩ := hvf
          have hlen : l'.length = l.length := by
            have := congrArg List.length hsnd; simpa using this.symm
          simp only [wordSemDecStack] at hd ⊢
          rw [hlen]
          split at hd
          · cases hd
          · rename_i hl
            rw [if_neg hl]
            cases hd1 : wordSemDecStack (q.drop l.length) rest with
            | none => rw [hd1] at hd; cases hd
            | some sx =>
                rw [hd1] at hd
                simp only [Option.some.injEq] at hd
                subst hd
                obtain ⟨y, hy, hxy⟩ := ih (q.drop l.length) rest' sx ⟨hvr, hd1⟩
                rw [hy]
                refine ⟨_, rfl, hxy, ?_⟩
                rw [sFrameValEqDef2]
                refine ⟨?_, rfl, rfl⟩
                rw [List.map_snd_zip, List.map_snd_zip] <;> simp [hlen] <;> omega

/-- Exact HOL `gc_s_val_eq` (`wordPropsScript.sml:2037-2049`). HOL's unused
universally quantified `x` is retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem gcSValEq {width : Nat} [NeZero width] {C F : Type} :
    ∀ (s _x : WordSemStateFiniteExact width C F) (st : List (WordSemStackFrame width))
      (y : WordSemStateFiniteExact width C F),
      sValEq s.stack st ∧ WordSemStateFiniteExact.gc s = some y →
      ∃ z, WordSemStateFiniteExact.gc { s with stack := st } = some { y with stack := z } ∧
        sValEq y.stack z ∧ sKeyEq z st := by
  rintro s _ st y ⟨hv, hg⟩
  unfold WordSemStateFiniteExact.gc at hg ⊢
  simp only at hg ⊢
  rw [← sValEqEncStack _ _ hv]
  split at hg
  · cases hg
  · rename_i wl m sto heq
    split at hg
    · cases hg
    · rename_i stack hd
      simp only [Option.some.injEq] at hg
      subst hg
      obtain ⟨z, hz, hsz⟩ := sValEqDecStack wl s.stack st stack ⟨hv, hd⟩
      rw [hz]
      refine ⟨z, rfl, hsz, (sKeyEqSym _ _).mp (decStackStackKeyEq wl st z hz)⟩

/-- Exact HOL `gc_s_val_eq_word_state` (`wordPropsScript.sml:2053-2067`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem gcSValEqWordState {width : Nat} [NeZero width] {C F : Type} :
    ∀ (s : WordSemStateFiniteExact width C F) (tlocs : Spt (WordLocW width))
      (tstack : List (WordSemStackFrame width)) (y : WordSemStateFiniteExact width C F),
      sValEq s.stack tstack ∧ WordSemStateFiniteExact.gc s = some y →
      ∃ zlocs zstack,
        WordSemStateFiniteExact.gc { s with stack := tstack, locals := tlocs } =
          some { y with stack := zstack, locals := zlocs } ∧
        sValEq y.stack zstack ∧ sKeyEq zstack tstack := by
  rintro s tlocs tstack y ⟨hv, hg⟩
  unfold WordSemStateFiniteExact.gc at hg ⊢
  simp only at hg ⊢
  rw [← sValEqEncStack _ _ hv]
  split at hg
  · cases hg
  · rename_i wl m sto heq
    split at hg
    · cases hg
    · rename_i stack hd
      simp only [Option.some.injEq] at hg
      subst hg
      obtain ⟨z, hz, hsz⟩ := sValEqDecStack wl s.stack tstack stack ⟨hv, hd⟩
      rw [hz]
      exact ⟨tlocs, z, rfl, hsz, (sKeyEqSym _ _).mp (decStackStackKeyEq wl tstack z hz)⟩

/-- Exact HOL `gc_s_val_eq_gen` (`wordPropsScript.sml:2083-2113`). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem gcSValEqGen {width : Nat} [NeZero width] {C F : Type} :
    ∀ (s t s' : WordSemStateFiniteExact width C F),
      s.gcFun = t.gcFun ∧ s.memory = t.memory ∧ s.mdomain = t.mdomain ∧ s.store = t.store ∧
      sValEq s.stack t.stack ∧ s.stackSize = t.stackSize ∧ s.stackMax = t.stackMax ∧
      s.stackLimit = t.stackLimit ∧ WordSemStateFiniteExact.gc s = some s' →
      ∃ t', WordSemStateFiniteExact.gc t = some t' ∧
        sValEq s'.stack t'.stack ∧ sKeyEq t.stack t'.stack ∧
        t'.memory = s'.memory ∧ t'.store = s'.store ∧ t'.stackSize = s'.stackSize ∧
        t'.stackMax = s'.stackMax ∧ t'.stackLimit = s'.stackLimit := by
  rintro s t s' ⟨hgf, hm, hmd, hst, hv, hss, hsm, hsl, hg⟩
  unfold WordSemStateFiniteExact.gc at hg ⊢
  simp only at hg ⊢
  rw [← sValEqEncStack _ _ hv, ← hgf, ← hm, ← hmd, ← hst]
  split at hg
  · cases hg
  · rename_i wl m sto heq
    split at hg
    · cases hg
    · rename_i stack hd
      simp only [Option.some.injEq] at hg
      subst hg
      obtain ⟨z, hz, hsz⟩ := sValEqDecStack wl s.stack t.stack stack ⟨hv, hd⟩
      rw [hz]
      exact ⟨_, rfl, hsz, decStackStackKeyEq wl t.stack z hz, rfl, rfl, hss.symm, hsm.symm,
        hsl.symm⟩

private theorem alistLookupIsSome {α : Type} (k : Nat) :
    ∀ l : List (Nat × α), (sptAListLookup k l).isSome = true ↔ k ∈ l.map Prod.fst
  | [] => by simp [sptAListLookup]
  | (a, v) :: l => by
      by_cases h : k = a
      · subst h; simp [sptAListLookup]
      · simp [sptAListLookup, h, alistLookupIsSome k l]

private theorem sptDomainFromAList {α : Type} (l : List (Nat × α)) (k : Nat) :
    sptDomain (sptFromAList l) k ↔ k ∈ l.map Prod.fst := by
  unfold sptDomain
  rw [sptLookup_sptFromAList]
  exact alistLookupIsSome k l

private theorem toAListKeys {α : Type} (x : Spt α) (k : Nat) :
    k ∈ (sptToAList x).map Prod.fst ↔ sptDomain x k := by
  simp only [List.mem_map, sptDomain]
  constructor
  · rintro ⟨⟨a, v⟩, hm, rfl⟩
    simp [(sptToAList_mem_iff_lookup x a v).mp hm]
  · intro hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    exact ⟨(k, v), (sptToAList_mem_iff_lookup x k v).mpr hv, rfl⟩

private theorem envToListKeys' {width : Nat} [NeZero width] (x : Spt (WordLocW width))
    (perm : Nat → Nat → Nat) (k : Nat) :
    k ∈ (wordSemEnvToList x perm).1.map Prod.fst ↔ sptDomain x k := by
  rw [← toAListKeys x k]
  simp only [List.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, (wordSemEnvToList_mem_iff x perm p).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, (wordSemEnvToList_mem_iff x perm p).mpr hp, rfl⟩

/-- Exact HOL `push_env_pop_env_s_key_eq` (`wordPropsScript.sml:2115-2133`). HOL
set union of the two domains is pointwise disjunction. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem pushEnvPopEnvSKeyEq {width : Nat} [NeZero width] {C F : Type} :
    ∀ (x : Spt (WordLocW width) × Spt (WordLocW width))
      (b : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
      (s t : WordSemStateFiniteExact width C F),
      sKeyEq (WordSemStateFiniteExact.pushEnv x b s).stack t.stack →
      ∃ n l ls opt,
        t.stack = .stackFrame n (sptToAList x.1) l opt :: ls ∧
        ∃ y, WordSemStateFiniteExact.popEnv t = some y ∧
          y.locals = sptUnion (sptFromAList l) (sptFromAList (sptToAList x.1)) ∧
          (fun k => sptDomain x.2 k ∨ sptDomain x.1 k) = sptDomain y.locals ∧
          sKeyEq s.stack y.stack := by
  intro x b s t h
  have hpush : ∃ L h0, (WordSemStateFiniteExact.pushEnv x b s).stack =
      .stackFrame s.localsSize (sptToAList x.1) L h0 :: s.stack ∧
      L = (wordSemEnvToList x.2 s.permute).1 := by
    cases b with
    | none => exact ⟨_, _, rfl, rfl⟩
    | some v => obtain ⟨_, _, _, _⟩ := v; exact ⟨_, _, rfl, rfl⟩
  obtain ⟨L, h0, hst, hL⟩ := hpush
  rw [hst] at h
  cases ht : t.stack with
  | nil => rw [ht] at h; exact absurd h (by simp [sKeyEq])
  | cons fr ls =>
      rw [ht] at h
      obtain ⟨hrest, hf⟩ := h
      rcases fr with ⟨n, l0, l, opt⟩
      rw [sFrameKeyEqDef2] at hf
      obtain ⟨hkeys, rfl, rfl, rfl⟩ := hf
      refine ⟨s.localsSize, l, ls, h0, rfl, ?_⟩
      have hpop : ∃ y, WordSemStateFiniteExact.popEnv t = some y ∧
          y.locals = sptUnion (sptFromAList l) (sptFromAList (sptToAList x.1)) ∧
          y.stack = ls := by
        unfold WordSemStateFiniteExact.popEnv
        rw [ht]
        cases h0 with
        | none => exact ⟨_, rfl, rfl, rfl⟩
        | some hh => obtain ⟨_, _, _⟩ := hh; exact ⟨_, rfl, rfl, rfl⟩
      obtain ⟨y, hy, hloc, hys⟩ := hpop
      refine ⟨y, hy, hloc, ?_, by rw [hys]; exact hrest⟩
      funext k
      apply propext
      rw [hloc, sptDomain_sptUnion]
      show _ ↔ (sptDomain (sptFromAList l) k ∨ sptDomain (sptFromAList (sptToAList x.1)) k)
      rw [sptDomainFromAList, sptDomainFromAList, toAListKeys, ← hkeys, hL, envToListKeys']

end WordSemStackEq

end Flapjack
