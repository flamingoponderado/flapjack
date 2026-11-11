module

public import Flapjack.HolRef
public import Flapjack.Misc.OptMmapCong
public import Flapjack.Pancake.PanStructs
public import Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact
public import Flapjack.Pancake.Proofs.PanStructs.CompileShapeExact

@[expose] public section

/-!
Proof lemmas for CakeML Pancake's `pan_structs` theory.

The local notes distinguish tagged source ports from untagged helpers over
production carriers and different equality or indexing APIs. The full native
program and declaration proofs are assembled in `CompileCorrectExact.lean`
and `CompileDeclsCorrectExact.lean`; `SemanticsEq.lean` and
`CompileTopSemanticsDeclsExact.lean` prove the original observational and
initial declaration semantics results. Those statements use the reviewed
exact compiler/evaluator carriers. They do not establish production routing
for the legacy helpers below or final Pancake-to-RISC-V correctness.
-/

namespace Flapjack

/-- Exact port of the local HOL `UNCURRY_EQ_o_SND`
    (`pan_structsProofScript.sml:552`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "UNCURRY_EQ_o_SND"]
theorem prod_uncurry_const_eq_comp_snd {α β γ : Type} (f : β → γ) :
    Function.uncurry (fun _ : α => f) = f ∘ Prod.snd := by
  funext p
  cases p
  rfl

/-- Exact port of HOL `map_uncurry_zip_again`
    (`pan_structsProofScript.sml:900`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "map_uncurry_zip_again"]
theorem list_zip_map_eq {α β γ δ : Type} (f : α → γ) (g : β → δ)
    (xs : List α) (ys : List β) (h : xs.length = ys.length) :
    (xs.zip ys).map (fun p => (f p.1, g p.2)) = (xs.map f).zip (ys.map g) := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp at h
  | cons x xs ih =>
      cases ys with
      | nil => simp at h
      | cons y ys =>
          simp only [List.zip_cons_cons, List.map_cons, List.length_cons] at h ⊢
          have h' : xs.length = ys.length := by omega
          rw [ih ys h']

/-! Support for PanValues: lookup success in a suffix implies lookup success
    in the original context. -/
theorem lookupInfo_isSome_drop (name : String) (context : StructContext)
    (n : Nat) :
    (lookupInfo name (context.drop n)).isSome = true →
      (lookupInfo name context).isSome = true := by
  induction context generalizing n with
  | nil => cases n <;> simp [lookupInfo]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      cases n with
      | zero => simp
      | succ m =>
          simp only [List.drop_succ_cons]
          intro h
          have hrest := ih m h
          by_cases hc : candidate == name
          · simp [lookupInfo, hc]
          · simp only [lookupInfo, hc]
            exact hrest

/-! Lean list-lookup adaptation of Cake's local `alookup_drop_helper`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:78`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "alookup_drop_helper"]
theorem lookup_drop_helper [BEq α] [LawfulBEq α]
    (n : Nat) (xs : List (α × β)) (key : α) (value : β)
    (hlookup : List.lookup key (xs.drop n) = some value)
    (hnodup : (xs.map Prod.fst).Nodup) :
    key ∉ (xs.take n).map Prod.fst ∧ List.lookup key xs = some value := by
  have hmem_drop : key ∈ (xs.drop n).map Prod.fst := by
    obtain ⟨l₁, l₂, heq, _⟩ :=
      (List.lookup_eq_some_iff (l := xs.drop n) (k := key) (b := value)).mp hlookup
    exact List.mem_map.mpr ⟨(key, value), by rw [heq]; simp, rfl⟩
  have hmap : xs.map Prod.fst =
      (xs.take n).map Prod.fst ++ (xs.drop n).map Prod.fst := by
    rw [← List.map_append, List.take_append_drop]
  have hnodup' : ((xs.take n).map Prod.fst ++ (xs.drop n).map Prod.fst).Nodup := by
    rw [← hmap]; exact hnodup
  have hnot_mem : key ∉ (xs.take n).map Prod.fst := by
    intro hk
    exact (List.nodup_append.mp hnodup').2.2 key hk key hmem_drop rfl
  refine ⟨hnot_mem, ?_⟩
  have htake_none : List.lookup key (xs.take n) = none := by
    rw [List.lookup_eq_none_iff]
    intro p hp
    rw [bne_iff_ne]
    intro hkp
    exact hnot_mem (List.mem_map.mpr ⟨p, hp, hkp.symm⟩)
  have h1 := List.lookup_append (l₁ := xs.take n) (l₂ := xs.drop n) (k := key)
  rw [htake_none] at h1
  simp only [Option.none_or] at h1
  rw [← List.take_append_drop n xs, h1]
  exact hlookup

/-- Exact translation of HOL `opt_mmap_eq_every`
    (`pan_structsProofScript.sml:255`): if production `List.mapM` succeeds,
    every successful image satisfying `P` makes the result satisfy `P`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "opt_mmap_eq_every"]
theorem list_mapM_all_of_mem {α β : Type} (f : α → Option β) (P : β → Bool)
    (xs : List α) (ys : List β) (h : xs.mapM f = some ys)
    (hf : ∀ x y, x ∈ xs → f x = some y → P y = true) :
    ys.all P = true := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.mapM_nil] at h
      cases h
      simp
  | cons a as ih =>
      rw [List.mapM_cons] at h
      cases hx : f a with
      | none => simp [hx] at h
      | some b =>
          simp only [hx] at h
          cases hxs : as.mapM f with
          | none => simp [hxs] at h
          | some ys' =>
              simp only [hxs] at h
              have hb : b :: ys' = ys := by simpa using h
              subst hb
              simp only [List.all_cons, Bool.and_eq_true]
              exact ⟨hf a b (by simp) hx,
                ih ys' hxs (fun x y hx' hfy => hf x y (by simp [hx']) hfy)⟩

/-- Exact port of HOL `dropWhile_MAP_helper`
    (`pan_structsProofScript.sml:542`): mapping commutes with `dropWhile` when
    the source and mapped predicates agree on every source element. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "dropWhile_MAP_helper"]
theorem dropWhile_map_helper {α β : Type} (P : α → Bool) (Q : β → Bool)
    (f : α → β) (xs : List α) (ys : List α)
    (h : xs.dropWhile P = ys)
    (hPQ : ∀ x ∈ xs, P x = Q (f x)) :
    (xs.map f).dropWhile Q = ys.map f := by
  induction xs generalizing ys with
  | nil =>
      simp only [List.dropWhile_nil] at h
      subst h
      simp
  | cons x xs ih =>
      have hx : P x = Q (f x) := hPQ x (by simp)
      rw [List.dropWhile_cons] at h
      by_cases hP : P x = true
      · rw [if_pos hP] at h
        have hQ : Q (f x) = true := by rw [← hx]; exact hP
        rw [List.map_cons, List.dropWhile_cons, hQ]
        simp only [if_true]
        exact ih ys h (fun y hy => hPQ y (by simp [hy]))
      · rw [if_neg hP] at h
        have hPfalse : P x = false := by simpa using hP
        have hQ : Q (f x) = false := by rw [← hx]; exact hPfalse
        rw [← h, List.map_cons, List.dropWhile_cons, hQ]
        simp only [Bool.false_eq_true, if_false]

/-- Cake's `opt_mmap_eq_some_el`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:19`). The `getElem?`
    formulation is the total Lean translation of HOL's total `EL`: under the
    in-range premise, each optional lookup succeeds and supplies that element. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "opt_mmap_eq_some_el"]
theorem optMmapEqSomeEl {α β : Type} (f : α → Option β) (xs : List α) (ys : List β) :
    xs.mapM f = some ys ↔
      xs.length = ys.length ∧ ∀ n, n < ys.length → (xs[n]?).bind f = ys[n]? := by
  exact list_mapM_eq_some_iff f xs ys

/-! Faithful port of Cake `afindi_less_length`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:345`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_less_length"]
theorem afindi_less_length [DecidableEq α] (key : α) :
    ∀ (entries : List (α × β)) (index : Nat),
      afindi key entries = some index → index < entries.length := by
  intro entries
  induction entries with
  | nil =>
      intro index h
      simp [afindi] at h
  | cons entry rest ih =>
      intro index h
      obtain ⟨candidate, value⟩ := entry
      simp only [afindi] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        simp
      · split at h
        · simp at h
        · rename_i found hfound
          simp only [Option.some.injEq] at h
          subst h
          have hlt := ih found hfound
          simp only [List.length_cons]
          omega

/-! Faithful Lean indexing form of Cake `afindi_EL`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:430`). Given the
    successful search, `getElem?` is `some` exactly at the in-range `EL` index. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_EL"]
theorem afindi_el_fst [DecidableEq α] (key : α) :
    ∀ (entries : List (α × β)) (index : Nat),
      afindi key entries = some index →
        (entries[index]?).map Prod.fst = some key := by
  intro entries
  induction entries with
  | nil =>
      intro index h
      simp [afindi] at h
  | cons entry rest ih =>
      intro index h
      obtain ⟨candidate, value⟩ := entry
      simp only [afindi] at h
      split at h
      · rename_i hbeq
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.getElem?_cons_zero, Option.map_some]
        exact congrArg some hbeq.symm
      · split at h
        · simp at h
        · rename_i found hfound
          simp only [Option.some.injEq] at h
          subst h
          simp only [List.getElem?_cons_succ]
          exact ih found hfound

/-! Faithful port of Cake `afindi_append`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:417`). The source uses
    `LENGTH xs + index`; this Lean statement writes the commuted Nat sum. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_append"]
theorem afindi_append [DecidableEq α] (key : α) (xs ys : List (α × β)) :
    afindi key (xs ++ ys) =
      (match afindi key xs with
        | none => (afindi key ys).map (fun index => index + xs.length)
        | some index => some index) := by
  induction xs with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hbeq : key = candidate
      · simp [afindi, hbeq]
      · simp only [List.cons_append, afindi, hbeq]
        rw [ih]
        cases ha : afindi key rest with
        | none =>
            cases hb : afindi key ys with
            | none => simp
            | some index => simp; omega
        | some index => simp

/-! Faithful port of Cake `afindi_MAP_eq`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:356`). -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "afindi_MAP_eq"]
theorem afindi_map_eq [DecidableEq α] (key : α) (f : α × β → α × γ)
    (entries : List (α × β))
    (hf : ∀ x y, (x, y) ∈ entries → (f (x, y)).1 = x) :
    afindi key (entries.map f) = afindi key entries := by
  induction entries with
  | nil => simp only [List.map_nil, afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      have hhead : (f (candidate, value)).1 = candidate :=
        hf candidate value (by simp)
      have htail : ∀ x y, (x, y) ∈ rest → (f (x, y)).1 = x :=
        fun x y hxy => hf x y (by simp [hxy])
      simp only [List.map_cons]
      rw [afindi_cons, afindi_cons, hhead, ih htail]

/-! Faithful API translation of Cake `dropWhile_afindi`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:334`). HOL's logical
    inequality predicate is expressed with `decide` for Lean's Bool-valued
    `List.dropWhile`; HOL `DROP` translates to `List.drop`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "dropWhile_afindi"]
theorem afindi_dropWhile [DecidableEq α] (key : α) (entries : List (α × β)) :
    entries.dropWhile (fun entry => decide (key ≠ entry.1)) =
      match afindi key entries with
      | none => []
      | some index => entries.drop index := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hb : key = candidate
      · simp [afindi_cons, hb]
      · have hdec : decide (key ≠ candidate) = true := by simp [hb]
        simp only [List.dropWhile_cons, afindi_cons, hdec, if_neg hb]
        rw [ih]
        cases afindi key rest with
        | none => simp
        | some index => simp [List.drop_succ_cons]

/-! Faithful API translation of Cake `ALOOKUP_eq_afindi`
    (`cakeml/pancake/proofs/pan_structsProofScript.sml:405`). `List.lookup`
    translates `ALOOKUP`; the optional indexed projection translates HOL's
    `OPTION_MAP` of `SND ∘ EL`, with `afindi_less_length` ensuring successful
    indices are in range. Its synthesized `BEq` comes from `DecidableEq`. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "ALOOKUP_eq_afindi"]
theorem afindi_lookup [DecidableEq α] (key : α) (entries : List (α × β)) :
    entries.lookup key =
      (afindi key entries).bind (fun index => (entries[index]?).map Prod.snd) := by
  induction entries with
  | nil => simp [afindi]
  | cons entry rest ih =>
      obtain ⟨candidate, value⟩ := entry
      by_cases hbeq : key = candidate
      · simp [afindi_cons, hbeq]
      · have hbeq' : (key == candidate) = false := by
          simp [BEq.beq, hbeq]
        simp only [List.lookup_cons, hbeq', afindi_cons, if_neg hbeq]
        rw [ih]
        cases afindi key rest with
        | none => simp
        | some index => simp [List.getElem?_cons_succ]

/-! Helper for Cake's local `map_fst_eq_alookup`: equal key lists imply
    identical `afindi` positions. This intermediate theorem is not a separate
    HOL declaration, so it has no `@[hol]` tag. -/
theorem afindi_eq_of_map_fst_eq [DecidableEq α] (key : α) :
    ∀ (xs : List (α × β)) (ys : List (α × γ)), xs.map Prod.fst = ys.map Prod.fst →
      afindi key xs = afindi key ys := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      simp only [List.map_nil] at h
      have hy : ys = [] := (List.map_eq_nil_iff.mp h.symm)
      subst hy
      simp [afindi]
  | cons x xs ih =>
      intro ys h
      obtain ⟨cx, vx⟩ := x
      cases ys with
      | nil => simp at h
      | cons y ys =>
          obtain ⟨cy, vy⟩ := y
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨hhead, htail⟩ := h
          have hcy : cx = cy := hhead
          subst hcy
          by_cases hbc : key = cx
          · rw [afindi_cons key (cx, vx) xs, afindi_cons key (cx, vy) ys,
              if_pos hbc, if_pos hbc]
          · rw [afindi_cons key (cx, vx) xs, afindi_cons key (cx, vy) ys,
              if_neg hbc, if_neg hbc, ih ys htail]

/-- HOL `map_fst_eq_alookup` (`pan_structsProofScript.sml:278`) has key type
    `α`, xs value type `β`, and ys value type `γ`; the source syntax leaves all
    three polymorphic. The direct HOL type probe confirms
    `xs : (α × β) list`, `ys : (α × γ) list`, `nm : α`, and `v : β`. Lean keeps
    those independent carriers. Its `Option.map` projections are the list-index
    API form of HOL `SND (EL i ...)` under the explicit bounds. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "map_fst_eq_alookup"]
theorem map_fst_eq_lookup [DecidableEq α]
    (xs : List (α × β)) (ys : List (α × γ)) (nm : α) {v : β}
    (hlen : xs.map Prod.fst = ys.map Prod.fst)
    (hlookup : xs.lookup nm = some v) :
    ∃ i, afindi nm xs = some i ∧ afindi nm ys = some i ∧
      i < xs.length ∧ i < ys.length ∧
      (xs[i]?).map Prod.snd = some v ∧ (ys[i]?).map Prod.snd = ys.lookup nm := by
  have hafindi := afindi_eq_of_map_fst_eq nm xs ys hlen
  have hbridge := afindi_lookup nm xs
  rw [hlookup] at hbridge
  cases h : afindi nm xs with
  | none =>
      rw [h] at hbridge
      simp at hbridge
  | some i =>
      rw [h] at hbridge
      simp only [Option.bind_some] at hbridge
      have hxs : (xs[i]?).map Prod.snd = some v := hbridge.symm
      have hi_xs : i < xs.length := afindi_less_length nm xs i h
      have hys : afindi nm ys = some i := by rw [← hafindi]; exact h
      have hi_ys : i < ys.length := afindi_less_length nm ys i hys
      have hybridge := afindi_lookup nm ys
      rw [hys] at hybridge
      simp only [Option.bind_some] at hybridge
      refine ⟨i, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · exact hys
      · exact hi_xs
      · exact hi_ys
      · exact hxs
      · exact hybridge.symm

end Flapjack
