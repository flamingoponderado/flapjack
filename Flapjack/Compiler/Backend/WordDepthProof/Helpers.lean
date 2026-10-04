import Flapjack.Compiler.Backend.WordDepth
import Flapjack.Compiler.Backend.BackendProps
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
import Flapjack.Compiler.Backend.LinearScan.Proofs.ApplyBijection

/-!
# `word_depthProofScript.sml` helper lemmas (lines 12-146)

The option-order and call-graph lemmas preceding `max_depth_call_graph_lemma`.
HOL `OPTION_MAP2` is `WordDepth.optionMap₂` (the rendering `max_depth` uses);
`optionMap₂_eq_map₂` relates it to `Option.map₂`, the rendering of the
`backendProps` option laws. `option_le` is `BackendProps.optionLe`.
-/

namespace Flapjack.Compiler.Backend.WordDepthProof

open Flapjack Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.BackendProps

/-- `WordDepth.optionMap₂` is `Option.map₂` (Flapjack infrastructure). -/
theorem optionMap₂_eq_map₂ {α β γ : Type} (f : α → β → γ) (a : Option α) (b : Option β) :
    optionMap₂ f a b = Option.map₂ f a b := by
  rcases a with _ | _ <;> rcases b with _ | _ <;> rfl

/-- Full original `option_le_X_MAX_X` (local, simp):
`option_le x (OPTION_MAP2 MAX m x) /\ option_le x (OPTION_MAP2 MAX x m)`. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "option_le_X_MAX_X"]
theorem optionLe_X_MAX_X (x m : Option Nat) :
    optionLe x (optionMap₂ max m x) ∧ optionLe x (optionMap₂ max x m) := by
  rcases m with _ | _ <;> rcases x with _ | _ <;> simp [optionLe, optionMap₂]

/-- Full original `OPTION_MAP2_MAX_IDEMPOT` (local, simp):
`OPTION_MAP2 MAX x x = x`. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "OPTION_MAP2_MAX_IDEMPOT"]
theorem optionMap2_max_idempot (x : Option Nat) : optionMap₂ max x x = x := by
  rcases x with _ | _ <;> simp [optionMap₂]

/-- Full original `OPTION_MAP2_SOME_0` (local, simp):
`OPTION_MAP2 (+) x (SOME 0n) = x /\ OPTION_MAP2 MAX x (SOME 0n) = x`. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "OPTION_MAP2_SOME_0"]
theorem optionMap2_some_0 (x : Option Nat) :
    optionMap₂ (· + ·) x (some 0) = x ∧ optionMap₂ max x (some 0) = x := by
  rcases x with _ | _ <;> simp [optionMap₂]

/-- `SOME 0` is a left unit for `OPTION_MAP2 MAX` (Flapjack infrastructure). -/
theorem optionMap2_max_zero_left (x : Option Nat) : optionMap₂ max (some 0) x = x := by
  rcases x with _ | _ <;> simp [optionMap₂]

/-- `NONE` absorbs `OPTION_MAP2` on the right (Flapjack infrastructure). -/
theorem optionMap2_none_right {α β γ : Type} (f : α → β → γ) (x : Option α) :
    optionMap₂ f x none = none := by
  rcases x with _ | _ <;> rfl

/-- Full original `max_depth_mk_Branch`:
`!t1 t2. max_depth s (mk_Branch t1 t2) = max_depth s (Branch t1 t2)`. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "max_depth_mk_Branch"]
theorem maxDepth_mkBranch (s : Spt Nat) :
    ∀ t1 t2, maxDepth s (mkBranch t1 t2) = maxDepth s (.branch t1 t2) := by
  intro t1 t2
  unfold mkBranch
  by_cases h12 : t1 = t2
  · subst h12; simp [maxDepth, optionMap2_max_idempot]
  rw [if_neg h12]
  by_cases h1 : t1 = .leaf
  · subst h1
    rw [if_pos rfl, maxDepth, maxDepth]
    exact (optionMap2_max_zero_left _).symm
  rw [if_neg h1]
  by_cases h2 : t2 = .leaf
  · subst h2
    rw [if_pos rfl, maxDepth, maxDepth]
    exact (optionMap2_some_0 _).2.symm
  rw [if_neg h2]
  by_cases h1u : t1 = .unknown
  · subst h1u; simp [maxDepth, optionMap₂]
  rw [if_neg h1u]
  by_cases h2u : t2 = .unknown
  · subst h2u
    rw [if_pos rfl, maxDepth, maxDepth]
    exact (optionMap2_none_right max _).symm
  rw [if_neg h2u]

/-- `max` is monotone in both arguments under `option_le` (Flapjack infrastructure). -/
theorem optionLe_max_mono {a a' b b' : Option Nat} (ha : optionLe a a') (hb : optionLe b b') :
    optionLe (optionMap₂ max a b) (optionMap₂ max a' b') := by
  rcases a with _ | _ <;> rcases a' with _ | _ <;> rcases b with _ | _ <;>
    rcases b' with _ | _ <;> simp_all [optionLe, optionMap₂]
  omega

/-- `+` is monotone in its right argument under `option_le` (Flapjack infrastructure). -/
theorem optionLe_add_mono {a b b' : Option Nat} (hb : optionLe b b') :
    optionLe (optionMap₂ (· + ·) a b) (optionMap₂ (· + ·) a b') := by
  rcases a with _ | _ <;> rcases b with _ | _ <;> rcases b' with _ | _ <;>
    simp_all [optionLe, optionMap₂]

/-- `SOME 0` is below everything (Flapjack infrastructure). -/
theorem optionLe_some_zero (x : Option Nat) : optionLe (some 0) x := by
  rcases x with _ | _ <;> simp [optionLe]

/-- Full original `MEM_max_depth_graphs`:
`!ns name y. MEM name ns /\ lookup name code = SOME y ==>
option_le (max_depth_graphs ss [name] xs funs code) (max_depth_graphs ss ns xs funs code)`,
with the free `code`, `ss`, `xs`, `funs` universally bound. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "MEM_max_depth_graphs"
  (words_as_type_indexed_bitvec)]
theorem mem_maxDepthGraphs {width : Nat} [NeZero width] {Metadata : Type}
    (ss : Spt Nat) (xs : List Nat) (funs : Spt (Nat × WordLangProgHOL (BitVec width)))
    (code : Spt (Metadata × WordLangProgHOL (BitVec width))) :
    ∀ (ns : List Nat) (name : Nat) (y : Metadata × WordLangProgHOL (BitVec width)),
      name ∈ ns ∧ sptLookup name code = some y →
        optionLe (maxDepthGraphs ss [name] xs funs code) (maxDepthGraphs ss ns xs funs code) := by
  intro ns
  induction ns with
  | nil => intro name y ⟨h, _⟩; simp at h
  | cons h t ih =>
      intro name y ⟨hmem, hlook⟩
      rcases List.mem_cons.mp hmem with rfl | ht
      · obtain ⟨a, body⟩ := y
        simp only [maxDepthGraphs, hlook]
        apply optionLe_max_mono (by rcases sptLookup name ss with _ | _ <;> simp [optionLe])
        apply optionLe_max_mono
          (by rcases maxDepth ss _ with _ | _ <;> simp [optionLe])
        exact optionLe_some_zero _
      · have := ih name y ⟨ht, hlook⟩
        generalize maxDepthGraphs ss [name] xs funs code = L at this ⊢
        rw [maxDepthGraphs]
        rcases sptLookup h code with _ | ⟨a, body⟩
        · simp [optionLe]
        · simp only [optionMap₂_eq_map₂, optionLe_max_right]
          exact Or.inr (Or.inr this)

/-- The `Call` clause of `call_graph` when the callee lookup misses
(Flapjack infrastructure). -/
theorem callGraph_call_lookup_none {width : Nat} [NeZero width]
    {funs : Spt (Nat × WordLangProgHOL (BitVec width))} {n : Nat} {ns : List Nat} {total : Nat}
    {ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)}
    {args : List Nat} {handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)}
    {d : Nat} (hc : ¬(d ∈ ns ∧ ret = none)) (hl : sptLookup d funs = none) :
    callGraph funs n ns total (.call ret (some d) args handler) = .unknown := by
  rw [callGraph, if_neg hc]
  split <;> simp_all

/-- The tail-call (`ret = NONE`) clause of `call_graph` for a present callee
(Flapjack infrastructure). -/
theorem callGraph_call_tail {width : Nat} [NeZero width]
    {funs : Spt (Nat × WordLangProgHOL (BitVec width))} {n : Nat} {ns : List Nat} {total : Nat}
    {args : List Nat} {handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)}
    {d a : Nat} {body : WordLangProgHOL (BitVec width)}
    (hc : d ∉ ns) (hl : sptLookup d funs = some (a, body)) :
    callGraph funs n ns total (.call none (some d) args handler) =
      if ns.length < total then mkBranch (.call d .leaf) (callGraph funs d (d :: ns) total body)
      else .leaf := by
  rw [callGraph, if_neg (by simpa using hc)]
  split <;> simp_all

/-- The returning (`ret = SOME`) clause of `call_graph` for a present callee
(Flapjack infrastructure). -/
theorem callGraph_call_ret {width : Nat} [NeZero width]
    {funs : Spt (Nat × WordLangProgHOL (BitVec width))} {n : Nat} {ns : List Nat} {total : Nat}
    {args : List Nat} {handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)}
    {d a : Nat} {body : WordLangProgHOL (BitVec width)} {r1 : List Nat}
    {r2 : WordLangCutsetsHOL} {retProg : WordLangProgHOL (BitVec width)} {r3 r4 : Nat}
    (hl : sptLookup d funs = some (a, body)) :
    callGraph funs n ns total (.call (some (r1, r2, retProg, r3, r4)) (some d) args handler) =
      match handler with
      | none =>
          .branch (.call n (.call d .leaf))
            (mkBranch (.call n (callGraph (sptDelete d funs) d [d] total body))
              (callGraph funs n ns total retProg))
      | some (_, p, _, _) =>
          .branch (.call n (.const 3 (.call d .leaf)))
            (mkBranch (.call n (.const 3 (callGraph (sptDelete d funs) d [d] total body)))
              (mkBranch (callGraph funs n ns total p) (callGraph funs n ns total retProg))) := by
  rw [callGraph, if_neg (by simp)]
  cases handler <;> split <;> simp_all

/-- Full original `option_le_max_depth_graph`:
`!funs h ns1 t x1 ns2. set ns2 ⊆ set ns1 /\ LENGTH ns2 <= LENGTH ns1 ==>
option_le (max_depth ss (call_graph funs h ns1 t x1)) (max_depth ss (call_graph funs h ns2 t x1))`. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "option_le_max_depth_graph"
  (words_as_type_indexed_bitvec)]
theorem optionLe_maxDepth_graph {width : Nat} [NeZero width] (ss : Spt Nat) :
    ∀ (funs : Spt (Nat × WordLangProgHOL (BitVec width))) (h : Nat) (ns1 : List Nat) (t : Nat)
      (x1 : WordLangProgHOL (BitVec width)) (ns2 : List Nat),
      (∀ x, x ∈ ns2 → x ∈ ns1) ∧ ns2.length ≤ ns1.length →
        optionLe (maxDepth ss (callGraph funs h ns1 t x1))
          (maxDepth ss (callGraph funs h ns2 t x1)) := by
  intro funs h ns1 t x1
  induction funs, h, ns1, t, x1 using callGraph.induct with
  | case1 funs n ns total p1 p2 ih1 ih2 =>
      intro ns2 hs
      simp only [callGraph, maxDepth_mkBranch, maxDepth]
      exact optionLe_max_mono (ih1 ns2 hs) (ih2 ns2 hs)
  | case2 funs n ns total _ _ _ p1 p2 ih1 ih2 =>
      intro ns2 hs
      simp only [callGraph, maxDepth_mkBranch, maxDepth]
      exact optionLe_max_mono (ih1 ns2 hs) (ih2 ns2 hs)
  | case3 => intro ns2 _; simp [callGraph, maxDepth, optionLe]
  | case4 funs n ns total ret _ handler d hd =>
      intro ns2 _
      rw [callGraph, if_pos hd]
      exact optionLe_some_zero _
  | case5 funs n ns total ret _ handler d hd hl =>
      intro ns2 hs
      have hd2 : ¬(d ∈ ns2 ∧ ret = none) := fun h => hd ⟨hs.1 d h.1, h.2⟩
      rw [callGraph_call_lookup_none hd hl, callGraph_call_lookup_none hd2 hl]
      simp [maxDepth, optionLe]
  | case6 funs n ns total _ handler d fst body hl hlt hd ih =>
      intro ns2 hs
      have hdn : d ∉ ns := fun h => hd ⟨h, rfl⟩
      have hd2n : d ∉ ns2 := fun h => hdn (hs.1 d h)
      rw [callGraph_call_tail hdn hl, callGraph_call_tail hd2n hl, if_pos hlt,
        if_pos (Nat.lt_of_le_of_lt hs.2 hlt)]
      simp only [maxDepth_mkBranch, maxDepth]
      apply optionLe_max_mono (optionLe_refl _)
      apply ih (d :: ns2)
      refine ⟨fun x hx => ?_, by simp [hs.2]⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hs.1 x hx)
  | case7 funs n ns total _ handler d fst body hl hlt hd =>
      intro ns2 _
      rw [callGraph_call_tail (fun h => hd ⟨h, rfl⟩) hl, if_neg hlt]
      exact optionLe_some_zero _
  | case8 funs n ns total _ d fst body hl r1 r2 retProg r3 r4 nf hd ihb ihr =>
      intro ns2 hs
      rw [callGraph_call_ret hl, callGraph_call_ret hl]
      simp only [maxDepth_mkBranch, maxDepth]
      exact optionLe_max_mono (optionLe_refl _)
        (optionLe_max_mono (optionLe_refl _) (ihr ns2 hs))
  | case9 funs n ns total _ d fst body hl r1 r2 retProg r3 r4 nf h1 p h2 h3 hd ihb ihp ihr =>
      intro ns2 hs
      rw [callGraph_call_ret hl, callGraph_call_ret hl]
      simp only [maxDepth_mkBranch, maxDepth]
      exact optionLe_max_mono (optionLe_refl _)
        (optionLe_max_mono (optionLe_refl _) (optionLe_max_mono (ihp ns2 hs) (ihr ns2 hs)))
  | case10 funs n ns total p ih =>
      intro ns2 hs
      simp only [callGraph]
      exact ih ns2 hs
  | _ =>
      intro ns2 hs
      first
        | (simp only [callGraph]; rcases maxDepth _ _ with _ | _ <;> simp [optionLe]; done)
        | (simp [callGraph, optionLe]; done)
        | (rename_i ih; simp only [callGraph]; exact ih ns2 hs)

/-- Full original `option_le_max_depth_graphs`:
`!ns ns1 ns2. set ns2 SUBSET set ns1 /\ LENGTH ns2 <= LENGTH ns1 ==>
option_le (max_depth_graphs ss ns ns1 funs funs2) (max_depth_graphs ss ns ns2 funs funs2)`. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "option_le_max_depth_graphs"
  (words_as_type_indexed_bitvec)]
theorem optionLe_maxDepthGraphs {width : Nat} [NeZero width] {Metadata : Type}
    (ss : Spt Nat) (funs : Spt (Nat × WordLangProgHOL (BitVec width)))
    (funs2 : Spt (Metadata × WordLangProgHOL (BitVec width))) :
    ∀ (ns ns1 ns2 : List Nat), (∀ x, x ∈ ns2 → x ∈ ns1) ∧ ns2.length ≤ ns1.length →
      optionLe (maxDepthGraphs ss ns ns1 funs funs2) (maxDepthGraphs ss ns ns2 funs funs2) := by
  intro ns
  induction ns with
  | nil => intro ns1 ns2 _; simp [maxDepthGraphs, optionLe]
  | cons h t ih =>
      intro ns1 ns2 hs
      simp only [maxDepthGraphs]
      rcases sptLookup h funs2 with _ | ⟨a, body⟩
      · simp [optionLe]
      · simp only
        apply optionLe_max_mono (by rcases sptLookup h ss with _ | _ <;> simp [optionLe])
        exact optionLe_max_mono (optionLe_maxDepth_graph ss funs h ns1 _ body ns2 hs)
          (ih ns1 ns2 hs)

/-- Full original `LENGTH_LESS_size` (local):
`!name ns funs y. ~MEM name ns /\ set ns ⊆ domain funs /\ ALL_DISTINCT ns /\
lookup name funs = SOME y ==> LENGTH ns < size funs`. -/
@[hol "cakeml/compiler/backend/proofs/word_depthProofScript.sml" "LENGTH_LESS_size"]
theorem length_less_size {α : Type} :
    ∀ (name : Nat) (ns : List Nat) (funs : Spt α) (y : α),
      name ∉ ns ∧ (∀ x, x ∈ ns → (sptLookup x funs).isSome = true) ∧ ns.Nodup ∧
        sptLookup name funs = some y → ns.length < sptSize funs := by
  rintro name ns funs y ⟨hn, hdom, hnd, hl⟩
  have keys : ∀ k, (sptLookup k funs).isSome = true → k ∈ (sptToAList funs).map Prod.fst := by
    intro k hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
    exact List.mem_map.mpr ⟨(k, v), (sptToAList_mem_iff_lookup funs k v).mpr hv, rfl⟩
  have hsub : name :: ns ⊆ (sptToAList funs).map Prod.fst := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact keys x (by simp [hl])
    · exact keys x (hdom x hx)
  have hle := List.Nodup.length_le_of_subset (List.nodup_cons.mpr ⟨hn, hnd⟩) hsub
  rw [List.length_map, LinearScan.lengthToAList, List.length_cons] at hle
  omega

end Flapjack.Compiler.Backend.WordDepthProof
