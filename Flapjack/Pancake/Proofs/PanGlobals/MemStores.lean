import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Pancake.Semantics.PanProps
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsMemory
import Flapjack.Pancake.Proofs.PanGlobals.MemStoresAppend
import Flapjack.Misc.GoodDimindex
import Flapjack.Pancake.Proofs.PanGlobals.StateRelationExact

/-!
# pan_globals `mem_stores` memory lemmas

Counterpart of `cakeml/pancake/proofs/pan_globalsProofScript.sml:243-533`
(bead `flapjack-pxn.18.5.2.27`; `mem_stores_append`, `mem_stores_memory_swap`
and `mem_stores_lookup` are the sibling modules `MemStoresAppend`,
`MemorySwap` and `MemoryLookup`): algebra of the exact tagged `panMemStoresHOL`
(`panSem$mem_stores_def`) over the total `HolWordLab` memory with a `Prop`
domain, and the word-arithmetic facts about the `bytes_in_word` stride used by
the `compile_correct` Store cases.  HOL's `'a word set` domain is a predicate;
membership is decided classically inside each statement (`letI`), with no added
premise.  `addresses` is the tagged `stack_removeProof$addresses_def` carrier.
-/

namespace Flapjack.PanGlobalsMemStores

open Flapjack
open Flapjack.Compiler.Backend.StackRemove (addresses)
open Flapjack.Pancake.PanLang

/-- Local support: `mem_stores_lookup` for any domain decision procedure (the
    tagged port is `PanGlobalsMemoryLookup.memStoresLookupHOL`, stated with the
    classical decision only). -/
private theorem memStoresLookup_gen {width : Nat} [NeZero width]
    (addrs : BitVec width → Prop) [DecidablePred addrs] :
    ∀ (addr : BitVec width) (vs : List (HolWordLab width))
      (memory m : BitVec width → HolWordLab width) (addr' : BitVec width),
      panMemStoresHOL addr vs addrs memory = some m →
        ¬ addresses addr vs.length addr' → m addr' = memory addr' := by
  intro addr vs
  induction vs generalizing addr with
  | nil =>
      intro memory m addr' h _
      simp only [panMemStoresHOL, Option.some.injEq] at h
      rw [h]
  | cons v vs ih =>
      intro memory m addr' h hnot
      simp only [panMemStoresHOL, panMemStoreHOL] at h
      by_cases hd : addrs addr
      · simp only [if_pos hd] at h
        have hne : addr' ≠ addr := fun heq => hnot (Or.inl heq)
        have htail : ¬ addresses (addr + Flapjack.Compiler.Backend.StackRemove.bytesInWord width)
            vs.length addr' := fun hin => hnot (Or.inr hin)
        rw [ih _ _ m addr' h htail, if_neg hne]
      · simp [if_neg hd] at h

/-- Local support: the stride step `a + B + B * n = a + B * (n + 1)`. -/
private theorem stride_succ {width : Nat} (a : BitVec width) (n : Nat) :
    a + BitVec.ofNat width (width / 8) + BitVec.ofNat width (width / 8) * BitVec.ofNat width n =
      a + BitVec.ofNat width (width / 8) * BitVec.ofNat width (n + 1) := by
  rw [BitVec.ofNat_add, BitVec.mul_add, BitVec.mul_one, BitVec.add_assoc,
    BitVec.add_comm (BitVec.ofNat width (width / 8))]

/-- Local support: `addresses a (n + k)` splits at the `n`-th stride.  No HOL
    original (HOL's proof uses `addresses_thm`). -/
theorem addresses_add {width : Nat} [NeZero width] (n k : Nat) :
    ∀ (a x : BitVec width), addresses a (n + k) x ↔
      addresses a n x ∨
        addresses (a + BitVec.ofNat width (width / 8) * BitVec.ofNat width n) k x := by
  induction n with
  | zero =>
      intro a x
      simp only [Nat.zero_add, BitVec.mul_zero, BitVec.add_zero]
      constructor
      · exact Or.inr
      · intro h; rcases h with h | h
        · exact h.elim
        · exact h
  | succ n ih =>
      intro a x
      rw [Nat.succ_add]
      show (x = a ∨ addresses (a + _) (n + k) x) ↔
        ((x = a ∨ addresses (a + _) n x) ∨ _)
      have := ih (a + Flapjack.Compiler.Backend.StackRemove.bytesInWord width) x
      unfold Flapjack.Compiler.Backend.StackRemove.bytesInWord at this ⊢
      rw [this, stride_succ]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

/-- Local support: `sizeOfShapesHOL` is the sum of the sizes. -/
private theorem sizeOfShapesHOL_eq_sum :
    ∀ shapes : List ShapeHOL, sizeOfShapesHOL shapes = (shapes.map sizeOfShapeHOL).sum
  | [] => by simp
  | shape :: rest => by simp [sizeOfShapesHOL_eq_sum rest]

/-- Local support: `EVERY (is_wf_shape ctxt)` as the list helper. -/
private theorem isWfShapesExactHOL_iff (context : StructContextExact) :
    ∀ shapes : List ShapeHOL,
      isWfShapesExactHOL context shapes = true ↔ ∀ sh ∈ shapes, isWfShapeExactHOL context sh = true
  | [] => by simp
  | shape :: rest => by simp [isWfShapesExactHOL_iff context rest]

/-- Local support: both parts of `mem_stores_load_disjoint` over the internal
    list well-formedness helper. -/
private theorem memStoresLoadDisjoint_aux {width : Nat} [NeZero width]
    (addr : BitVec width) (vs : List (HolWordLab width)) (addrs : BitVec width → Prop)
    [DecidablePred addrs]
    (memory m : BitVec width → HolWordLab width)
    (hm : panMemStoresHOL addr vs addrs memory = some m) :
    (∀ (sh : ShapeHOL) (addr' : BitVec width),
      isWfShapeExactHOL [] sh = true →
      (∀ x, addresses addr' (sizeOfShapeHOL sh) x → ¬ addresses addr vs.length x) →
      memLoadHOLExact sh addr' addrs m [] = memLoadHOLExact sh addr' addrs memory []) ∧
    (∀ (shs : List ShapeHOL) (addr' : BitVec width),
      isWfShapesExactHOL [] shs = true →
      (∀ x, addresses addr' (sizeOfShapesHOL shs) x → ¬ addresses addr vs.length x) →
      memLoadsHOLExact shs addr' addrs m [] = memLoadsHOLExact shs addr' addrs memory []) := by
  have hcons : ∀ (sh : ShapeHOL) (rest : List ShapeHOL),
      (∀ addr' : BitVec width, isWfShapeExactHOL [] sh = true →
        (∀ x, addresses addr' (sizeOfShapeHOL sh) x → ¬ addresses addr vs.length x) →
        memLoadHOLExact sh addr' addrs m [] = memLoadHOLExact sh addr' addrs memory []) →
      (∀ addr' : BitVec width, isWfShapesExactHOL [] rest = true →
        (∀ x, addresses addr' (sizeOfShapesHOL rest) x → ¬ addresses addr vs.length x) →
        memLoadsHOLExact rest addr' addrs m [] = memLoadsHOLExact rest addr' addrs memory []) →
      ∀ addr' : BitVec width, isWfShapesExactHOL [] (sh :: rest) = true →
        (∀ x, addresses addr' (sizeOfShapesHOL (sh :: rest)) x → ¬ addresses addr vs.length x) →
        memLoadsHOLExact (sh :: rest) addr' addrs m [] =
          memLoadsHOLExact (sh :: rest) addr' addrs memory [] := by
    intro sh rest ihSh ihRest addr' hwf hdis
    simp only [isWfShapesExactHOL_cons, Bool.and_eq_true] at hwf
    simp only [sizeOfShapesHOL_cons] at hdis
    rw [memLoadsHOLExact, memLoadsHOLExact,
      sizeOfShapeWithContextHOL_eq_nil sh hwf.1 []]
    rw [ihSh addr' hwf.1 (fun x hx => hdis x ((addresses_add _ _ addr' x).2 (Or.inl hx))),
      ihRest (addr' + bytesInWordHOL width * BitVec.ofNat width (sizeOfShapeHOL sh)) hwf.2 (fun x hx => hdis x ((addresses_add _ _ addr' x).2 (Or.inr hx)))]
  have hshape : ∀ (sh : ShapeHOL) (addr' : BitVec width),
      isWfShapeExactHOL [] sh = true →
      (∀ x, addresses addr' (sizeOfShapeHOL sh) x → ¬ addresses addr vs.length x) →
      memLoadHOLExact sh addr' addrs m [] = memLoadHOLExact sh addr' addrs memory [] := by
    intro sh
    induction sh using ShapeHOL.rec (motive_2 := fun shs =>
        ∀ addr' : BitVec width, isWfShapesExactHOL [] shs = true →
          (∀ x, addresses addr' (sizeOfShapesHOL shs) x → ¬ addresses addr vs.length x) →
          memLoadsHOLExact shs addr' addrs m [] = memLoadsHOLExact shs addr' addrs memory []) with
    | one =>
        intro addr' _ hdis
        rw [memLoadHOLExact, memLoadHOLExact]
        have := memStoresLookup_gen addrs addr vs memory m addr' hm
          (hdis addr' (by simp [addresses]))
        rw [this]
    | comb shapes ih =>
        intro addr' hwf hdis
        rw [memLoadHOLExact, memLoadHOLExact]
        rw [ih addr' (by simpa using hwf) (by simpa using hdis)]
    | named name =>
        intro _ hwf _
        simp at hwf
    | nil =>
        rw [memLoadsHOLExact, memLoadsHOLExact]
    | cons sh rest ihSh ihRest =>
        rename_i addr' hwf hdis
        exact hcons sh rest ihSh ihRest addr' hwf hdis
  refine ⟨hshape, ?_⟩
  intro shs
  induction shs with
  | nil => intro addr' _ _; rw [memLoadsHOLExact, memLoadsHOLExact]
  | cons sh rest ihRest => exact hcons sh rest (hshape sh) ihRest

/-- Exact HOL `mem_stores_load_disjoint` (`pan_globalsProofScript.sml:323-364`).
    HOL `DISJOINT s t` over predicate sets is `∀ x, s x → ¬ t x`; `EVERY` is
    list membership. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_load_disjoint"
  (words_as_type_indexed_bitvec)]
theorem memStoresLoadDisjointHOL {width : Nat} [NeZero width] :
    (∀ (sh : ShapeHOL) (addr : BitVec width) (vs : List (HolWordLab width))
      (addrs : BitVec width → Prop) (memory m : BitVec width → HolWordLab width)
      (stcs : StructContextExact) (addr' : BitVec width),
      letI : DecidablePred addrs := fun a => Classical.propDecidable (addrs a)
      panMemStoresHOL addr vs addrs memory = some m ∧
        stcs = [] ∧ isWfShapeExactHOL stcs sh = true ∧
        (∀ x, addresses addr' (sizeOfShapeHOL sh) x → ¬ addresses addr vs.length x) →
        memLoadHOLExact sh addr' addrs m stcs = memLoadHOLExact sh addr' addrs memory []) ∧
    (∀ (shs : List ShapeHOL) (addr : BitVec width) (vs : List (HolWordLab width))
      (addrs : BitVec width → Prop) (memory m : BitVec width → HolWordLab width)
      (stcs : StructContextExact) (addr' : BitVec width),
      letI : DecidablePred addrs := fun a => Classical.propDecidable (addrs a)
      panMemStoresHOL addr vs addrs memory = some m ∧
        stcs = [] ∧ (∀ sh ∈ shs, isWfShapeExactHOL stcs sh = true) ∧
        (∀ x, addresses addr' (shs.map sizeOfShapeHOL).sum x → ¬ addresses addr vs.length x) →
        memLoadsHOLExact shs addr' addrs m stcs = memLoadsHOLExact shs addr' addrs memory []) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro sh addr vs addrs memory m stcs addr' ⟨hm, rfl, hwf, hdis⟩
    exact (memStoresLoadDisjoint_aux addr vs addrs memory m hm).1 sh addr' hwf hdis
  · rintro shs addr vs addrs memory m stcs addr' ⟨hm, rfl, hwf, hdis⟩
    exact (memStoresLoadDisjoint_aux addr vs addrs memory m hm).2 shs addr'
      ((isWfShapesExactHOL_iff [] shs).2 hwf) (by rw [sizeOfShapesHOL_eq_sum]; exact hdis)

/-- Local support: a successful empty-context load of a well-formed shape
    covers its `size_of_shape` addresses by the domain. -/
private theorem memLoad_domain_cover {width : Nat} [NeZero width]
    (addrs : BitVec width → Prop) [DecidablePred addrs]
    (memory : BitVec width → HolWordLab width) :
    (∀ (sh : ShapeHOL) (addr : BitVec width) (v : ValueHOL width),
      memLoadHOLExact sh addr addrs memory [] = some v → isWfShapeExactHOL [] sh = true →
      ∀ x, addresses addr (sizeOfShapeHOL sh) x → addrs x) ∧
    (∀ (shs : List ShapeHOL) (addr : BitVec width) (vs : List (ValueHOL width)),
      memLoadsHOLExact shs addr addrs memory [] = some vs → isWfShapesExactHOL [] shs = true →
      ∀ x, addresses addr (sizeOfShapesHOL shs) x → addrs x) := by
  have hcons : ∀ (sh : ShapeHOL) (rest : List ShapeHOL),
      (∀ (addr : BitVec width) (v : ValueHOL width),
        memLoadHOLExact sh addr addrs memory [] = some v → isWfShapeExactHOL [] sh = true →
        ∀ x, addresses addr (sizeOfShapeHOL sh) x → addrs x) →
      (∀ (addr : BitVec width) (vs : List (ValueHOL width)),
        memLoadsHOLExact rest addr addrs memory [] = some vs → isWfShapesExactHOL [] rest = true →
        ∀ x, addresses addr (sizeOfShapesHOL rest) x → addrs x) →
      ∀ (addr : BitVec width) (vs : List (ValueHOL width)),
        memLoadsHOLExact (sh :: rest) addr addrs memory [] = some vs →
        isWfShapesExactHOL [] (sh :: rest) = true →
        ∀ x, addresses addr (sizeOfShapesHOL (sh :: rest)) x → addrs x := by
    intro sh rest ihSh ihRest addr vs h hwf x hx
    simp only [isWfShapesExactHOL_cons, Bool.and_eq_true] at hwf
    simp only [sizeOfShapesHOL_cons] at hx
    rw [memLoadsHOLExact, sizeOfShapeWithContextHOL_eq_nil sh hwf.1 []] at h
    cases h1 : memLoadHOLExact sh addr addrs memory [] with
    | none => rw [h1] at h; cases h
    | some v =>
        cases h2 : memLoadsHOLExact rest
            (addr + bytesInWordHOL width * BitVec.ofNat width (sizeOfShapeHOL sh))
            addrs memory [] with
        | none => rw [h1, h2] at h; cases h
        | some vs' =>
            rcases (addresses_add _ _ addr x).1 hx with hx | hx
            · exact ihSh addr v h1 hwf.1 x hx
            · exact ihRest _ vs' h2 hwf.2 x hx
  have hshape : ∀ (sh : ShapeHOL) (addr : BitVec width) (v : ValueHOL width),
      memLoadHOLExact sh addr addrs memory [] = some v → isWfShapeExactHOL [] sh = true →
      ∀ x, addresses addr (sizeOfShapeHOL sh) x → addrs x := by
    intro sh
    induction sh using ShapeHOL.rec (motive_2 := fun shs =>
        ∀ (addr : BitVec width) (vs : List (ValueHOL width)),
          memLoadsHOLExact shs addr addrs memory [] = some vs → isWfShapesExactHOL [] shs = true →
          ∀ x, addresses addr (sizeOfShapesHOL shs) x → addrs x) with
    | one =>
        intro addr v h _ x hx
        rw [memLoadHOLExact] at h
        by_cases hd : addrs addr
        · simp only [sizeOfShapeHOL_one] at hx
          rcases hx with rfl | hx
          · exact hd
          · exact hx.elim
        · rw [if_neg hd] at h; cases h
    | comb shapes ih =>
        intro addr v h hwf x hx
        rw [memLoadHOLExact] at h
        cases hs : memLoadsHOLExact shapes addr addrs memory [] with
        | none => rw [hs] at h; cases h
        | some vs => exact ih addr vs hs (by simpa using hwf) x (by simpa using hx)
    | named name =>
        intro _ _ _ hwf
        simp at hwf
    | nil =>
        rename_i addr vs h hwf x hx
        exact hx.elim
    | cons sh rest ihSh ihRest =>
        rename_i addr vs h hwf x hx
        exact hcons sh rest ihSh ihRest addr vs h hwf x hx
  refine ⟨hshape, ?_⟩
  intro shs
  induction shs with
  | nil => intro _ _ _ _ x hx; exact hx.elim
  | cons sh rest ihRest => exact hcons sh rest (hshape sh) ihRest

/-- Exact HOL `mem_load_mem_store` (`pan_globalsProofScript.sml:266-307`),
    all three conjuncts of HOL's `mem_load_ind` statement (the third is HOL's
    trivial `mem_load_flds` conjunct `... ⇒ T`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_load_mem_store"
  (words_as_type_indexed_bitvec)]
theorem memLoadMemStoreHOL {width : Nat} [NeZero width] :
    (∀ (s : ShapeHOL) (addr : BitVec width) (addrs : BitVec width → Prop)
      (memory : BitVec width → HolWordLab width) (sctxt : StructContextExact)
      (v w : ValueHOL width),
      letI : DecidablePred addrs := fun a => Classical.propDecidable (addrs a)
      memLoadHOLExact s addr addrs memory sctxt = some v ∧
        sctxt = [] ∧ isWfShapeExactHOL sctxt s = true ∧ shapeOfHOLExact w = s →
        ∃ m, panMemStoresHOL addr (flattenHOL w) addrs memory = some m) ∧
    (∀ (ss : List ShapeHOL) (addr : BitVec width) (addrs : BitVec width → Prop)
      (memory : BitVec width → HolWordLab width) (sctxt : StructContextExact)
      (vs ws : List (ValueHOL width)),
      letI : DecidablePred addrs := fun a => Classical.propDecidable (addrs a)
      memLoadsHOLExact ss addr addrs memory sctxt = some vs ∧
        sctxt = [] ∧ (∀ s ∈ ss, isWfShapeExactHOL sctxt s = true) ∧
        ss = ws.map shapeOfHOLExact →
        ∃ m, panMemStoresHOL addr (ws.map (fun a => flattenHOL a)).flatten addrs memory = some m) ∧
    (∀ (fs : List (MlStringHOLM × ShapeHOL)) (addr : BitVec width)
      (addrs : BitVec width → Prop) (memory : BitVec width → HolWordLab width)
      (sctxt : StructContextExact) (vfs : List (MlStringHOLM × ValueHOL width)),
      letI : DecidablePred addrs := fun a => Classical.propDecidable (addrs a)
      memLoadFldsHOLExact fs addr addrs memory sctxt = some vfs ∧ sctxt = [] ∧ True → True) := by
  classical
  refine ⟨?_, ?_, fun _ _ _ _ _ _ _ => trivial⟩
  · rintro s addr addrs memory sctxt v w ⟨h, rfl, hwf, rfl⟩
    have hcover := (memLoad_domain_cover addrs memory).1 _ addr v h hwf
    rw [← flattenHOL_length_eq_sizeOfShapeHOL w hwf] at hcover
    exact Flapjack.PanGlobalsInitGlobalsMemory.memStoresAddrsIsSomeHOL addr _ addrs memory hcover
  · rintro ss addr addrs memory sctxt vs ws ⟨h, rfl, hwf, rfl⟩
    have hwf' := (isWfShapesExactHOL_iff [] _).2 hwf
    have hcover := (memLoad_domain_cover addrs memory).2 _ addr vs h hwf'
    rw [← lengthFlattenHOLs_eq_sizeOfShapesHOL ws hwf'] at hcover
    exact Flapjack.PanGlobalsInitGlobalsMemory.memStoresAddrsIsSomeHOL addr _ addrs memory hcover

/-- Local support: without wrap-around, a block of `n1` strides is disjoint
    from the next `n2` strides at HOL's good dimensions. -/
private theorem addresses_disjoint_stride {width : Nat} [NeZero width] (hw : goodDimindex width)
    (a : BitVec width) (n1 n2 : Nat) (hlt : (n1 + n2) * (width / 8) < 2 ^ width) :
    ∀ x, addresses a n1 x →
      ¬ addresses (a + BitVec.ofNat width (width / 8) * BitVec.ofNat width n1) n2 x := by
  intro x h1 h2
  rw [Flapjack.Compiler.Backend.StackRemove.mem_addresses] at h1 h2
  obtain ⟨i, hi, rfl⟩ := h1
  obtain ⟨j, hj, hx⟩ := h2
  have := congrArg BitVec.toNat hx
  unfold Flapjack.Compiler.Backend.StackRemove.bytesInWord at this
  rcases hw with rfl | rfl <;>
  · simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at this
    simp only [Nat.reducePow, Nat.reduceDiv] at this hlt
    omega

section LoadBack

variable {width : Nat} [NeZero width] (addrs : BitVec width → Prop) [DecidablePred addrs]

mutual
  /-- Local support: first conjunct of `mem_stores_mem_load_back`. -/
  private theorem loadBack_val (hw : goodDimindex width) :
      ∀ (val : ValueHOL width) (addr : BitVec width) (memory m : BitVec width → HolWordLab width),
        panMemStoresHOL addr (flattenHOL val) addrs memory = some m →
        (flattenHOL val).length * (width / 8) < 2 ^ width →
        isWfShapeExactHOL [] (shapeOfHOLExact val) = true →
        memLoadHOLExact (shapeOfHOLExact val) addr addrs m [] = some val
    | .val w, addr, memory, m, hm, _, _ => by
        simp only [flattenHOL, panMemStoresHOL, panMemStoreHOL] at hm
        simp only [shapeOfHOLExact]
        rw [memLoadHOLExact]
        by_cases hd : addrs addr
        · simp only [if_pos hd, Option.some.injEq] at hm
          rw [if_pos hd, ← hm]
          simp
        · simp [if_neg hd] at hm
    | .rStruct fields, addr, memory, m, hm, hlen, hwf => by
        simp only [flattenHOL] at hm hlen
        simp only [shapeOfHOLExact, isWfShapeExactHOL_comb] at hwf ⊢
        rw [memLoadHOLExact, loadBack_vals hw fields addr memory m hm hlen hwf]
    | .nStruct name fields, _, _, _, _, _, hwf => by
        simp [shapeOfHOLExact, isWfShapeExactHOL_named, structContextLookupHOL_nil] at hwf

  /-- Local support: second conjunct of `mem_stores_mem_load_back`. -/
  private theorem loadBack_vals (hw : goodDimindex width) :
      ∀ (vals : List (ValueHOL width)) (addr : BitVec width)
        (memory m : BitVec width → HolWordLab width),
        panMemStoresHOL addr (vals.map flattenHOL).flatten addrs memory = some m →
        (vals.map flattenHOL).flatten.length * (width / 8) < 2 ^ width →
        isWfShapesExactHOL [] (vals.map shapeOfHOLExact) = true →
        memLoadsHOLExact (vals.map shapeOfHOLExact) addr addrs m [] = some vals
    | [], _, _, _, _, _, _ => by
        simp only [List.map_nil]
        rw [memLoadsHOLExact]
    | val :: vals, addr, memory, m, hm, hlen, hwf => by
        simp only [List.map_cons, List.flatten_cons] at hm hlen hwf ⊢
        simp only [isWfShapesExactHOL_cons, Bool.and_eq_true] at hwf
        have happ := Flapjack.PanGlobalsMemStoresAppend.memStoresAppend addr (flattenHOL val) addrs memory
          (vals.map flattenHOL).flatten
        rw [hm] at happ
        cases h1 : panMemStoresHOL addr (flattenHOL val) addrs memory with
        | none => rw [h1] at happ; cases happ
        | some m1 =>
            rw [h1] at happ
            simp only at happ
            have hsize := flattenHOL_length_eq_sizeOfShapeHOL val hwf.1
            rw [List.length_append] at hlen
            have hlen1 : (flattenHOL val).length * (width / 8) < 2 ^ width := by
              have := Nat.mul_le_mul_right (width / 8)
                (Nat.le_add_right (flattenHOL val).length (vals.map flattenHOL).flatten.length)
              omega
            have hlen2 : (vals.map flattenHOL).flatten.length * (width / 8) < 2 ^ width := by
              have := Nat.mul_le_mul_right (width / 8)
                (Nat.le_add_left (vals.map flattenHOL).flatten.length (flattenHOL val).length)
              omega
            have hfirst : memLoadHOLExact (shapeOfHOLExact val) addr addrs m [] =
                memLoadHOLExact (shapeOfHOLExact val) addr addrs m1 [] :=
              (memStoresLoadDisjoint_aux _ _ addrs m1 m happ.symm).1 _ addr hwf.1
                (by
                  rw [← hsize]
                  exact addresses_disjoint_stride hw addr _ _ hlen)
            rw [memLoadsHOLExact, sizeOfShapeWithContextHOL_eq_nil _ hwf.1 [], ← hsize, hfirst,
              loadBack_val hw val addr memory m1 h1 hlen1 hwf.1]
            have hrest := loadBack_vals hw vals _ m1 m happ.symm hlen2 hwf.2
            unfold panBytesInWord at hrest
            unfold bytesInWordHOL
            rw [hrest]
end

end LoadBack

/-- Exact HOL `mem_stores_mem_load_back` (`pan_globalsProofScript.sml:366-423`).
    `dimword(:'a)` is `2 ^ width` and `w2n` is `BitVec.toNat`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_mem_load_back"
  (words_as_type_indexed_bitvec)]
theorem memStoresMemLoadBackHOL {width : Nat} [NeZero width] :
    (∀ (val : ValueHOL width) (addr : BitVec width) (addrs : BitVec width → Prop)
      (memory m : BitVec width → HolWordLab width) (sctxt : StructContextExact),
      letI : DecidablePred addrs := fun a => Classical.propDecidable (addrs a)
      panMemStoresHOL addr (flattenHOL val) addrs memory = some m ∧
        (flattenHOL val).length * (panBytesInWord width).toNat < 2 ^ width ∧
        isWfShapeExactHOL sctxt (shapeOfHOLExact val) = true ∧ sctxt = [] ∧
        goodDimindex width →
        memLoadHOLExact (shapeOfHOLExact val) addr addrs m sctxt = some val) ∧
    (∀ (vals : List (ValueHOL width)) (addr : BitVec width) (addrs : BitVec width → Prop)
      (memory m : BitVec width → HolWordLab width) (sctxt : StructContextExact),
      letI : DecidablePred addrs := fun a => Classical.propDecidable (addrs a)
      panMemStoresHOL addr (vals.map (fun a => flattenHOL a)).flatten addrs memory = some m ∧
        (vals.map (fun a => flattenHOL a)).flatten.length * (panBytesInWord width).toNat <
          2 ^ width ∧
        (∀ s ∈ vals.map shapeOfHOLExact, isWfShapeExactHOL sctxt s = true) ∧ sctxt = [] ∧
        goodDimindex width →
        memLoadsHOLExact (vals.map shapeOfHOLExact) addr addrs m sctxt = some vals) := by
  classical
  have hB : ∀ hw : goodDimindex width, (panBytesInWord width).toNat = width / 8 := by
    intro hw
    rcases hw with rfl | rfl <;> rfl
  refine ⟨?_, ?_⟩
  · rintro val addr addrs memory m sctxt ⟨hm, hlen, hwf, rfl, hw⟩
    rw [hB hw] at hlen
    exact loadBack_val addrs hw val addr memory m hm hlen hwf
  · rintro vals addr addrs memory m sctxt ⟨hm, hlen, hwf, rfl, hw⟩
    rw [hB hw] at hlen
    exact loadBack_vals addrs hw vals addr memory m hm hlen ((isWfShapesExactHOL_iff [] _).2 hwf)

/-- Exact HOL `LESS_MULT_MONO'` (`pan_globalsProofScript.sml:425-429`, local). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "LESS_MULT_MONO'"]
theorem lessMultMono' {a m n : Nat} : 0 < a → (a * m < a * n ↔ m < n) :=
  fun ha => Nat.mul_lt_mul_left ha

/-- Exact HOL `w2n_add_alt` (`pan_globalsProofScript.sml:448-456`);
    `dimword(:'a)` is `2 ^ width`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "w2n_add_alt"
  (words_as_type_indexed_bitvec)]
theorem w2nAddAltHOL {width : Nat} [NeZero width] :
    ∀ (a b : BitVec width),
      a.toNat + b.toNat < 2 ^ width → a.toNat + b.toNat = (a + b).toNat := by
  intro a b h
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

/-- Local support: HOL `byte_aligned` at the good dimensions is divisibility of
    `w2n` by the byte count. -/
private theorem byteAligned_toNat {width : Nat} [NeZero width] (hw : goodDimindex width)
    (a : BitVec width) (h : panGlobalsByteAlignedHOL a) : a.toNat % (width / 8) = 0 := by
  rcases hw with rfl | rfl
  · have h' : BitVec.ofNat 32 ((a.toNat / 4) * 4) = a := h
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    have := a.isLt
    simp only [Nat.reduceDiv]
    omega
  · have h' : BitVec.ofNat 64 ((a.toNat / 8) * 8) = a := h
    have := congrArg BitVec.toNat h'
    simp only [BitVec.toNat_ofNat] at this
    have := a.isLt
    simp only [Nat.reduceDiv]
    omega

/-- Exact HOL `byte_aligned_mul_bytes_in_word` (`pan_globalsProofScript.sml:431-446`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "byte_aligned_mul_bytes_in_word"
  (words_as_type_indexed_bitvec)]
theorem byteAlignedMulBytesInWordHOL {width : Nat} [NeZero width] (a : BitVec width) :
    goodDimindex width ∧ panGlobalsByteAlignedHOL a →
      ∃ b : BitVec width, a = b * panBytesInWord width ∧
        b.toNat * (panBytesInWord width).toNat < 2 ^ width := by
  rintro ⟨hw, ha⟩
  have hmod := byteAligned_toNat hw a ha
  have hlt := a.isLt
  refine ⟨BitVec.ofNat width (a.toNat / (width / 8)), ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    unfold panBytesInWord
    rcases hw with rfl | rfl <;>
    · simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.reduceDiv, Nat.reducePow] at hmod hlt ⊢
      omega
  · unfold panBytesInWord
    rcases hw with rfl | rfl <;>
    · simp only [BitVec.toNat_ofNat, Nat.reduceDiv, Nat.reducePow] at hmod hlt ⊢
      omega

/-- Exact HOL `good_dimindex_w2n_add` (`pan_globalsProofScript.sml:458-488`);
    HOL `-1w` is `-1 : BitVec width`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "good_dimindex_w2n_add"
  (words_as_type_indexed_bitvec)]
theorem goodDimindexW2nAddHOL {width : Nat} [NeZero width] (a : BitVec width) :
    goodDimindex width ∧ panGlobalsByteAlignedHOL a ∧ a ≠ -1 * panBytesInWord width →
      a.toNat + (panBytesInWord width).toNat = (a + panBytesInWord width).toNat := by
  rintro ⟨hw, ha, hne⟩
  have hmod := byteAligned_toNat hw a ha
  have hlt := a.isLt
  unfold panBytesInWord at hne ⊢
  rcases hw with rfl | rfl
  · have hne' : a.toNat ≠ 2 ^ 32 - 4 := by
      intro h; apply hne; apply BitVec.eq_of_toNat_eq; rw [h]; decide
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reduceDiv, Nat.reducePow, Nat.reduceSub]
      at hmod hlt hne' ⊢
    omega
  · have hne' : a.toNat ≠ 2 ^ 64 - 8 := by
      intro h; apply hne; apply BitVec.eq_of_toNat_eq; rw [h]; decide
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reduceDiv, Nat.reducePow, Nat.reduceSub]
      at hmod hlt hne' ⊢
    omega

/-- Local support: a successful `mem_stores` covers its addresses by the domain. -/
private theorem memStores_cover {width : Nat} [NeZero width]
    (addrs : BitVec width → Prop) [DecidablePred addrs] :
    ∀ (addr : BitVec width) (ws : List (HolWordLab width))
      (memory m : BitVec width → HolWordLab width),
      panMemStoresHOL addr ws addrs memory = some m →
        ∀ x, addresses addr ws.length x → addrs x := by
  intro addr ws
  induction ws generalizing addr with
  | nil => intro _ _ _ x hx; exact hx.elim
  | cons w ws ih =>
      intro memory m h x hx
      simp only [panMemStoresHOL, panMemStoreHOL] at h
      by_cases hd : addrs addr
      · simp only [if_pos hd] at h
        rcases hx with rfl | hx
        · exact hd
        · exact ih _ _ m h x hx
      · simp [if_neg hd] at h

/-- Exact HOL `mem_stores_bounded_length` (`pan_globalsProofScript.sml:490-533`). -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "mem_stores_bounded_length"
  (words_as_type_indexed_bitvec)]
theorem memStoresBoundedLengthHOL {width : Nat} [NeZero width] :
    ∀ (addr : BitVec width) (ws : List (HolWordLab width)) (addrs : BitVec width → Prop)
      (memory m : BitVec width → HolWordLab width) (addr' : BitVec width),
      letI : DecidablePred addrs := fun a => Classical.propDecidable (addrs a)
      panMemStoresHOL addr ws addrs memory = some m ∧ ¬ addrs addr' ∧
        panGlobalsByteAlignedHOL addr ∧ panGlobalsByteAlignedHOL addr' ∧ goodDimindex width →
        (panBytesInWord width).toNat * ws.length ≤ (addr' - addr).toNat := by
  classical
  rintro addr ws addrs memory m addr' ⟨hm, hnot, ha, ha', hw⟩
  have hcover := memStores_cover addrs addr ws memory m hm
  have hmod := byteAligned_toNat hw addr ha
  have hmod' := byteAligned_toNat hw addr' ha'
  have hlt := addr.isLt
  have hlt' := addr'.isLt
  apply Classical.byContradiction
  intro hgt
  apply hnot
  apply hcover
  rw [Flapjack.Compiler.Backend.StackRemove.mem_addresses]
  refine ⟨(addr' - addr).toNat / (width / 8), ?_, ?_⟩
  · unfold panBytesInWord at hgt
    rcases hw with rfl | rfl <;>
    · simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reduceDiv, Nat.reducePow]
        at hgt hmod hmod' hlt hlt' ⊢
      omega
  · apply BitVec.eq_of_toNat_eq
    unfold Flapjack.Compiler.Backend.StackRemove.bytesInWord
    rcases hw with rfl | rfl <;>
    · simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_ofNat,
        Nat.reduceDiv, Nat.reducePow] at hmod hmod' hlt hlt' ⊢
      omega

end Flapjack.PanGlobalsMemStores
