module

public import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation
public import Flapjack.Compiler.Backend.BackendCommon.SmallInt
public import Flapjack.Misc.ListEl
public import Flapjack.FiniteMap.SubmapExact
public import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Value and environment relations for the TMC semantic simulation. -/
namespace Flapjack.Compiler.Backend.BviTmc
open BvlSem

private def maptoBroadlookup (f : HolFiniteMapExact Nat Nat) : Nat → Option Nat := f.lookup
private def mapofBroad (lookup : Nat → Option Nat)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact Nat Nat :=
  ⟨lookup, support⟩

theorem holFmapAsFiniteSupportParamWitness_valueRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Values are unchanged except that reference pointers are translated by
the finite pointer map. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "v_rel"
  (fmap_as_finite_support_parameters := [f])]
inductive valueRel (f : HolFiniteMapExact Nat Nat) : Value → Value → Prop where
  | number (i : Int) : valueRel f (.number i) (.number i)
  | word64 (w : BitVec 64) : valueRel f (.word64 w) (.word64 w)
  | block (tag : Nat) (xs ys : List Value) :
      List.Forall₂ (valueRel f) xs ys → valueRel f (.block tag xs) (.block tag ys)
  | codePtr (n : Nat) : valueRel f (.codePtr n) (.codePtr n)
  | refPtr (n m : Nat) (b : Bool) : f.lookup n = some m → valueRel f (.refPtr b n) (.refPtr b m)

theorem holFmapAsFiniteSupportParamWitness_refRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Related reference cells contain related values; mutable blocks are
intentionally absent from the source relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "ref_rel"
  (fmap_as_finite_support_parameters := [f])]
inductive refRel (f : HolFiniteMapExact Nat Nat) : Ref Value → Ref Value → Prop where
  | byteArray (b : Bool) (bytes : List (BitVec 8)) : refRel f (.byteArray b bytes) (.byteArray b bytes)
  | valueArray (xs ys : List Value) : List.Forall₂ (valueRel f) xs ys → refRel f (.valueArray xs) (.valueArray ys)
  | thunk (mode : AstHOL.ThunkMode) (x y : Value) : valueRel f x y → refRel f (.thunk mode x) (.thunk mode y)

theorem holFmapAsFiniteSupportParamWitness_envRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- An optimized environment has two additional values describing the
mutable hole; the non-optimized relation permits arbitrary extra values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_def"
  (fmap_as_finite_support_parameters := [f])]
noncomputable def envRel (opt : Bool) (f : HolFiniteMapExact Nat Nat) (source target : List Value) : Prop :=
  ∃ xs ys, target = xs ++ ys ∧ List.Forall₂ (valueRel f) source xs ∧
    (opt = true → ys.length = 2 ∧ ∃ ptr idx,
      holEl 0 ys = .refPtr false ptr ∧ holEl 1 ys = .number idx ∧ BackendCommon.smallEnoughInt idx)

theorem holFmapAsFiniteSupportParamWitness_valueRel_submap_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_valueRel_submap_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl

/-- Extending the pointer map preserves related values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "v_rel_submap"
  (fmap_as_finite_support_parameters := [f, g])]
theorem valueRel_submap (f : HolFiniteMapExact Nat Nat) (v1 v2 : Value) (g : HolFiniteMapExact Nat Nat)
    (h : valueRel f v1 v2 ∧ f.submap g) : valueRel g v1 v2 := by
  obtain ⟨related, submap⟩ := h
  cases related with
  | number i => exact .number i
  | word64 w => exact .word64 w
  | codePtr n => exact .codePtr n
  | refPtr n m b lookup => exact .refPtr n m b (submap n m lookup)
  | block tag xs ys pairs =>
    apply valueRel.block
    have each : ∀ x ∈ xs, ∀ y, valueRel f x y → valueRel g x y := by
      intro x member y rel
      exact valueRel_submap f x y g ⟨rel, submap⟩
    induction pairs with
    | nil => exact .nil
    | cons rel rest ih =>
      apply List.Forall₂.cons
      · exact each _ (by simp) _ rel
      · apply ih
        intro x member y rel
        exact each x (by simp [member]) y rel
termination_by sizeOf v1
decreasing_by
  have smaller := List.sizeOf_lt_of_mem member
  subst v1
  simp_wf
  omega

theorem holFmapAsFiniteSupportParamWitness_listRel_submap_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_listRel_submap_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl

/-- Extending the pointer map preserves related lists. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "list_rel_submap"
  (fmap_as_finite_support_parameters := [f, g])]
theorem listRel_submap (f : HolFiniteMapExact Nat Nat) (g : HolFiniteMapExact Nat Nat)
    (source target : List Value) (h : List.Forall₂ (valueRel f) source target ∧ f.submap g) :
    List.Forall₂ (valueRel g) source target := by
  obtain ⟨related, submap⟩ := h
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (valueRel_submap f _ _ g ⟨head, submap⟩) ih

theorem holFmapAsFiniteSupportParamWitness_envRel_submap_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_envRel_submap_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl

/-- Extending the pointer map preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_submap"
  (fmap_as_finite_support_parameters := [f, g])]
theorem envRel_submap (opt : Bool) (f : HolFiniteMapExact Nat Nat) (g : HolFiniteMapExact Nat Nat)
    (source target : List Value) (h : envRel opt f source target ∧ f.submap g) :
    envRel opt g source target := by
  obtain ⟨related, submap⟩ := h
  obtain ⟨xs, ys, equal, pairs, extras⟩ := related
  exact ⟨xs, ys, equal, listRel_submap f g source xs ⟨pairs, submap⟩, extras⟩

theorem holFmapAsFiniteSupportParamWitness_envRel_relax_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Dropping the optimized-hole requirement preserves the environment relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_relax_opt"
  (fmap_as_finite_support_parameters := [f])]
theorem envRel_relax (opt : Bool) (f : HolFiniteMapExact Nat Nat) (source target : List Value)
    (related : envRel opt f source target) : envRel false f source target := by
  obtain ⟨xs, ys, equal, pairs, _⟩ := related
  exact ⟨xs, ys, equal, pairs, by simp⟩

theorem holFmapAsFiniteSupportParamWitness_envRel_cons_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Prefixing related values preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_cons"
  (fmap_as_finite_support_parameters := [f])]
theorem envRel_cons (opt : Bool) (f : HolFiniteMapExact Nat Nat) (source target : List Value)
    (a b : Value) (h : envRel opt f source target ∧ valueRel f a b) :
    envRel opt f (a :: source) (b :: target) := by
  obtain ⟨related, values⟩ := h
  obtain ⟨xs, ys, rfl, pairs, extras⟩ := related
  exact ⟨b :: xs, ys, rfl, .cons values pairs, extras⟩

theorem holFmapAsFiniteSupportParamWitness_envRel_append_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Prefixing lists of related values preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_append"
  (fmap_as_finite_support_parameters := [f])]
theorem envRel_append (opt : Bool) (f : HolFiniteMapExact Nat Nat) (source target a b : List Value)
    (h : envRel opt f source target ∧ List.Forall₂ (valueRel f) a b) :
    envRel opt f (a ++ source) (b ++ target) := by
  obtain ⟨related, values⟩ := h
  obtain ⟨xs, ys, rfl, pairs, extras⟩ := related
  refine ⟨b ++ xs, ys, by simp [List.append_assoc], ?_, extras⟩
  induction values with
  | nil => exact pairs
  | cons head tail ih => exact .cons head ih

theorem holFmapAsFiniteSupportParamWitness_envRel_length_opt_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Optimized environments contain precisely two additional values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_length_opt"
  (fmap_as_finite_support_parameters := [f])]
theorem envRel_length_opt (f : HolFiniteMapExact Nat Nat) (source target : List Value)
    (related : envRel true f source target) : target.length = source.length + 2 := by
  obtain ⟨xs, ys, rfl, pairs, extras⟩ := related
  have equal := pairs.length_eq
  have two := (extras rfl).1
  simp [equal, two]

theorem holFmapAsFiniteSupportParamWitness_envRel_length_non_opt_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- An unoptimized target environment is at least as long as the source. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_length_non_opt"
  (fmap_as_finite_support_parameters := [f])]
theorem envRel_length_non_opt (f : HolFiniteMapExact Nat Nat) (source target : List Value)
    (related : envRel false f source target) : source.length ≤ target.length := by
  obtain ⟨xs, ys, rfl, pairs, _⟩ := related
  have equal := pairs.length_eq
  simp [equal]

theorem holFmapAsFiniteSupportParamWitness_envRel_length_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Related target environments are at least as long as their sources. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_length"
  (fmap_as_finite_support_parameters := [f])]
theorem envRel_length (opt : Bool) (f : HolFiniteMapExact Nat Nat) (source target : List Value)
    (related : envRel opt f source target) : source.length ≤ target.length := by
  cases opt with
  | false => exact envRel_length_non_opt f source target related
  | true => have length := envRel_length_opt f source target related; omega

theorem holFmapAsFiniteSupportParamWitness_envRel_extras_opt_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- An optimized environment stores its hole pointer and index after the related prefix. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_extras_opt"
  (fmap_as_finite_support_parameters := [f])]
theorem envRel_extras_opt (f : HolFiniteMapExact Nat Nat) (source target : List Value)
    (related : envRel true f source target) :
    ∃ ptr idx, holEl source.length target = .refPtr false ptr ∧
      holEl (source.length + 1) target = .number idx := by
  obtain ⟨front, extras, rfl, entries, extra⟩ := related
  obtain ⟨len, ptr, idx, ptrEq, idxEq, _⟩ := extra rfl
  have sameLength := entries.length_eq
  have atExtra (n : Nat) (bound : n < extras.length) :
      holEl (source.length + n) (front ++ extras) = holEl n extras := by
    have fullBound : source.length + n < (front ++ extras).length := by
      simp only [List.length_append]
      omega
    rw [holEl_eq_getElem _ _ fullBound, holEl_eq_getElem _ _ bound]
    simp [List.getElem_append_right, sameLength]
  refine ⟨ptr, idx, ?_, ?_⟩
  · simpa using (atExtra 0 (by omega)).trans ptrEq
  · exact (atExtra 1 (by omega)).trans idxEq

theorem holFmapAsFiniteSupportParamWitness_envRel_strip_extras_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- An optimized environment splits into a related prefix and its two
hole-management values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_strip_extras"
  (fmap_as_finite_support_parameters := [f])]
theorem envRel_strip_extras (f : HolFiniteMapExact Nat Nat) (source target : List Value)
    (related : envRel true f source target) :
    ∃ envPrefix ptr idx, envRel false f source envPrefix ∧
      target = envPrefix ++ [.refPtr false ptr, .number idx] ∧ BackendCommon.smallEnoughInt idx := by
  obtain ⟨xs, ys, rfl, pairs, extras⟩ := related
  obtain ⟨length, ptr, idx, ptrEq, idxEq, small⟩ := extras rfl
  cases ys with
  | nil => simp at length
  | cons first rest =>
    cases rest with
    | nil => simp at length
    | cons second rest =>
      cases rest with
      | cons third rest => simp at length
      | nil =>
        simp [holEl, holHd] at ptrEq idxEq
        subst first
        subst second
        exact ⟨xs, ptr, idx, ⟨xs, [], by simp, pairs, by simp⟩, rfl, small⟩

theorem holFmapAsFiniteSupportParamWitness_listToValue_rel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Encoding lists of related values yields related source list values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "list_to_v_v_rel"
  (fmap_as_finite_support_parameters := [f])]
theorem listToValue_rel (xs ys : List Value) (f : HolFiniteMapExact Nat Nat)
    (related : List.Forall₂ (valueRel f) xs ys) : valueRel f (listToValue xs) (listToValue ys) := by
  induction related with
  | nil => exact .block _ [] [] .nil
  | cons head tail ih => exact .block _ _ _ (.cons head (.cons ih .nil))

theorem holFmapAsFiniteSupportParamWitness_valueToList_rel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Decoding a related list value yields a list of related elements. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "v_to_list_v_rel"
  (fmap_as_finite_support_parameters := [f])]
theorem valueToList_rel (source : Value) (xs : List Value) (target : Value) (f : HolFiniteMapExact Nat Nat)
    (h : valueToList source = some xs ∧ valueRel f source target) :
    ∃ ys, valueToList target = some ys ∧ List.Forall₂ (valueRel f) xs ys := by
  obtain ⟨decoded, related⟩ := h
  have shape := (BvlSem.listToValue_valueToList source xs decoded).symm
  rw [shape] at related
  clear source decoded shape
  induction xs generalizing target with
  | nil =>
    change valueRel f (.block BackendCommon.nilTag []) target at related
    cases related with
    | block tag sourceArgs targetArgs pairs =>
      cases pairs
      exact ⟨[], by simp [valueToList], .nil⟩
  | cons head xs ih =>
    change valueRel f (.block BackendCommon.consTag [head, listToValue xs]) target at related
    cases related with
    | block tag sourceArgs targetArgs pairs =>
      cases pairs with
      | cons headRel tailRel =>
        cases tailRel with
        | cons lastRel emptyRel =>
          cases emptyRel
          obtain ⟨out, outRun, outRel⟩ := ih _ lastRel
          exact ⟨_, by simp [valueToList, outRun], .cons headRel outRel⟩

theorem holFmapAsFiniteSupportParamWitness_listRel_valueRel_number_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Lists of number values related pointwise are identical. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "list_rel_v_rel_number"
  (fmap_as_finite_support_parameters := [f])]
theorem listRel_valueRel_number {α : Type} (g : α → Int) (numbers : List α) (values : List Value)
    (f : HolFiniteMapExact Nat Nat)
    (related : List.Forall₂ (valueRel f) (numbers.map (fun n => .number (g n))) values) :
    values = numbers.map (fun n => .number (g n)) := by
  induction numbers generalizing values with
  | nil => cases related; rfl
  | cons number numbers ih =>
    cases related with
    | cons head tail =>
      cases head
      simp only [List.map_cons]
      congr 1
      exact ih _ tail

theorem holFmapAsFiniteSupportParamWitness_listRel_valueRel_word_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Lists of word values related pointwise are identical. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "list_rel_v_rel_word"
  (fmap_as_finite_support_parameters := [f])]
theorem listRel_valueRel_word (words : List (BitVec 64)) (values : List Value)
    (f : HolFiniteMapExact Nat Nat) (related : List.Forall₂ (valueRel f) (words.map Value.word64) values) :
    values = words.map Value.word64 := by
  induction words generalizing values with
  | nil => cases related; rfl
  | cons word words ih =>
    cases related with
    | cons head tail =>
      cases head
      simp only [List.map_cons]
      congr 1
      exact ih _ tail

theorem holFmapAsFiniteSupportParamWitness_valueToBytes_rel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Related list values decode to the same byte sequence.

Intended HOL counterpart, pending statement and finite-map carrier source review.
Former reference: @[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "v_to_bytes_v_rel" (fmap_as_finite_support_parameters := [f])] -/
theorem valueToBytes_rel (v : Value) (bytes : List (BitVec 8)) (f : HolFiniteMapExact Nat Nat) (v' : Value)
    (decoded : valueToBytes v = some bytes) (related : valueRel f v v') : valueToBytes v' = some bytes := by
  have listDecoded := (valueToBytes_eq_some v bytes).mp decoded
  obtain ⟨values, targetDecoded, valuesRelated⟩ := valueToList_rel v _ v' f ⟨listDecoded, related⟩
  have same := listRel_valueRel_number (fun b : BitVec 8 => (b.toNat : Int)) bytes values f valuesRelated
  exact (valueToBytes_eq_some v' bytes).mpr (by simpa [same] using targetDecoded)

theorem holFmapAsFiniteSupportParamWitness_valueToWords_rel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Related list values decode to the same word sequence.

Intended HOL counterpart, pending statement and finite-map carrier source review.
Former reference: @[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "v_to_words_v_rel" (fmap_as_finite_support_parameters := [f])] -/
theorem valueToWords_rel (v : Value) (words : List (BitVec 64)) (f : HolFiniteMapExact Nat Nat) (v' : Value)
    (decoded : valueToWords v = some words) (related : valueRel f v v') : valueToWords v' = some words := by
  have listDecoded := (valueToWords_eq_some v words).mp decoded
  obtain ⟨values, targetDecoded, valuesRelated⟩ := valueToList_rel v _ v' f ⟨listDecoded, related⟩
  have same := listRel_valueRel_word words values f valuesRelated
  exact (valueToWords_eq_some v' words).mpr (by simpa [same] using targetDecoded)

theorem holFmapAsFiniteSupportParamWitness_envRel_el_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Related environments have related entries at every source index.
The later HOL theorem `env_rel_el` has the same typed statement as
`env_rel_el_v_rel`; both are captured in the source probe. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_el_v_rel"
  (fmap_as_finite_support_parameters := [f])]
theorem envRel_el (opt : Bool) (f : HolFiniteMapExact Nat Nat) (source target : List Value) (index : Nat)
    (h : envRel opt f source target ∧ index < source.length) :
    valueRel f (holEl index source) (holEl index target) := by
  obtain ⟨related, bound⟩ := h
  obtain ⟨front, extras, rfl, entries, _⟩ := related
  have frontBound : index < front.length := by simpa [← entries.length_eq] using bound
  have targetBound : index < (front ++ extras).length := by simp; omega
  rw [holEl_eq_getElem index source bound, holEl_eq_getElem index (front ++ extras) targetBound]
  have entry := (List.forall₂_iff_get.mp entries).2 index bound frontBound
  simpa [List.getElem_append_left, frontBound] using entry

/-- Dropping the last entry preserves a pointwise list relation. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "list_rel_front"]
theorem listRel_front {α β : Type} (r : α → β → Prop) (xs : List α) (ys : List β)
    (related : List.Forall₂ r xs ys) : List.Forall₂ r xs.dropLast ys.dropLast := by
  induction related with
  | nil => exact .nil
  | @cons a b xs ys head tail ih =>
    cases tail with
    | nil => exact .nil
    | cons next rest =>
      simpa [List.dropLast] using List.Forall₂.cons head ih

/-- The last entries of nonempty related lists are related. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "list_rel_last"]
theorem listRel_last {α β : Type} [Nonempty α] [Nonempty β] (r : α → β → Prop)
    (xs : List α) (ys : List β) (related : List.Forall₂ r xs ys) (nonempty : xs ≠ []) :
    r (holLast xs) (holLast ys) := by
  induction related with
  | nil => contradiction
  | @cons a b xs ys head tail ih =>
    cases tail with
    | nil => simpa [holLast] using head
    | @cons c d xs ys next rest =>
      simpa [holLast] using ih (by simp)

theorem holFmapAsFiniteSupportParamWitness_listRel_envRel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Pointwise-related values form a non-optimised related environment. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "list_rel_env_rel"
  (fmap_as_finite_support_parameters := [f])]
theorem listRel_envRel (f : HolFiniteMapExact Nat Nat) (source target : List Value)
    (related : List.Forall₂ (valueRel f) source target) : envRel false f source target := by
  exact ⟨target, [], by simp, related, by simp⟩

end Flapjack.Compiler.Backend.BviTmc
