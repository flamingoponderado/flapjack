import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation
import Flapjack.Compiler.Backend.BackendCommon.SmallInt
import Flapjack.Misc.ListEl
import Flapjack.Compiler.Backend.Semantics.BvlSem.Conversions

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

/-- Lookup characterization of finite-map extension. -/
def finiteSubmap (f g : HolFiniteMapExact Nat Nat) : Prop :=
  ∀ key value, f.lookup key = some value → g.lookup key = some value

theorem holFmapAsFiniteSupportParamWitness_valueRel_submap_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_valueRel_submap_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl

/-- Extending the pointer map preserves related values. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "v_rel_submap"
  (fmap_as_finite_support_parameters := [f, g])]
theorem valueRel_submap (f : HolFiniteMapExact Nat Nat) (g : HolFiniteMapExact Nat Nat) (v1 v2 : Value)
    (related : valueRel f v1 v2) (submap : finiteSubmap f g) : valueRel g v1 v2 := by
  cases related with
  | number i => exact .number i
  | word64 w => exact .word64 w
  | codePtr n => exact .codePtr n
  | refPtr n m b lookup => exact .refPtr n m b (submap n m lookup)
  | block tag xs ys pairs =>
    apply valueRel.block
    have each : ∀ x ∈ xs, ∀ y, valueRel f x y → valueRel g x y := by
      intro x member y rel
      exact valueRel_submap f g x y rel submap
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
    (source target : List Value) (related : List.Forall₂ (valueRel f) source target)
    (submap : finiteSubmap f g) : List.Forall₂ (valueRel g) source target := by
  induction related with
  | nil => exact .nil
  | cons head tail ih => exact .cons (valueRel_submap f g _ _ head submap) ih

theorem holFmapAsFiniteSupportParamWitness_envRel_submap_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl
theorem holFmapAsFiniteSupportParamWitness_envRel_submap_g (g : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup g) g.finiteSupport = g := by cases g; rfl

/-- Extending the pointer map preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_submap"
  (fmap_as_finite_support_parameters := [f, g])]
theorem envRel_submap (opt : Bool) (f : HolFiniteMapExact Nat Nat) (g : HolFiniteMapExact Nat Nat)
    (source target : List Value) (related : envRel opt f source target) (submap : finiteSubmap f g) :
    envRel opt g source target := by
  obtain ⟨xs, ys, equal, pairs, extras⟩ := related
  exact ⟨xs, ys, equal, listRel_submap f g source xs pairs submap, extras⟩

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
    (a b : Value) (related : envRel opt f source target) (values : valueRel f a b) :
    envRel opt f (a :: source) (b :: target) := by
  obtain ⟨xs, ys, rfl, pairs, extras⟩ := related
  exact ⟨b :: xs, ys, rfl, .cons values pairs, extras⟩

theorem holFmapAsFiniteSupportParamWitness_envRel_append_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Prefixing lists of related values preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "env_rel_append"
  (fmap_as_finite_support_parameters := [f])]
theorem envRel_append (opt : Bool) (f : HolFiniteMapExact Nat Nat) (source target a b : List Value)
    (related : envRel opt f source target) (values : List.Forall₂ (valueRel f) a b) :
    envRel opt f (a ++ source) (b ++ target) := by
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
theorem listToValue_rel (f : HolFiniteMapExact Nat Nat) (xs ys : List Value)
    (related : List.Forall₂ (valueRel f) xs ys) : valueRel f (listToValue xs) (listToValue ys) := by
  induction related with
  | nil => exact .block _ [] [] .nil
  | cons head tail ih => exact .block _ _ _ (.cons head (.cons ih .nil))

private theorem decoded_eq_listToValue (xs : List Value) (source : Value)
    (decoded : valueToList source = some xs) : source = listToValue xs := by
  induction xs generalizing source with
  | nil =>
    cases source with
    | block tag args =>
      cases args with
      | nil =>
        by_cases h : tag = BackendCommon.nilTag
        · subst tag; rfl
        · simp [valueToList, h] at decoded
      | cons head tail =>
        cases tail with
        | nil => simp [valueToList] at decoded
        | cons last rest =>
          cases rest with
          | nil =>
            simp only [valueToList] at decoded
            split at decoded
            · cases h : valueToList last <;> simp [h] at decoded
            · simp at decoded
          | cons third rest => simp [valueToList] at decoded
    | _ => simp [valueToList] at decoded

  | cons head xs ih =>
    cases source with
    | block tag args =>
      cases args with
      | nil =>
        simp only [valueToList] at decoded
        split at decoded <;> simp at decoded
      | cons a tail =>
        cases tail with
        | nil => simp [valueToList] at decoded
        | cons last rest =>
          cases rest with
          | cons third rest => simp [valueToList] at decoded
          | nil =>
            by_cases h : tag = BackendCommon.consTag
            · simp only [valueToList, h, ↓reduceIte] at decoded
              cases tailRun : valueToList last with
              | none => simp [tailRun] at decoded
              | some tailValues =>
                simp [tailRun] at decoded
                obtain ⟨rfl, rfl⟩ := decoded
                have tailEq := ih last tailRun
                subst tag
                simp [listToValue, tailEq]
            · simp [valueToList, h] at decoded
    | _ => simp [valueToList] at decoded


theorem holFmapAsFiniteSupportParamWitness_valueToList_rel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Decoding a related list value yields a list of related elements. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "v_to_list_v_rel"
  (fmap_as_finite_support_parameters := [f])]
theorem valueToList_rel (f : HolFiniteMapExact Nat Nat) (source : Value) (xs : List Value) (target : Value)
    (decoded : valueToList source = some xs) (related : valueRel f source target) :
    ∃ ys, valueToList target = some ys ∧ List.Forall₂ (valueRel f) xs ys := by
  have shape := decoded_eq_listToValue xs source decoded
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

private theorem related_bytes_identity (f : HolFiniteMapExact Nat Nat) (bytes : List (BitVec 8))
    (values : List Value) (related : List.Forall₂ (valueRel f) (bytes.map (fun b => .number b.toNat)) values) :
    values = bytes.map (fun b => .number b.toNat) := by
  induction bytes generalizing values with
  | nil => cases related; rfl
  | cons byte bytes ih =>
    cases related with
    | cons head tail =>
      cases head
      simp only [List.map_cons]
      congr 1
      exact ih _ tail

private theorem related_words_identity (f : HolFiniteMapExact Nat Nat) (words : List (BitVec 64))
    (values : List Value) (related : List.Forall₂ (valueRel f) (words.map Value.word64) values) :
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

/-- Related list values decode to the same byte sequence. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "v_to_bytes_v_rel"
  (fmap_as_finite_support_parameters := [f])]
theorem valueToBytes_rel (v : Value) (bytes : List (BitVec 8)) (f : HolFiniteMapExact Nat Nat) (v' : Value)
    (decoded : valueToBytes v = some bytes) (related : valueRel f v v') : valueToBytes v' = some bytes := by
  have listDecoded := (valueToBytes_eq_some v bytes).mp decoded
  obtain ⟨values, targetDecoded, valuesRelated⟩ := valueToList_rel f v _ v' listDecoded related
  have same := related_bytes_identity f bytes values valuesRelated
  exact (valueToBytes_eq_some v' bytes).mpr (by simpa [same] using targetDecoded)

theorem holFmapAsFiniteSupportParamWitness_valueToWords_rel_f (f : HolFiniteMapExact Nat Nat) :
    mapofBroad (maptoBroadlookup f) f.finiteSupport = f := by cases f; rfl

/-- Related list values decode to the same word sequence. -/
@[hol "cakeml/compiler/backend/proofs/bvi_tmcProofScript.sml" "v_to_words_v_rel"
  (fmap_as_finite_support_parameters := [f])]
theorem valueToWords_rel (v : Value) (words : List (BitVec 64)) (f : HolFiniteMapExact Nat Nat) (v' : Value)
    (decoded : valueToWords v = some words) (related : valueRel f v v') : valueToWords v' = some words := by
  have listDecoded := (valueToWords_eq_some v words).mp decoded
  obtain ⟨values, targetDecoded, valuesRelated⟩ := valueToList_rel f v _ v' listDecoded related
  have same := related_words_identity f words values valuesRelated
  exact (valueToWords_eq_some v' words).mpr (by simpa [same] using targetDecoded)

end Flapjack.Compiler.Backend.BviTmc
