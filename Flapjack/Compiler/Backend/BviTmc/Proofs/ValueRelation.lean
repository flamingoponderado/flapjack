import Flapjack.Compiler.Backend.BviTmc.Proofs.CodeRelation
import Flapjack.Compiler.Backend.BackendCommon.SmallInt
import Flapjack.Misc.ListEl

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

end Flapjack.Compiler.Backend.BviTmc
