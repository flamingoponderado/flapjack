import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ClosureRelation
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ClosureArguments
import Flapjack.Compiler.Backend.BackendCommon.ClosTags
import Mathlib.Data.List.Forall2

/-! Value and environment relations for closure-to-BVL simulation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.Compiler.Backend.BackendCommon

private def toBroad {α : Type} (m : HolFiniteMapExact Nat α) := m.lookup
private def ofBroad {α : Type} (lookup : Nat → Option α)
    (support : ∃ keys : List Nat, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact Nat α := ⟨lookup, support⟩

/-- Codec roundtrips for the finite maps in the value relation. -/
theorem holFmapAsFiniteSupportParamWitness_vRel_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (ofBroad (toBroad f) f.finiteSupport).lookup key = f.lookup key ∧
    (ofBroad (toBroad f) f.finiteSupport).finiteSupport = f.finiteSupport ∧
    ofBroad (toBroad f) f.finiteSupport = f := by
  cases f
  exact ⟨rfl, rfl, rfl⟩

theorem holFmapAsFiniteSupportParamWitness_vRel_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs := by
  cases refs
  exact ⟨rfl, rfl, rfl⟩

/-- Closure values and their BVL representations, including partial applications. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "v_rel"
  (fmap_as_finite_support_parameters := [f, refs])]
inductive vRel (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (code : Spt (Nat × Bvl.Exp)) : ClosSem.Value → BvlSem.Value → Prop where
  | number (n : Int) : vRel maxApp f refs code (.number n) (.number n)
  | word64 (w : BitVec 64) : vRel maxApp f refs code (.word64 w) (.word64 w)
  | block {tag xs ys} : List.Forall₂ (vRel maxApp f refs code) xs ys →
      vRel maxApp f refs code (.block tag xs) (.block (closTagShift tag) ys)
  | byteVector {bs p} : refs.lookup p = some (.byteArray true bs) →
      (¬ ∃ r, f.lookup r = some p) →
      vRel maxApp f refs code (.byteVector bs) (.refPtr true p)
  | refPtr {b r1 r2} : f.lookup r1 = some r2 →
      vRel maxApp f refs code (.refPtr b r1) (.refPtr b r2)
  | closure {env fvs cl p n ys} : List.Forall₂ (vRel maxApp f refs code) env fvs →
      clRel maxApp (fun p => ∃ r, f.lookup r = some p) refs code (env, fvs) cl
        (.block 30 (.codePtr p :: .number n :: ys)) →
      vRel maxApp f refs code cl (.block 30 (.codePtr p :: .number n :: ys))
  | partialClosure {env fvs argEnv ys numArgs cl clApp cl'} :
      List.Forall₂ (vRel maxApp f refs code) env fvs →
      List.Forall₂ (vRel maxApp f refs code) argEnv ys →
      argEnv ≠ [] → argEnv.length < numArgs →
      sptLookup (partialAppFnLocation maxApp (numArgs - 1) (ys.length - 1)) code =
        some (numArgs - argEnv.length + 1,
          generatePartialAppClosureFn (numArgs - 1) (ys.length - 1)) →
      addArgs cl argEnv = some clApp → getNumArgs cl = some numArgs →
      clRel maxApp (fun p => ∃ r, f.lookup r = some p) refs code (env, fvs) cl cl' →
      vRel maxApp f refs code clApp
        (.block 31 (.codePtr (partialAppFnLocation maxApp (numArgs - 1) (ys.length - 1)) ::
          .number (Int.ofNat (numArgs - 1 - argEnv.length)) :: cl' :: ys))

theorem holFmapAsFiniteSupportParamWitness_vRel_subspt_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (ofBroad (toBroad f) f.finiteSupport).lookup key = f.lookup key ∧
    (ofBroad (toBroad f) f.finiteSupport).finiteSupport = f.finiteSupport ∧
    ofBroad (toBroad f) f.finiteSupport = f :=
  holFmapAsFiniteSupportParamWitness_vRel_f f key

theorem holFmapAsFiniteSupportParamWitness_vRel_subspt_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_vRel_refs refs key

/-- Extending the code tree preserves related values. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "v_rel_subspt"
  (fmap_as_finite_support_parameters := [f, refs])]
theorem vRel_subspt {maxApp : Nat} (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    {code1 code2 : Spt (Nat × Bvl.Exp)} {x y}
    (related : vRel maxApp f refs code1 x y) (sub : sptSubspt code1 code2) :
    vRel maxApp f refs code2 x y := by
  refine vRel.rec
    (motive_1 := fun x y _ => ∀ code2, sptSubspt code1 code2 → vRel maxApp f refs code2 x y)
    (motive_2 := fun xs ys _ => ∀ code2, sptSubspt code1 code2 →
      List.Forall₂ (vRel maxApp f refs code2) xs ys)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ related code2 sub
  · intro n code2 sub
    exact .number n
  · intro w code2 sub
    exact .word64 w
  · intro tag xs ys related ih code2 sub
    exact .block (ih code2 sub)
  · intro bs p lookup fresh code2 sub
    exact .byteVector lookup fresh
  · intro b r1 r2 lookup code2 sub
    exact .refPtr lookup
  · intro env fvs cl p n ys related closure ih code2 sub
    exact .closure (ih code2 sub) (clRel_subspt refs closure sub)
  · intro env fvs argEnv ys numArgs cl clApp cl' envRel argRel nonempty bound lookup added arity closure
      envIh argIh code2 sub
    have mem := (sptMem_iff_lookup _ _).2 ⟨_, lookup⟩
    exact .partialClosure (envIh code2 sub) (argIh code2 sub) nonempty bound
      ((sub _ mem).2.trans lookup) added arity (clRel_subspt refs closure sub)
  · intro code2 sub
    exact .nil
  · intro a b xs ys head tail headIh tailIh code2 sub
    exact .cons (headIh code2 sub) (tailIh code2 sub)

theorem holFmapAsFiniteSupportParamWitness_envRel_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (ofBroad (toBroad f) f.finiteSupport).lookup key = f.lookup key ∧
    (ofBroad (toBroad f) f.finiteSupport).finiteSupport = f.finiteSupport ∧
    ofBroad (toBroad f) f.finiteSupport = f :=
  holFmapAsFiniteSupportParamWitness_vRel_f f key

theorem holFmapAsFiniteSupportParamWitness_envRel_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_vRel_refs refs key

/-- The source environment may be related to a prefix of a longer BVL environment. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "env_rel_def"
  (fmap_as_finite_support_parameters := [f, refs])]
def envRel (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp)) :
    List ClosSem.Value → List BvlSem.Value → Prop
  | [], _ => True
  | _ :: _, [] => False
  | x :: xs, y :: ys => vRel maxApp f refs code x y ∧ envRel maxApp f refs code xs ys

/-- Source-shaped environment-length consequence. The finite-map parameter
qualifiers and inferred HOL type remain to be reviewed before tagging it. -/
theorem envRel_length {maxApp : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {xs ys} (related : envRel maxApp f refs code xs ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
      cases ys with
      | nil => exact False.elim related
      | cons y ys =>
          have tail : envRel maxApp f refs code xs ys := related.2
          simpa using Nat.succ_le_succ (ih tail)

theorem holFmapAsFiniteSupportParamWitness_envRel_subspt_f
    (f : HolFiniteMapExact Nat Nat) (key : Nat) :
    (ofBroad (toBroad f) f.finiteSupport).lookup key = f.lookup key ∧
    (ofBroad (toBroad f) f.finiteSupport).finiteSupport = f.finiteSupport ∧
    ofBroad (toBroad f) f.finiteSupport = f :=
  holFmapAsFiniteSupportParamWitness_vRel_f f key

theorem holFmapAsFiniteSupportParamWitness_envRel_subspt_refs
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (ofBroad (toBroad refs) refs.finiteSupport).lookup key = refs.lookup key ∧
    (ofBroad (toBroad refs) refs.finiteSupport).finiteSupport = refs.finiteSupport ∧
    ofBroad (toBroad refs) refs.finiteSupport = refs :=
  holFmapAsFiniteSupportParamWitness_vRel_refs refs key

/-- Extending the code tree preserves related environments. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "env_rel_subspt"
  (fmap_as_finite_support_parameters := [f, refs])]
theorem envRel_subspt {maxApp : Nat} (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    {code1 code2 : Spt (Nat × Bvl.Exp)} {xs ys}
    (related : envRel maxApp f refs code1 xs ys) (sub : sptSubspt code1 code2) :
    envRel maxApp f refs code2 xs ys := by
  induction xs generalizing ys with
  | nil => trivial
  | cons x xs ih =>
      cases ys with
      | nil => exact False.elim related
      | cons y ys => exact ⟨vRel_subspt f refs related.1 sub, ih related.2⟩

end Flapjack.Compiler.Backend.ClosToBvl
