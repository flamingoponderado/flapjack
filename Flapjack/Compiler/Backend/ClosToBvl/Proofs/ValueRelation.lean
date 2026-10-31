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

end Flapjack.Compiler.Backend.ClosToBvl
