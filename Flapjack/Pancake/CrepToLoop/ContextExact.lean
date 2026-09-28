import Flapjack.Pancake.CrepToLoop
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Basis.Pure.MlString
import Flapjack.Compiler.Encoders.Asm

/-!
Exact finite-map carrier and context helpers for `crep_to_loopScript.sml`.
Production `LoopContext` remains list/String-backed; these declarations model
the HOL `context` datatype over its actual finite-map and mlstring carriers.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm

/-- Function-backed view with explicit finite-support evidence for the
    canonical finite-map carrier witness. -/
structure CrepToLoopContextBroad where
  varsLookup : Nat → Option Nat
  varsFiniteSupport : ∃ keys : List Nat, ∀ key, varsLookup key ≠ none → key ∈ keys
  funcsLookup : MlString → Option (Nat × Nat)
  funcsFiniteSupport : ∃ keys : List MlString,
    ∀ key, funcsLookup key ≠ none → key ∈ keys
  vmax : Nat
  target : AsmArchitecture

/-- Exact HOL `crep_to_loop$context` (`crep_to_loopScript.sml:11-18`). Both
    `|->` fields use the canonical finite-support carrier; function names use
    HOL `mlstring`; and `target` uses the exact `asm$architecture` datatype. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "context"
  (fmap_as_finite_support := [vars, funcs])]
structure CrepToLoopContextExact where
  vars : HolFiniteMapExact Nat Nat
  funcs : HolFiniteMapExact MlString (Nat × Nat)
  vmax : Nat
  target : AsmArchitecture

namespace CrepToLoopContextExact

/-- Forget the finite-map wrapper while retaining the support witnesses. -/
def toBroad (context : CrepToLoopContextExact) : CrepToLoopContextBroad where
  varsLookup := context.vars.lookup
  varsFiniteSupport := context.vars.finiteSupport
  funcsLookup := context.funcs.lookup
  funcsFiniteSupport := context.funcs.finiteSupport
  vmax := context.vmax
  target := context.target

/-- Reconstruct the canonical finite-support maps from their lookup/support
    pairs. -/
def ofBroad (context : CrepToLoopContextBroad) : CrepToLoopContextExact where
  vars := ⟨context.varsLookup, context.varsFiniteSupport⟩
  funcs := ⟨context.funcsLookup, context.funcsFiniteSupport⟩
  vmax := context.vmax
  target := context.target

/-- Canonical finite-support witness required by the `context` qualifier. -/
theorem holFmapAsFiniteSupportWitness (context : CrepToLoopContextExact) :
    ofBroad (toBroad context) = context := by
  cases context
  rfl

end CrepToLoopContextExact

private def CrepToLoopFiniteMap.toBroadlookup (map : HolFiniteMapExact α β) :
    α → Option β := map.lookup

private def CrepToLoopFiniteMap.ofBroad (lookup : α → Option β)
    (support : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact α β := ⟨lookup, support⟩

/-- Checked finite-map parameter translation for `mk_ctxt_def.vmap`. -/
theorem holFmapAsFiniteSupportParamWitness_mkCtxtExact_vmap
    (vmap : HolFiniteMapExact Nat Nat) :
    CrepToLoopFiniteMap.ofBroad (CrepToLoopFiniteMap.toBroadlookup vmap)
      vmap.finiteSupport = vmap := by
  cases vmap
  rfl

/-- Checked finite-map parameter translation for `mk_ctxt_def.fs`. -/
theorem holFmapAsFiniteSupportParamWitness_mkCtxtExact_fs
    (fs : HolFiniteMapExact MlString (Nat × Nat)) :
    CrepToLoopFiniteMap.ofBroad (CrepToLoopFiniteMap.toBroadlookup fs)
      fs.finiteSupport = fs := by
  cases fs
  rfl

/-- Exact HOL `mk_ctxt_def` (`crep_to_loopScript.sml:221-228`), preserving
    source argument and field order. -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "mk_ctxt_def"
  (fmap_as_finite_support_parameters := [vmap, fs])]
def mkCtxtExact (target : AsmArchitecture)
    (vmap : HolFiniteMapExact Nat Nat)
    (fs : HolFiniteMapExact MlString (Nat × Nat)) (vmax : Nat) :
    CrepToLoopContextExact :=
  { vars := vmap, funcs := fs, vmax := vmax, target := target }

/-- Exact HOL `find_lab_def` (`crep_to_loopScript.sml:27-32`). -/
@[hol "cakeml/pancake/crep_to_loopScript.sml" "find_lab_def"
  (fmap_as_finite_support := [funcs])]
def findLabExact (context : CrepToLoopContextExact) (function : MlString) : Nat :=
  match context.funcs.lookup function with
  | some (label, _) => label
  | none => 0

end Flapjack
