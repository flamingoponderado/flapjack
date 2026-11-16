module

public import Flapjack.Compiler.Inference.Infer
public import Flapjack.FiniteMap.BroadCodec
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.HOL.Transfer.Fmsp.Operations
public import Flapjack.Translator.Monadic.MonadBase

@[expose] public section

/-! Source inference state and its relation to the executable sparse tree. -/
namespace Flapjack.Compiler.Inference.Infer.HOLState
open Flapjack.Translator.Monadic.MonadBase Flapjack.HOL.Transfer.Fmsp

/-- The source state carries a finite-map substitution. -/
@[hol "cakeml/compiler/inference/inferScript.sml" "infer_st"
  (fmap_as_finite_support := [subst])]
structure InferState where
  nextUvar : Nat
  subst : HolFiniteMapExact Nat InferT
  nextId : Nat

/-- Explicit lookup-and-support view used for the canonical map codec. -/
structure InferStateBroad where
  nextUvarBroad : Nat
  substBroad : FiniteMapBroad Nat InferT
  nextIdBroad : Nat

def toBroad (s : InferState) : InferStateBroad :=
  ⟨s.nextUvar, FiniteMapBroad.toBroad s.subst, s.nextId⟩

def ofBroad (s : InferStateBroad) : InferState :=
  ⟨s.nextUvarBroad, FiniteMapBroad.ofBroad s.substBroad, s.nextIdBroad⟩

/-- Both directions of the state representation preserve every field. -/
theorem holFmapAsFiniteSupportWitness :
    (∀ s : InferState, ofBroad (toBroad s) = s) ∧
    (∀ s : InferStateBroad, toBroad (ofBroad s) = s) := by
  constructor <;> intro s <;> cases s <;> rfl

@[hol "cakeml/compiler/inference/inferScript.sml" "init_infer_state_def"
  (fmap_as_finite_support := [subst])]
def initInferState (s : InferState) : InferState :=
  { s with nextUvar := 0, subst := HolFiniteMapExact.holEmpty }

@[hol "cakeml/compiler/inference/inferScript.sml" "init_state_def"
  (fmap_as_finite_support := [subst])]
def initState {ε : Type} : M InferState Unit ε :=
  fun s => (.success (), initInferState s)

@[hol "cakeml/compiler/inference/inferScript.sml" "fresh_uvar_def"
  (fmap_as_finite_support := [subst])]
def freshUvar {ε : Type} : M InferState InferT ε :=
  fun s => (.success (.uvar s.nextUvar), { s with nextUvar := s.nextUvar + 1 })

@[hol "cakeml/compiler/inference/inferScript.sml" "n_fresh_id_def"
  (fmap_as_finite_support := [subst])]
def freshIds {ε : Type} (n : Nat) : M InferState (List Nat) ε :=
  fun s => (.success ((List.range n).map (fun i => s.nextId + i)),
    { s with nextId := s.nextId + n })

/-- Convert the executable sparse-tree state to the canonical source carrier. -/
def ofExecutable (s : Infer.State) : InferState :=
  ⟨s.nextUvar, sp2fm s.subst, s.nextId⟩

/-- Executable reset agrees with source reset under the sparse-tree codec. -/
theorem resetStateCorresponds (s : Infer.State) :
    ofExecutable (Infer.resetState s) = initInferState (ofExecutable s) := by
  simp [ofExecutable, Infer.resetState, initInferState, (sp2fmThm (α := InferT) 0 () .ln).1]

/-- Executable fresh-variable allocation returns the same value and state as
    the source monadic operation under the sparse-tree codec. -/
theorem freshUvarCorresponds (s : Infer.State) :
    (freshUvar (ε := Unit) (ofExecutable s)) =
      (.success (Infer.freshUvar s).1, ofExecutable (Infer.freshUvar s).2) := by
  rfl

/-- Executable identifier allocation agrees with the source list and state. -/
theorem freshIdsCorresponds (n : Nat) (s : Infer.State) :
    (freshIds (ε := Unit) n (ofExecutable s)) =
      (.success (Infer.freshIds n s).1, ofExecutable (Infer.freshIds n s).2) := by
  have ids : (List.range n).map (fun i => s.nextId + i) =
      List.ofFn (n := n) (fun i => s.nextId + i.val) := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp
  simp [freshIds, Infer.freshIds, ofExecutable, ids]

end Flapjack.Compiler.Inference.Infer.HOLState
