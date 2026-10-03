import Flapjack.Pancake.Proofs.PanStructs.CompileCorrect
import Flapjack.Pancake.Proofs.PanStructs.ConvertCode
import Flapjack.Pancake.Proofs.PanStructs.ConvertEshapes
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
namespace Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack
open Flapjack.Pancake.PanStructs.CompileShapeExact

/-- Flapjack canonical finite-map carrier roundtrip, re-exported for this module.
This is representation infrastructure, not a separate HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Full source state conversion: transform the five named fields and preserve
every other state component through the original record update. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "convert_s_def"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
def convertStateExact {width : Nat} [NeZero width] {σ : Type}
    (context : ContextExact) (state : PanSemStateFiniteExact width σ) :
    PanSemStateFiniteExact width σ :=
  { state with
    locals := state.locals.map2 (fun entry => convertV entry.2)
    globals := state.globals.map2 (fun entry => convertV entry.2)
    structs := []
    code := convertCodeExact context state.code
    eshapes := convertEshapesExact context.structs state.eshapes }
end Flapjack.Pancake.Proofs.PanStructs.ConvertState
