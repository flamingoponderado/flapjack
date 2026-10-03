import Flapjack.Pancake.Proofs.PanStructs.CompileExpAtomic
namespace Flapjack.Pancake.Proofs.PanStructs.CompileExpVar
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Pancake.Proofs.PanStructs.ConvertState
open Flapjack.Pancake.Proofs.PanStructs.ShapeMap
open Flapjack.Pancake.Proofs.PanStructs.StructInfosOkExact

/-- Flapjack external-library lookup infrastructure. Lawful equality yields the
first matching entry; these helper typeclasses do not enter the HOL case. -/
theorem alistToFmap_findSome {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    (entries : List (α × β)) (key : α) :
    alistToFmap entries key =
      entries.findSome? (fun entry => if entry.1 = key then some entry.2 else none) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    change (if entry.1 == key then some entry.2 else alistToFmap entries key) =
      (match (if entry.1 = key then some entry.2 else none) with
       | some value => some value
       | none => entries.findSome? (fun p => if p.1 = key then some p.2 else none))
    by_cases heq : entry.1 = key
    · simp [heq]
    · have hbeq : (entry.1 == key) = false := by simp [heq]
      simp only [hbeq, Bool.false_eq_true, ↓reduceIte, heq, ih]

/-- Flapjack codec bridge to the exact expression compiler’s first-match lookup.
No distinctness or successful-lookup premise is required. -/
theorem shapeMap_lookup_findSome (entries : List (MlS × ShapeHOL)) (key : MlS) :
    (shapeMap entries).lookup key =
      entries.findSome? (fun entry => if entry.1 = key then some entry.2 else none) := by
  rw [shapeMap_lookup]
  apply alistToFmap_findSome

/-- Canonical imported state-carrier roundtrip for this representation qualifier.
Flapjack infrastructure, not an independent HOL declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
      (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
      PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Genuine Var constructor case of the full HOL expression theorem. Both kinds
retain all seven source hypotheses and derive all three original conclusions. -/
@[hol "cakeml/pancake/proofs/pan_structsProofScript.sml" "compile_exp_correct"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileExpCorrectVar {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ) (context : ContextExact)
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (h : @PanSemStateFiniteExact.evalHOLFinite width σ _ source
        (fun a => Classical.propDecidable (source.memaddrs a)) (.var kind name : ExpHOL width) = some value ∧
      shapeMap context.locals = source.locals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      shapeMap context.globals = source.globals.map2 (fun entry => shapeOfHOLExact entry.2) ∧
      context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)) ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.locals ∧
      feveryHOL (fun entry => valueFldsOkHOLExact source.structs entry.2) source.globals ∧
      structInfosOkHOLExact source.structs) :
    oldExpShapeExact context (.var kind name : ExpHOL width) = shapeOfHOLExact value ∧
    valueFldsOkHOLExact source.structs value = true ∧
    @PanSemStateFiniteExact.evalHOLFinite width σ _ (convertStateExact context source)
      (fun a => Classical.propDecidable ((convertStateExact context source).memaddrs a))
      (compileExpExact context (.var kind name : ExpHOL width)) = some (convertV value) := by
  rcases h with ⟨heval, hlocals, hglobals, hstructs, hfieldsLocal, hfieldsGlobal, hinfo⟩
  cases kind with
  | «local» =>
    have hlookup : source.locals.lookup name = some value := by
      simpa only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact,
        PanSemStateFiniteExact.toExact] using heval
    have hshape : (shapeMap context.locals).lookup name = some (shapeOfHOLExact value) := by
      rw [hlocals]
      simp only [HolFiniteMapExact.lookup_map2, hlookup, Option.map_some]
    refine ⟨?_, hfieldsLocal name value hlookup, ?_⟩
    · rw [shapeMap_lookup_findSome] at hshape
      simpa only [oldExpShapeExact, Option.getD_some] using
        congrArg (fun result : Option ShapeHOL => result.getD .one) hshape
    · simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, compileExpExact,
        convertStateExact, PanSemStateFiniteExact.toExact, HolFiniteMapExact.map2, hlookup]
  | «global» =>
    have hlookup : source.globals.lookup name = some value := by
      simpa only [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact,
        PanSemStateFiniteExact.toExact] using heval
    have hshape : (shapeMap context.globals).lookup name = some (shapeOfHOLExact value) := by
      rw [hglobals]
      simp only [HolFiniteMapExact.lookup_map2, hlookup, Option.map_some]
    refine ⟨?_, hfieldsGlobal name value hlookup, ?_⟩
    · rw [shapeMap_lookup_findSome] at hshape
      simpa only [oldExpShapeExact, Option.getD_some] using
        congrArg (fun result : Option ShapeHOL => result.getD .one) hshape
    · simp [PanSemStateFiniteExact.evalHOLFinite, evalHOLExact, compileExpExact,
        convertStateExact, PanSemStateFiniteExact.toExact, HolFiniteMapExact.map2, hlookup]
end Flapjack.Pancake.Proofs.PanStructs.CompileExpVar
