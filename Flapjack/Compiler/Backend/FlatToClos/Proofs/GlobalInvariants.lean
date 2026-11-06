import Flapjack.Compiler.Backend.FlatToClos.Helpers
import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals
import Flapjack.Compiler.Backend.FlatProps.GlobalBagProperties

/-! Global-write properties of flat-to-closure generated constructors. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Compiler.Backend.FlatProps (GlobalBag emptyGlobalBag unionGlobalBag unionGlobalBag_eq_empty)
open Flapjack.Compiler.Backend.ClosProps

private theorem unionEmptyL (bag : GlobalBag) : unionGlobalBag emptyGlobalBag bag = bag := by
  funext key
  simp [unionGlobalBag, emptyGlobalBag]

private theorem destConstant_safe (e : ClosLang.Exp) (c : ClosLang.Const)
    (decoded : destConstant e = some c) : setGlobals e = emptyGlobalBag ∧ esgcFree e := by
  cases e <;> simp [destConstant] at decoded
  case op t op args =>
    cases args with
    | cons a rest => cases op <;> simp at decoded
    | nil =>
      cases op <;> try simp at decoded
      case intOp op =>
        cases op <;> try simp at decoded
        simp [setGlobals, elistGlobals, opGlobalBag, unionEmptyL, esgcFree, esgcFreeList]
      case blockOp op =>
        cases op <;> try simp at decoded <;>
          simp [setGlobals, elistGlobals, opGlobalBag, unionEmptyL, esgcFree, esgcFreeList]

private theorem destConstants_safe (xs : List ClosLang.Exp) (cs : List ClosLang.Const)
    (decoded : destConstants xs = some cs) : elistGlobals xs = emptyGlobalBag ∧ esgcFreeList xs := by
  induction xs generalizing cs with
  | nil => simp [elistGlobals, esgcFreeList]
  | cons x xs ih =>
    cases first : destConstant x with
    | none => simp [destConstants, first] at decoded
    | some c =>
      cases rest : destConstants xs with
      | none => simp [destConstants, first, rest] at decoded
      | some cs' =>
        have a := destConstant_safe x c first
        have b := ih cs' rest
        exact ⟨by simp [elistGlobals, a.1, b.1, unionEmptyL], by simpa [esgcFreeList] using And.intro a.2 b.2⟩

/-- A closure expression list has no global writes exactly when every member does not. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "elist_globals_empty"]
theorem elistGlobals_empty (xs : List ClosLang.Exp) :
    elistGlobals xs = emptyGlobalBag ↔ ∀ e ∈ xs, setGlobals e = emptyGlobalBag := by
  induction xs with
  | nil => simp [elistGlobals]
  | cons x xs ih => simp [elistGlobals, unionGlobalBag_eq_empty, ih]

/-- Literal lowering produces no global writes or nested write closures. -/
theorem compileLit_globalSafe (t : Tra) (lit : Flapjack.AstHOL.Lit) :
    setGlobals (compileLit t lit) = emptyGlobalBag ∧ esgcFree (compileLit t lit) := by
  cases lit <;> simp [compileLit, setGlobals, elistGlobals, opGlobalBag, unionEmptyL, esgcFree, esgcFreeList]

/-- Constructor folding preserves the complete global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "set_globals_SmartCons"]
theorem setGlobals_smartCons (t : Tra) (tag : Nat) (xs : List ClosLang.Exp) :
    setGlobals (smartCons t tag xs) = elistGlobals xs := by
  cases xs with
  | nil => simp [smartCons, setGlobals, elistGlobals, opGlobalBag, unionEmptyL]
  | cons x xs =>
    cases decoded : destConstants (x :: xs) with
    | none => simp [smartCons, decoded, setGlobals, opGlobalBag, unionEmptyL]
    | some cs =>
      have h := (destConstants_safe (x :: xs) cs decoded).1
      simp [smartCons, decoded, setGlobals, elistGlobals, opGlobalBag, unionEmptyL, h]

/-- Constructor folding preserves closure safety of all operands. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "esgc_free_SmartCons"]
theorem esgcFree_smartCons (t : Tra) (tag : Nat) (xs : List ClosLang.Exp) :
    esgcFree (smartCons t tag xs) ↔ esgcFreeList xs := by
  cases xs with
  | nil => simp [smartCons, esgcFree, esgcFreeList]
  | cons x xs =>
    cases decoded : destConstants (x :: xs) with
    | none => simp [smartCons, decoded, esgcFree]
    | some cs =>
      have h := (destConstants_safe (x :: xs) cs decoded).2
      simp [smartCons, decoded, esgcFree, esgcFreeList, h]

end Flapjack.Compiler.Backend.FlatToClos
