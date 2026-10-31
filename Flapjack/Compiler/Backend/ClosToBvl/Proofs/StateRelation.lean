import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ValueRelation
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Oracle
import Flapjack.Compiler.Backend.ClosToBvl.Stubs

/-! Reference cells and initialization data for the closure-to-BVL state relation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Related mutable arrays, thunks and byte arrays have the same source shape. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ref_rel_def"]
def refRel {α β : Type} (R : α → β → Prop) : ClosSem.Ref α → BvlSem.Ref β → Prop
  | .valueArray xs, .valueArray ys => List.Forall₂ R xs ys
  | .thunk m x, .thunk n y => m = n ∧ R x y
  | .byteArray xs, .byteArray frozen ys => frozen = false ∧ xs = ys
  | _, _ => False

/-- Code pointers for every possible partial application. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "global_table_def"]
def globalTable (maxApp : Nat) : BvlSem.Value :=
  .block 0 (((List.range maxApp).map fun total =>
    (List.range total).map fun previous =>
      BvlSem.Value.codePtr (partialAppFnLocation maxApp total previous)).flatten)

/-- The three source-reference cases, expressed by the shape of their BVL cells. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ref_rel_simp"]
theorem refRel_simp {α β : Type} (R : α → β → Prop)
    (vs : List α) (m : AstHOL.ThunkMode) (v : α) (bs : List (BitVec 8))
    (y : BvlSem.Ref β) :
    (refRel R (.valueArray vs) y ↔ ∃ ws, y = .valueArray ws ∧ List.Forall₂ R vs ws) ∧
    (refRel R (.thunk m v) y ↔ ∃ w, y = .thunk m w ∧ R v w) ∧
    (refRel R (.byteArray bs) y ↔ y = .byteArray false bs) := by
  cases y <;> simp [refRel, eq_comm]

/-- Optional values are related when both are absent or their contents are related. -/
def optionValueRel (R : ClosSem.Value → BvlSem.Value → Prop) :
    Option ClosSem.Value → Option BvlSem.Value → Prop
  | none, none => True
  | some x, some y => R x y
  | _, _ => False

/-- Candidate rendering of the closure-to-BVL state relation. It is not yet
tagged as the HOL declaration: the source and target state structures both
have the short name `State`, so the multi-carrier finite-map qualifier cannot
currently distinguish their `refs` fields. The closure state carrier still
requires source review against its finite-map roundtrip witness. -/
def stateRel {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (s : ClosSem.State C F) (t : BvlSem.State C F) : Prop :=
  s.ffi = t.ffi ∧
  List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code))
    s.globals (t.globals.drop numAddedGlobals) ∧
  ClosSem.getGlobal 0 t.globals = some (some (globalTable s.maxApp)) ∧
  (∀ x₁ x₂ y, f.lookup x₁ = some y → f.lookup x₂ = some y → x₁ = x₂) ∧
  (∀ x y bs, f.lookup x = some y → t.refs.lookup y ≠ some (.byteArray true bs)) ∧
  (∀ x, f.lookup x ≠ none ↔ s.refs.lookup x ≠ none) ∧
  (∀ x y, f.lookup x = some y → t.refs.lookup y ≠ none) ∧
  (∀ n x, s.refs.lookup n = some x →
    ∃ y m, f.lookup n = some m ∧ t.refs.lookup m = some y ∧
      refRel (vRel s.maxApp f t.refs t.code) x y) ∧
  (∀ n, n < s.maxApp → sptLookup (genericAppFnLocation n) t.code =
    some (n + 2, generateGenericApp s.maxApp n)) ∧
  (∀ total n, total < s.maxApp ∧ n < total →
    sptLookup (partialAppFnLocation s.maxApp total n) t.code =
      some (total - n + 1, generatePartialAppClosureFn total n)) ∧
  sptLookup (numStubs s.maxApp - 2) t.code = some (2, forceThunkCode) ∧
  compileOracleInv s.maxApp s.code s.compile s.compileOracle t.code t.compile t.compileOracle ∧
  ∀ name arity c, s.code.lookup name = some (arity, c) →
    ∃ aux1 c2 aux2, compileExpsHOL s.maxApp [c] aux1 = ([c2], aux2) ∧
      sptLookup (name + numStubs s.maxApp) t.code = some (arity, c2) ∧
      codeInstalled aux2 t.code

/-- The related globals and partial-application table can be extracted from
the candidate relation. This is local Flapjack proof infrastructure while
the state-relation carrier qualifier is awaiting review. -/
theorem stateRel_globals {C F : Type} {f : HolFiniteMapExact Nat Nat}
    {s : ClosSem.State C F} {t : BvlSem.State C F} (related : stateRel f s t) :
    ClosSem.getGlobal 0 t.globals = some (some (globalTable s.maxApp)) ∧
      List.Forall₂ (optionValueRel (vRel s.maxApp f t.refs t.code))
        s.globals (t.globals.drop numAddedGlobals) :=
  ⟨related.2.2.1, related.2.1⟩

/-- Clock updates do not change the candidate relation; the clocks are
handled separately by the evaluator simulation. This is untagged while the
underlying state relation's finite-map owners await qualification. -/
theorem stateRel_clock {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (s : ClosSem.State C F) (t : BvlSem.State C F) (clock : Nat) :
    (stateRel f s { t with clock } ↔ stateRel f s t) ∧
    (stateRel f { s with clock } t ↔ stateRel f s t) := by
  exact ⟨Iff.rfl, Iff.rfl⟩

end Flapjack.Compiler.Backend.ClosToBvl
