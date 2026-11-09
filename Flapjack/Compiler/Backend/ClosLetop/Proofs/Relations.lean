module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.Production
public import Flapjack.Compiler.Backend.ClosMti.Proofs.StateRelation

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Relations used by closure let-operation cleanup correctness. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosSem BackendProps

/-- Target code is the let-operation cleanup of source code. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "code_rel_def"]
def CodeRel (source target : List ClosLang.Exp) : Prop := target = compileList source

/-- Related recursive function bodies preserve their arity and transform their code. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "f_rel_def"]
def FunctionRel {α : Type} (source target : α × ClosLang.Exp) : Prop :=
  source.1 = target.1 ∧ CodeRel [source.2] [target.2]

/-- Values preserve their payloads and transform embedded closure bodies. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "v_rel"]
inductive ValueRel : Value → Value → Prop where
  | number (value : Int) : ValueRel (.number value) (.number value)
  | word64 (value : BitVec 64) : ValueRel (.word64 value) (.word64 value)
  | byteVector (bytes : List (BitVec 8)) : ValueRel (.byteVector bytes) (.byteVector bytes)
  | refPtr (flag : Bool) (address : Nat) : ValueRel (.refPtr flag address) (.refPtr flag address)
  | block (tag : Nat) (source target : List Value) :
      List.Forall₂ ValueRel source target → ValueRel (.block tag source) (.block tag target)
  | closure (location : Option Nat) (args nextArgs env nextEnv : List Value)
      (arity : Nat) (body nextBody : ClosLang.Exp) :
      List.Forall₂ ValueRel env nextEnv → List.Forall₂ ValueRel args nextArgs →
      CodeRel [body] [nextBody] →
      ValueRel (.closure location args env arity body) (.closure location nextArgs nextEnv arity nextBody)
  | recclosure (location : Option Nat) (args nextArgs env nextEnv : List Value)
      (functions nextFunctions : List (Nat × ClosLang.Exp)) (index : Nat) :
      List.Forall₂ ValueRel env nextEnv → List.Forall₂ ValueRel args nextArgs →
      List.Forall₂ FunctionRel functions nextFunctions →
      ValueRel (.recclosure location args env functions index)
        (.recclosure location nextArgs nextEnv nextFunctions index)

/-- Reference payloads retain their kind and related contents. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "ref_rel"]
inductive RefRel : Ref Value → Ref Value → Prop where
  | byteArray (bytes : List (BitVec 8)) : RefRel (.byteArray bytes) (.byteArray bytes)
  | valueArray (source target : List Value) :
      List.Forall₂ ValueRel source target → RefRel (.valueArray source) (.valueArray target)
  | thunk (mode : Flapjack.AstHOL.ThunkMode) (source target : Value) :
      ValueRel source target → RefRel (.thunk mode source) (.thunk mode target)

private def maptoBroadlookup {K V : Type} (map : HolFiniteMapExact K V) : K → Option V := map.lookup
private def mapofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- The first finite-map parameter has a canonical lookup roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_fmapRel_first {K A : Type} (first : HolFiniteMapExact K A) :
    mapofBroad (maptoBroadlookup first) first.finiteSupport = first := by cases first; rfl

/-- The second finite-map parameter has a canonical lookup roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_fmapRel_second {K B : Type} (second : HolFiniteMapExact K B) :
    mapofBroad (maptoBroadlookup second) second.finiteSupport = second := by cases second; rfl

/-- Maps have equal domains and related entries at each source key. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "FMAP_REL_def"
  (fmap_as_finite_support_parameters := [first, second])]
def fmapRel {K A B : Type} (r : A → B → Prop) (first : HolFiniteMapExact K A)
    (second : HolFiniteMapExact K B) : Prop :=
  (∀ k, first.lookup k ≠ none ↔ second.lookup k ≠ none) ∧
    ∀ k v, first.lookup k = some v → ∃ w, second.lookup k = some w ∧ r v w

/-- The closure state's canonical finite-map representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- Relate closure states across let-operation cleanup. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "state_rel_def"
  (fmap_as_finite_support := [refs, code])]
def StateRel {C F : Type} (source target : State C F) : Prop :=
  (∀ n, (source.compileOracle n).2.2 = []) ∧
  source.code = HolFiniteMapExact.empty ∧ target.code = HolFiniteMapExact.empty ∧
  target.maxApp = source.maxApp ∧ 1 ≤ source.maxApp ∧ target.clock = source.clock ∧
  target.ffi = source.ffi ∧ List.Forall₂ (Flapjack.optionRel ValueRel) source.globals target.globals ∧
  fmapRel RefRel source.refs target.refs ∧
  source.compile = pureCc compileInc target.compile ∧
  target.compileOracle = pureCo compileInc ∘ source.compileOracle

/-- Related code lists have the same length. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "code_rel_IMP_LENGTH"]
theorem codeRel_length (source target : List ClosLang.Exp) (related : CodeRel source target) :
    source.length = target.length := by
  change target = compileList source at related
  subst target
  simp [compileList_eq_map]

/-- Related lists with at least two elements have related head and tail. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "code_rel_CONS_CONS"]
theorem codeRel_cons (x1 x2 : ClosLang.Exp) (xs : List ClosLang.Exp)
    (y1 y2 : ClosLang.Exp) (ys : List ClosLang.Exp)
    (related : CodeRel (x1 :: x2 :: xs) (y1 :: y2 :: ys)) :
    CodeRel [x1] [y1] ∧ CodeRel (x2 :: xs) (y2 :: ys) := by
  simp [CodeRel, compileList] at related ⊢
  exact related

end Flapjack.Compiler.Backend.ClosLetop
