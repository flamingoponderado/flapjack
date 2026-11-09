module

public import Flapjack.Compiler.Backend.ClosKnown.KnownOp
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Globals

@[expose] public section

/-! Global approximation changes made by known-function primitives. -/
namespace Flapjack.Compiler.Backend.ClosKnown
open ClosProps

/-- Outside the source operation's write bag, primitive approximation
leaves every tree lookup unchanged. This is proof infrastructure. -/
theorem knownOpLookupUnchanged (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (a : ValApprox) (g : Spt ValApprox) (key : Nat)
    (known : knownOpHOL op args g0 = (a, g)) (outside : opGlobalBag op key = 0) :
    sptLookup key g = sptLookup key g0 := by
  cases op with
  | globOp op =>
    cases op with
    | global index =>
      cases args <;> simp_all [knownOpHOL]
      all_goals split at known <;> simp_all
    | setGlobal index =>
      cases args with
      | nil => simp_all [knownOpHOL]
      | cons x xs =>
        simp only [knownOpHOL, Prod.mk.injEq] at known
        rcases known with ⟨_, rfl⟩
        have different : key ≠ index := by simpa [opGlobalBag] using outside
        exact sptLookup_sptInsert_ne index key _ g0 different
    | _ => simp_all [knownOpHOL]
  | blockOp op => cases op <;> simp_all [knownOpHOL]
  | intOp op => cases op <;> simp_all [knownOpHOL]
  | memOp op =>
    cases op with
    | el =>
      cases args with
      | nil => simp_all [knownOpHOL]
      | cons x xs =>
        cases xs with
        | nil => cases x <;> simp_all [knownOpHOL]
        | cons y ys =>
          cases ys with
          | nil =>
            cases x <;> cases y <;> simp_all [knownOpHOL]
            all_goals split at known <;> simp_all
          | cons z zs => cases x <;> cases y <;> simp_all [knownOpHOL]
    | _ => simp_all [knownOpHOL]
  | _ => simp_all [knownOpHOL]

/-- Any resulting lookup either was present unchanged or belongs to the
operation's global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_changed_globals_cases"]
theorem knownOpChangedGlobalsCases (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (result : ValApprox) (g : Spt ValApprox)
    (known : knownOpHOL op args g0 = (result, g)) :
    ∀ k a, sptLookup k g = some a →
      sptLookup k g0 = some a ∨ opGlobalBag op k ≠ 0 := by
  intro k a found
  by_cases outside : opGlobalBag op k = 0
  · left
    rw [← knownOpLookupUnchanged op args g0 result g k known outside]
    exact found
  · exact Or.inr outside

/-- Changes to the domain or existing lookup are confined to the operation's
global-write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_changed_globals"]
theorem knownOpChangedGlobals (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (result : ValApprox) (g : Spt ValApprox)
    (known : knownOpHOL op args g0 = (result, g)) :
    ∀ i, sptMem i g ∧ (sptMem i g0 → sptLookup i g ≠ sptLookup i g0) →
      opGlobalBag op i ≠ 0 := by
  intro i ⟨member, changed⟩
  obtain ⟨value, found⟩ := (sptMem_iff_lookup i g).1 member
  rcases knownOpChangedGlobalsCases op args g0 result g known i value found with old | added
  · have oldMember := (sptMem_iff_lookup i g0).2 ⟨value, old⟩
    exact False.elim (changed oldMember (found.trans old.symm))
  · exact added

/-- The result domain is included in the previous domain plus the write bag. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "known_op_changed_globals_alt_set"]
theorem knownOpChangedGlobalsAltSet (op : ClosLang.Op) (args : List ValApprox)
    (g0 : Spt ValApprox) (result : ValApprox) (g : Spt ValApprox)
    (known : knownOpHOL op args g0 = (result, g)) :
    ∀ i, sptMem i g → sptMem i g0 ∨ opGlobalBag op i ≠ 0 := by
  intro i member
  obtain ⟨value, found⟩ := (sptMem_iff_lookup i g).1 member
  rcases knownOpChangedGlobalsCases op args g0 result g known i value found with old | added
  · exact Or.inl ((sptMem_iff_lookup i g0).2 ⟨value, old⟩)
  · exact Or.inr added

end Flapjack.Compiler.Backend.ClosKnown
