module

public import Flapjack.Compiler.Backend.ClosKnown.Proofs.KnownGlobals
public import Flapjack.Compiler.Backend.ClosKnownProps.Merge

@[expose] public section

/-! Tree inclusion across sequential known-function traversals. -/
namespace Flapjack.Compiler.Backend.ClosKnown.SubsptComposition
open ClosProps

/-- An intermediate better-defined tree is included when the endpoints agree. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "subspt_better_definedg"]
theorem subsptBetterDefinedG (sp1 sp2 sp3 : Spt ValApprox)
    (h : sptSubspt sp1 sp3 ∧ ClosKnownProps.betterDefinedG sp1 sp2 ∧
      ClosKnownProps.betterDefinedG sp2 sp3) : sptSubspt sp1 sp2 := by
  intro k member
  obtain ⟨member2, related12⟩ := h.2.1 k member
  obtain ⟨_, related23⟩ := h.2.2 k member2
  obtain ⟨a, ha⟩ := (sptMem_iff_lookup k sp1).mp member
  obtain ⟨b, hb⟩ := (sptMem_iff_lookup k sp2).mp member2
  have hc : sptLookup k sp3 = some a := by rw [(h.1 k member).2, ha]
  simp only [ha, hb, Flapjack.holThe] at related12
  simp only [hb, hc, Flapjack.holThe] at related23
  have eq := ClosKnownProps.subapproxAntisym a b ⟨related12, related23⟩
  exact ⟨member2, by rw [ha, hb, eq]⟩

/-- Two disjoint write frames cannot hide an intermediate change when the
initial tree is included in the final tree. This is Flapjack infrastructure. -/
private theorem framedSubspt {A : Type} (g0 g1 g2 : Spt A) (writes1 writes2 : Nat → Nat)
    (frame1 : ∀ i, writes1 i = 0 → sptLookup i g1 = sptLookup i g0)
    (frame2 : ∀ i, writes2 i = 0 → sptLookup i g2 = sptLookup i g1)
    (sub : sptSubspt g0 g2) (disjoint : ∀ i, writes1 i = 0 ∨ writes2 i = 0) :
    sptSubspt g0 g1 ∧ sptSubspt g1 g2 := by
  constructor
  · intro i member
    obtain ⟨_, finalEq⟩ := sub i member
    have middleEq : sptLookup i g1 = sptLookup i g0 := by
      rcases disjoint i with first | second
      · exact frame1 i first
      · exact (frame2 i second).symm.trans finalEq
    obtain ⟨value, found⟩ := (sptMem_iff_lookup i g0).1 member
    exact ⟨(sptMem_iff_lookup i g1).2 ⟨value, middleEq.trans found⟩, middleEq⟩
  · intro i member
    have finalEq : sptLookup i g2 = sptLookup i g1 := by
      rcases disjoint i with first | second
      · have middleEq := frame1 i first
        obtain ⟨value, found⟩ := (sptMem_iff_lookup i g1).1 member
        have oldFound : sptLookup i g0 = some value := middleEq.symm.trans found
        have oldMember := (sptMem_iff_lookup i g0).2 ⟨value, oldFound⟩
        exact (sub i oldMember).2.trans middleEq.symm
      · exact frame2 i second
    obtain ⟨value, found⟩ := (sptMem_iff_lookup i g1).1 member
    exact ⟨(sptMem_iff_lookup i g2).2 ⟨value, finalEq.trans found⟩, finalEq⟩

/-- Disjoint sequential traversals inherit inclusion of the initial tree in
the final tree at both intermediate steps. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "subspt_known_elist_globals"]
theorem subsptKnownElistGlobals (c : Config) (es1 : List ClosLang.Exp) (as1 : List ValApprox)
    (g0 : Spt ValApprox) (al1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox)
    (es2 : List ClosLang.Exp) (as2 : List ValApprox) (al2 : List (ClosLang.Exp × ValApprox))
    (g2 : Spt ValApprox)
    (h : knownListTotal c es1 as1 g0 = (al1, g1) ∧ knownListTotal c es2 as2 g1 = (al2, g2) ∧
      sptSubspt g0 g2 ∧ ∀ i, elistGlobals es1 i = 0 ∨ elistGlobals es2 i = 0) :
    sptSubspt g0 g1 ∧ sptSubspt g1 g2 := by
  obtain ⟨first, second, sub, disjoint⟩ := h
  apply framedSubspt g0 g1 g2 (elistGlobals es1) (elistGlobals es2) ?_ ?_ sub disjoint
  · intro i outside
    have frame := knownListTotalLookupUnchanged c es1 as1 g0 i outside
    simpa [first] using frame
  · intro i outside
    have frame := knownListTotalLookupUnchanged c es2 as2 g1 i outside
    simpa [second] using frame

/-- A traversal followed by a disjoint primitive operation inherits inclusion
at both intermediate steps. -/
@[hol "cakeml/compiler/backend/proofs/clos_knownProofScript.sml" "subspt_known_op_elist_globals"]
theorem subsptKnownOpElistGlobals (c : Config) (es : List ClosLang.Exp) (as1 : List ValApprox)
    (g0 : Spt ValApprox) (al1 : List (ClosLang.Exp × ValApprox)) (g1 : Spt ValApprox)
    (op : ClosLang.Op) (as2 : List ValApprox) (g2 : Spt ValApprox) (a : ValApprox)
    (h : knownListTotal c es as1 g0 = (al1, g1) ∧ knownOpHOL op as2 g1 = (a, g2) ∧
      sptSubspt g0 g2 ∧ ∀ i, opGlobalBag op i = 0 ∨ elistGlobals es i = 0) :
    sptSubspt g0 g1 ∧ sptSubspt g1 g2 := by
  obtain ⟨first, second, sub, disjoint⟩ := h
  apply framedSubspt g0 g1 g2 (elistGlobals es) (opGlobalBag op) ?_ ?_ sub ?_
  · intro i outside
    have frame := knownListTotalLookupUnchanged c es as1 g0 i outside
    simpa [first] using frame
  · intro i outside
    exact knownOpLookupUnchanged op as2 g1 a g2 i second outside
  · intro i
    exact (disjoint i).symm

end Flapjack.Compiler.Backend.ClosKnown.SubsptComposition
