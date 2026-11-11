module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CallsWellformed
public import Flapjack.Compiler.Backend.ClosCall.Proofs.CallsExtension
public import Flapjack.Compiler.Backend.ClosCall.Proofs.DomainLocations
public import Flapjack.Misc.ListEl
@[expose] public section

/-! Isolation of an indexed direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- Each indexed expression is converted between states satisfying the
original extension, well-formedness, freshness and location bounds. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_el_sing"]
theorem calls_el_sing (xs : List Exp) (g0 : State) (ys : List Exp) (g : State) (i : Nat)
    (h : calls xs g0 = (ys, g) ∧ i < xs.length ∧ (g0.2.map Prod.fst).Nodup ∧
      (codeLocations xs).Nodup ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {x | x ∈ codeLocations xs} ∧ label ∈ g0.2.map Prod.fst)) ∧
      wellFormed g0 ∧ everyFnLocationSome xs) :
    ∃ ga gb,
      calls [holEl i xs] ga = ([holEl i ys], gb) ∧
      stateExtends g0 ga ∧ stateExtends ga gb ∧ stateExtends gb g ∧ wellFormed ga ∧ wellFormed gb ∧
      (∀ label, ¬ (label ∈ Set.image Nat.succ {x | x ∈ codeLocations [holEl i xs]} ∧ label ∈ ga.2.map Prod.fst)) ∧
      Set.Subset {x | x ∈ ga.2.map Prod.fst} (Set.union {x | x ∈ g0.2.map Prod.fst}
        (Set.image Nat.succ {x | x ∈ codeLocations (xs.take i)})) ∧
      Set.Subset (Set.diff {x | x ∈ codeLocations [holEl i xs]} (sptDomain gb.1))
        (Set.diff {x | x ∈ codeLocations xs} (sptDomain g.1)) := by
  induction xs generalizing g0 ys g i with
  | nil => simp at h
  | cons x xs ih =>
    obtain ⟨run, bound, oldDistinct, locationsDistinct, fresh, well, annotations⟩ := h
    cases headRun : callsSing x g0 with
    | mk headOut mid =>
      cases tailRun : callsSingList xs mid with
      | mk tailOut final =>
        change callsSingList (x :: xs) g0 = (ys, g) at run
        simp only [callsSingList, headRun, tailRun, Prod.mk.injEq] at run
        obtain ⟨rfl, rfl⟩ := run
        have headCalls : calls [x] g0 = ([headOut], mid) := by
          simp [calls, callsSingList, headRun]
        have tailCalls : calls xs mid = (tailOut, final) := tailRun
        have splitDistinct : (codeLocationsExp x ++ codeLocations xs).Nodup := by
          simpa [codeLocations] using locationsDistinct
        have headDistinct : (codeLocations [x]).Nodup := by
          simpa [codeLocations] using List.Nodup.of_append_left splitDistinct
        have tailDistinct : (codeLocations xs).Nodup := List.Nodup.of_append_right splitDistinct
        have cross := (List.nodup_append.mp splitDistinct).2.2
        have headFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {k | k ∈ codeLocations [x]} ∧
            label ∈ g0.2.map Prod.fst) := by
          intro label ⟨⟨k, member, eq⟩, old⟩
          apply fresh label
          refine ⟨⟨k, ?_, eq⟩, old⟩
          change k ∈ codeLocations [x] at member
          simp only [codeLocations, List.append_nil] at member
          simp [codeLocations, member]
        simp only [everyFnLocationSome] at annotations
        have headAnnotation : everyFnLocationSome [x] := by
          simpa [everyFnLocationSome] using annotations.1
        have tailAnnotation : everyFnLocationSome xs := annotations.2
        have headExt := calls_subg [x] g0 [headOut] mid ⟨headCalls, oldDistinct, headDistinct, headFresh⟩
        have headWell := calls_wellFormed [x] g0 [headOut] mid
          ⟨headCalls, headDistinct, headFresh, headAnnotation, well⟩
        have midDistinct : (mid.2.map Prod.fst).Nodup := headExt.2.2
        have tailFresh : ∀ label, ¬ (label ∈ Set.image Nat.succ {x | x ∈ codeLocations xs} ∧
            label ∈ mid.2.map Prod.fst) := by
          intro label ⟨⟨k, member, eq⟩, inMid⟩
          have origins := calls_addSucc_codeLocations [x] g0 [headOut] mid headCalls inMid
          rcases origins with old | ⟨q, inHead, equal⟩
          · apply fresh label
            refine ⟨⟨k, ?_, eq⟩, old⟩
            change k ∈ codeLocations xs at member
            simp [codeLocations, member]
          · simp only [codeLocations, List.append_nil] at inHead
            have same : q = k := Nat.succ.inj (equal.trans eq.symm)
            subst q
            exact cross k inHead k member rfl
        have tailExt := calls_subg xs mid tailOut final ⟨tailCalls, midDistinct, tailDistinct, tailFresh⟩
        cases i with
        | zero =>
          simp only [holEl, holHd, List.take_zero]
          refine ⟨g0, mid, headCalls, stateExtends_refl g0 oldDistinct, headExt, tailExt,
            well, headWell, headFresh, ?_, ?_⟩
          · intro label member
            exact Or.inl member
          · intro k ⟨inHead, notMid⟩
            constructor
            · change k ∈ codeLocations [x] at inHead
              simp only [codeLocations, List.append_nil] at inHead
              simp [codeLocations, inHead]
            · intro inFinal
              rcases calls_domainLocations xs mid tailOut final tailCalls inFinal with inMid | inTail
              · exact notMid inMid
              · change k ∈ codeLocations [x] at inHead
                simp only [codeLocations, List.append_nil] at inHead
                exact cross k inHead k inTail rfl
        | succ i =>
          have tailBound : i < xs.length := by simpa using bound
          obtain ⟨ga, gb, selected, midGa, gaGb, gbFinal, gaWell, gbWell, selectedFresh, priorLabels, remaining⟩ :=
            ih mid tailOut final i ⟨tailCalls, tailBound, midDistinct, tailDistinct, tailFresh, headWell, tailAnnotation⟩
          simp only [holEl, List.tail_cons, List.take_succ_cons]
          refine ⟨ga, gb, selected, stateExtends_trans g0 mid ga headExt midGa, gaGb, gbFinal,
            gaWell, gbWell, selectedFresh, ?_, ?_⟩
          · intro label member
            rcases priorLabels member with fromMid | ⟨k, inPrefix, eq⟩
            · rcases calls_addSucc_codeLocations [x] g0 [headOut] mid headCalls fromMid with old | ⟨k, inHead, eq⟩
              · exact Or.inl old
              · right
                refine ⟨k, ?_, eq⟩
                change k ∈ codeLocations [x] at inHead
                simp only [codeLocations, List.append_nil] at inHead
                simp [codeLocations, inHead]
            · right
              refine ⟨k, ?_, eq⟩
              change k ∈ codeLocations (xs.take i) at inPrefix
              simp [codeLocations, inPrefix]
          · intro k member
            have hit := remaining member
            refine ⟨?_, hit.2⟩
            have inTail : k ∈ codeLocations xs := hit.1
            simp [codeLocations, inTail]

end Flapjack.Compiler.Backend.ClosCall
