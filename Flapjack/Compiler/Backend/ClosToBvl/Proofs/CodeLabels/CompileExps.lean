module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.CodeLabels
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.Accumulator
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.InitialCodeDomain
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ExpsEquivalence
public import Flapjack.Compiler.Backend.Semantics.ClosProps.CodeLabels
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Syntactic.LabelsAndArity
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations

@[expose] public section

namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang
private abbrev Aux := List (Nat × Nat × Bvl.Exp)
private def auxLabels (aux : Aux) : Set Nat := BvlProps.getCodeLabelsList (aux.map fun t => t.2.2)
private def limitLabels (app : Nat) (source : Set Nat) (aux : Aux) : Set Nat :=
  (Set.image (fun k => numStubs app + k) source) ∪ auxLabels aux ∪
    (sptDomain (initCode app) : Set Nat) ∪ {numStubs app - 2}

private theorem varLabels (app : Nat) (tr : BackendCommon.Tra) (v : Nat) (aux : Aux) :
    BvlProps.getCodeLabels (compileExpHOL app (.var tr v) aux).1 ∪
      auxLabels (compileExpHOL app (.var tr v) aux).2 ⊆
      limitLabels app (ClosProps.getCodeLabels (.var tr v)) aux := by
  simp [compileExpHOL, BvlProps.getCodeLabels, ClosProps.getCodeLabels, limitLabels]
  intro key member
  exact Or.inr (Set.mem_union_left _ member)

end Flapjack.Compiler.Backend.ClosToBvl

namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang
private theorem labelsVarList (xs : List Nat) :
    BvlProps.getCodeLabelsList (xs.map Bvl.Exp.var) = ∅ := by
  induction xs with
  | nil => simp [BvlProps.getCodeLabelsList]
  | cons x xs ih => simp [BvlProps.getCodeLabelsList, BvlProps.getCodeLabels, ih]

private theorem labelsAppend (xs ys : List Bvl.Exp) :
    BvlProps.getCodeLabelsList (xs ++ ys) =
      BvlProps.getCodeLabelsList xs ∪ BvlProps.getCodeLabelsList ys := by
  induction xs with
  | nil => simp [BvlProps.getCodeLabelsList]
  | cons x xs ih => simp [BvlProps.getCodeLabelsList, ih, Set.union_assoc]

private theorem labelsReverse (xs : List Bvl.Exp) :
    BvlProps.getCodeLabelsList xs.reverse = BvlProps.getCodeLabelsList xs := by
  simp only [BvlProps.getCodeLabelsList_eq]
  ext label
  simp

private theorem labelsMkClCall (n : Nat) :
    BvlProps.getCodeLabels (mkClCall (.var n) ((List.range n).map Bvl.Exp.var)) = {n - 1} := by
  change BvlProps.getCodeLabels
    (.ifThenElse
      (.op (.blockOp (.equalConst (.int (Int.ofNat (((List.range n).map Bvl.Exp.var).length - 1)))))
        [.op (.blockOp (.elemAt 1)) [.var n]])
      (.call (((List.range n).map Bvl.Exp.var).length - 1) none
        (((List.range n).map Bvl.Exp.var) ++ [.var n, .op (.blockOp (.elemAt 0)) [.var n]]))
      (.call 0 (some (genericAppFnLocation (((List.range n).map Bvl.Exp.var).length - 1)))
        (((List.range n).map Bvl.Exp.var) ++ [.var n]))) = _
  simp [BvlProps.getCodeLabels, BvlProps.getCodeLabelsList, genericAppFnLocation,
    assignGetCodeLabel, labelsAppend, labelsVarList]

end Flapjack.Compiler.Backend.ClosToBvl

namespace Flapjack.Compiler.Backend.ClosToBvl
private theorem labelsElemVarList (xs : List Nat) (v : Nat) :
    BvlProps.getCodeLabelsList (xs.map fun i => .op (.blockOp (.elemAt i)) [.var v]) = ∅ := by
  induction xs with
  | nil => simp [BvlProps.getCodeLabelsList]
  | cons x xs ih => simp [BvlProps.getCodeLabelsList, BvlProps.getCodeLabels,
      ClosLang.assignGetCodeLabel, ih]

private theorem labelsFreeLet (v count : Nat) :
    BvlProps.getCodeLabelsList (freeLet (.var v) count) = ∅ := by
  change BvlProps.getCodeLabelsList ((List.range count).map fun i =>
    .op (.blockOp (.elemAt (i + 2))) [.var v]) = ∅
  simpa [List.map_map, Function.comp_def] using
    labelsElemVarList ((List.range count).map fun i => i + 2) v

private theorem labelsReccCase (n arity : Nat) (body : Bvl.Exp) :
    BvlProps.getCodeLabels (codeForReccCase n arity body).2 = BvlProps.getCodeLabels body := by
  change BvlProps.getCodeLabels
    (.let [.op (.blockOp (.elemAt 2)) [.var arity]]
      (.let (((List.range arity).map fun a => .var (a + 1)) ++
        ((List.range n).map fun i => .op (.blockOp (.elemAt i)) [.var 0])) body)) = _
  have vars := labelsVarList ((List.range arity).map fun a => a + 1)
  simp only [List.map_map, Function.comp_def] at vars
  simp [BvlProps.getCodeLabels, BvlProps.getCodeLabelsList, ClosLang.assignGetCodeLabel,
    labelsAppend, labelsElemVarList, vars]
end Flapjack.Compiler.Backend.ClosToBvl

namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps
private theorem chainLabels {X Y B C S T A D : Set Nat} {f : Nat → Nat} {v : Nat}
    (one : X ∪ B ⊆ Set.image f S ∪ A ∪ D ∪ {v})
    (two : Y ∪ C ⊆ Set.image f T ∪ B ∪ D ∪ {v}) :
    (X ∪ Y) ∪ C ⊆ Set.image f (S ∪ T) ∪ A ∪ D ∪ {v} := by
  intro x hx
  simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hx ⊢
  have one := @one x
  have two := @two x
  simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at one two
  aesop

private theorem labelsCases (n : Nat) (fs : List (Nat × Bvl.Exp)) :
    BvlProps.getCodeLabelsList ((fs.map fun p => codeForReccCase n p.1 p.2).map Prod.snd) =
      BvlProps.getCodeLabelsList (fs.map Prod.snd) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    cases p with
    | mk arity body =>
      simp only [List.map_cons, BvlProps.getCodeLabelsList, labelsReccCase, ih]

private theorem labelsConstZeroList (xs : List Nat) :
    BvlProps.getCodeLabelsList (xs.map fun _ => mkConst 0) = ∅ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, BvlProps.getCodeLabelsList, BvlProps.getCodeLabels,
      mkConst, assignGetCodeLabel, Set.empty_union]
    simpa only [mkConst] using ih

private theorem labelsBuildRecc (args vs : List Nat) (n len : Nat) (body : Bvl.Exp) :
    BvlProps.getCodeLabels (buildReccLetsHOL args vs n len body) =
      {n + 2 * (len - 1)} ∪ (fun j => n + 2 * j) '' Set.Iio (len - 1) ∪ BvlProps.getCodeLabels body := by
  simp only [buildReccLetsHOL, BvlProps.getCodeLabels, BvlProps.getCodeLabelsList,
    assignGetCodeLabel, Set.empty_union, Set.union_empty, reccLets_codeLabels]
  simp only [labelsReverse, labelsAppend, labelsConstZeroList, labelsVarList, Set.empty_union]
  simp only [reccLet0, BvlProps.getCodeLabels, BvlProps.getCodeLabelsList, mkConst, mkLabel,
    assignGetCodeLabel, Set.empty_union, Set.union_empty]
  exact (Set.union_assoc _ _ _).symm

private theorem auxBuildLabels (n : Nat) (cases : List (Nat × Bvl.Exp)) (acc : Aux)
    (next : Nat) (out : Aux) (run : buildAux n cases acc = (next, out)) :
    auxLabels out ⊆ BvlProps.getCodeLabelsList (cases.map Prod.snd) ∪ auxLabels acc := by
  intro key member
  simp only [auxLabels, BvlProps.getCodeLabelsList_eq, Set.mem_sUnion, Set.mem_image,
    Set.mem_ofPred_eq, List.mem_map] at member ⊢
  rcases member with ⟨_, ⟨body, ⟨entry, entryMem, rfl⟩, rfl⟩, bodyMem⟩
  have orig := mem_buildAux_imp_snd_mem n cases acc next out entry ⟨run, entryMem⟩
  rcases orig with inCases | inAcc
  · left
    exact ⟨_, ⟨entry.2.2, ⟨entry.2, inCases, rfl⟩, rfl⟩, bodyMem⟩
  · right
    exact ⟨_, ⟨entry.2.2, ⟨entry, inAcc, rfl⟩, rfl⟩, bodyMem⟩

mutual
private theorem exprLabels (app : Nat) (e : Exp) (aux : Aux) (positive : 0 < app)
    (noLabel : noLabels e) (arity : obeysMaxApp app e) (locations : fnLocationSomeExp e) :
    BvlProps.getCodeLabels (compileExpHOL app e aux).1 ∪
      auxLabels (compileExpHOL app e aux).2 ⊆ limitLabels app (ClosProps.getCodeLabels e) aux := by
  cases e with
  | var tr v => exact varLabels app tr v aux
  | handle tr body handler =>
    simp only [noLabels] at noLabel
    simp only [obeysMaxApp] at arity
    simp only [fnLocationSomeExp] at locations
    cases hbody : compileExpHOL app body aux with
    | mk out middle =>
      cases hhandler : compileExpHOL app handler middle with
      | mk other final =>
        have one := exprLabels app body aux positive noLabel.1 arity.1 locations.1
        have two := exprLabels app handler middle positive noLabel.2 arity.2 locations.2
        simp only [hbody] at one
        simp only [hhandler] at two
        simpa only [compileExpHOL, hbody, hhandler, BvlProps.getCodeLabels,
          ClosProps.getCodeLabels, limitLabels] using chainLabels one two
  | «let» tr bindings body =>
    simp only [noLabels] at noLabel
    simp only [obeysMaxApp] at arity
    simp only [fnLocationSomeExp] at locations
    cases hbindings : compileExpListHOL app bindings aux with
    | mk out middle =>
      cases hbody : compileExpHOL app body middle with
      | mk other final =>
        have one := listLabels app bindings aux positive noLabel.1 arity.1 locations.2
        have two := exprLabels app body middle positive noLabel.2 arity.2 locations.1
        simp only [hbindings] at one
        simp only [hbody] at two
        simpa only [compileExpHOL, hbindings, hbody, BvlProps.getCodeLabels,
          ClosProps.getCodeLabels, limitLabels] using chainLabels one two
  | ifThenElse tr x y z =>
    simp only [noLabels] at noLabel
    simp only [obeysMaxApp] at arity
    simp only [fnLocationSomeExp] at locations
    cases hx : compileExpHOL app x aux with
    | mk ox ax =>
      cases hy : compileExpHOL app y ax with
      | mk oy ay =>
        cases hz : compileExpHOL app z ay with
        | mk oz az =>
          have one := exprLabels app x aux positive noLabel.1 arity.1 locations.1
          have two := exprLabels app y ax positive noLabel.2.1 arity.2.1 locations.2.1
          have three := exprLabels app z ay positive noLabel.2.2 arity.2.2 locations.2.2
          simp only [hx] at one
          simp only [hy] at two
          simp only [hz] at three
          simpa only [compileExpHOL, hx, hy, hz, BvlProps.getCodeLabels,
            ClosProps.getCodeLabels, limitLabels] using chainLabels (chainLabels one two) three
  | raise tr body =>
    have ih := exprLabels app body aux positive (by simpa [noLabels] using noLabel)
      (by simpa [obeysMaxApp] using arity) (by simpa [fnLocationSomeExp] using locations)
    cases run : compileExpHOL app body aux with
    | mk out next =>
      simpa [compileExpHOL, run, BvlProps.getCodeLabels, ClosProps.getCodeLabels] using ih
  | tick tr body =>
    have ih := exprLabels app body aux positive (by simpa [noLabels] using noLabel)
      (by simpa [obeysMaxApp] using arity) (by simpa [fnLocationSomeExp] using locations)
    cases run : compileExpHOL app body aux with
    | mk out next =>
      simpa [compileExpHOL, run, BvlProps.getCodeLabels, ClosProps.getCodeLabels] using ih
  | call tr ticks dest args =>
    have ih := listLabels app args aux positive (by simpa [noLabels] using noLabel)
      (by simpa [obeysMaxApp] using arity) (by simpa [fnLocationSomeExp] using locations)
    cases run : compileExpListHOL app args aux with
    | mk out next =>
      simp only [run] at ih
      simp only [compileExpHOL, run, BvlProps.getCodeLabels, ClosProps.getCodeLabels,
        limitLabels] at *
      have widen : ((fun k => numStubs app + k) '' getCodeLabelsList args ∪ auxLabels aux ∪
          sptDomain (initCode app)) ⊆ ((fun k => numStubs app + k) ''
            insert dest (getCodeLabelsList args) ∪ auxLabels aux ∪ sptDomain (initCode app)) := by
        exact Set.union_subset_union (Set.union_subset_union
          (Set.image_mono (Set.subset_insert _ _)) (Set.Subset.refl _)) (Set.Subset.refl _)
      intro key member
      simp only [Set.mem_union, Set.mem_singleton_iff] at member ih ⊢
      rcases member with (rfl | member) | member
      · left; left; left; exact ⟨dest, Or.inl rfl, Nat.add_comm _ _⟩
      · have h := ih (Or.inl member)
        simp only [Set.mem_union] at h ⊢
        aesop (add safe widen)
      · have h := ih (Or.inr member)
        simp only [Set.mem_union] at h ⊢
        aesop (add safe widen)
  | app tr loc fn args =>
    simp only [noLabels] at noLabel
    simp only [obeysMaxApp] at arity
    simp only [fnLocationSomeExp] at locations
    cases hfn : compileExpHOL app fn aux with
    | mk fout middle =>
      cases hargs : compileExpListHOL app args middle with
      | mk aout final =>
        have first := exprLabels app fn aux positive noLabel.1 arity.2.1 locations.1
        have rest := listLabels app args middle positive noLabel.2 arity.2.2 locations.2
        simp only [hfn] at first
        simp only [hargs] at rest
        have combined := chainLabels first rest
        have len := compileExpList_length app args middle
        simp only [hargs] at len
        have stub : sptDomain (initCode app) (aout.length - 1) := by
          rw [domain_initCode app positive]
          change aout.length - 1 < app + app * (app - 1) / 2
          omega
        cases loc with
        | none =>
          simp only [compileExpHOL, hfn, hargs, BvlProps.getCodeLabels,
            ClosProps.getCodeLabels, labelsAppend, BvlProps.getCodeLabelsList,
            labelsMkClCall, Set.union_empty, Set.empty_union, limitLabels]
          intro key member
          simp only [Set.mem_union, Set.mem_singleton_iff] at member
          rcases member with ((ha | hf) | rfl) | hn
          · exact combined (by simp only [Set.mem_union]; aesop)
          · exact combined (by simp only [Set.mem_union]; aesop)
          · exact Or.inl (Or.inr stub)
          · exact combined (by simp only [Set.mem_union]; aesop)
        | some loc =>
          simp only [compileExpHOL, hfn, hargs, BvlProps.getCodeLabels,
            ClosProps.getCodeLabels, labelsAppend, BvlProps.getCodeLabelsList,
            Set.union_empty, limitLabels]
          have smaller : getCodeLabels fn ∪ getCodeLabelsList args ⊆
              {loc} ∪ getCodeLabels fn ∪ getCodeLabelsList args := by
            intro key h
            simp only [Set.mem_union] at h ⊢
            aesop
          have widen : ((fun k => numStubs app + k) '' (getCodeLabels fn ∪ getCodeLabelsList args) ∪
              auxLabels aux ∪ (sptDomain (initCode app) : Set Nat) ∪ {numStubs app - 2}) ⊆
              ((fun k => numStubs app + k) '' ({loc} ∪ getCodeLabels fn ∪ getCodeLabelsList args) ∪
              auxLabels aux ∪ (sptDomain (initCode app) : Set Nat) ∪ {numStubs app - 2}) := by
            exact Set.union_subset_union (Set.union_subset_union (Set.union_subset_union
              (Set.image_mono smaller) (Set.Subset.refl _)) (Set.Subset.refl _)) (Set.Subset.refl _)
          intro key member
          simp only [Set.mem_union, Set.mem_singleton_iff] at member
          rcases member with (rfl | member | member) | member
          · left; left; left
            exact ⟨loc, by simp, Nat.add_comm _ _⟩
          · apply widen
            apply combined
            simp only [Set.mem_union]
            aesop
          · apply widen
            apply combined
            simp only [Set.mem_union]
            aesop
          · apply widen
            apply combined
            simp only [Set.mem_union]
            aesop
  | fn tr loc vs args body =>
    simp only [fnLocationSomeExp] at locations
    cases loc with
    | none => simp at locations
    | some loc =>
      cases run : compileExpHOL app body aux with
      | mk out next =>
        have ih := exprLabels app body aux positive (by simpa [noLabels] using noLabel)
          (by simpa [obeysMaxApp] using arity) locations.2
        simp only [run] at ih
        simp only [compileExpHOL, run, Option.getD_some, BvlProps.getCodeLabels,
          ClosProps.getCodeLabels, auxLabels, List.map_cons, labelsAppend,
          BvlProps.getCodeLabelsList, labelsFreeLet, Set.union_empty, limitLabels] at *
        simp only [assignGetCodeLabel, Set.empty_union, labelsReverse, BvlProps.getCodeLabelsList,
          BvlProps.getCodeLabels, mkLabel, mkConst, labelsVarList, Set.union_empty]
        have widen : ((fun k => numStubs app + k) '' getCodeLabels body ∪
            BvlProps.getCodeLabelsList (aux.map fun t => t.2.2) ∪
            (sptDomain (initCode app) : Set Nat) ∪ {numStubs app - 2}) ⊆
            ((fun k => numStubs app + k) '' ({loc} ∪ getCodeLabels body) ∪
            BvlProps.getCodeLabelsList (aux.map fun t => t.2.2) ∪
            (sptDomain (initCode app) : Set Nat) ∪ {numStubs app - 2}) := by
          exact Set.union_subset_union (Set.union_subset_union (Set.union_subset_union
            (Set.image_mono (Set.subset_union_right)) (Set.Subset.refl _))
            (Set.Subset.refl _)) (Set.Subset.refl _)
        intro key member
        simp only [Set.mem_union, Set.mem_singleton_iff] at member
        rcases member with rfl | member | member
        · left; left; left; exact ⟨loc, by simp, Nat.add_comm _ _⟩
        · exact widen (ih (Or.inl member))
        · exact widen (ih (Or.inr member))
  | letrec tr loc vs fs body =>
    simp only [noLabels] at noLabel
    simp only [obeysMaxApp] at arity
    simp only [fnLocationSomeExp] at locations
    cases loc with
    | none => simp at locations
    | some loc =>
      cases fs with
      | nil =>
        have ih := exprLabels app body aux positive noLabel.2 arity.2 locations.2.2
        have emptyIio : Set.Iio (0 : Nat) = ∅ := by
          ext n
          exact iff_false_intro (Nat.not_lt_zero n)
        simpa [compileExpHOL, ClosProps.getCodeLabels, ClosProps.getCodeLabelsFuns,
          limitLabels, emptyIio] using ih
      | cons first rest =>
        cases rest with
        | nil =>
          cases first with
          | mk args fnbody =>
            simp only [noLabelsFuns] at noLabel
            simp only [obeysMaxAppFuns] at arity
            simp only [fnLocationSomeFuns] at locations
            cases hfn : compileExpHOL app fnbody aux with
            | mk fout middle =>
              let newBody := Bvl.Exp.let ((List.range args).map Bvl.Exp.var ++ [.var args] ++
                freeLet (.var args) (vs.getD []).length) fout
              let mid := (loc + numStubs app, args + 1, newBody) :: middle
              cases hbody : compileExpHOL app body mid with
              | mk bout final =>
                have one := exprLabels app fnbody aux positive noLabel.1.1 arity.1.1 locations.2.1.1
                have two := exprLabels app body mid positive noLabel.2 arity.2 locations.2.2
                simp only [hfn] at one
                simp only [hbody] at two
                simp only [compileExpHOL, hfn, Option.getD_some]
                change compileExpHOL app body ((loc + numStubs app, args + 1, newBody) :: middle) = (bout, final) at hbody
                rw [hbody]
                change BvlProps.getCodeLabels (.let [(.op (.blockOp (.cons 30))
                  ((mkLabel (loc + numStubs app) :: mkConst (args - 1) :: (vs.getD []).map Bvl.Exp.var).reverse))] bout) ∪
                    auxLabels final ⊆ _
                simp only [BvlProps.getCodeLabels, BvlProps.getCodeLabelsList,
                  Set.union_empty]
                have newBodyLabels : BvlProps.getCodeLabels newBody = BvlProps.getCodeLabels fout := by
                  simp [newBody, BvlProps.getCodeLabels, labelsAppend, BvlProps.getCodeLabelsList,
                    labelsVarList, labelsFreeLet]
                have midLabels : auxLabels mid = BvlProps.getCodeLabels fout ∪ auxLabels middle := by
                  simp [mid, auxLabels, BvlProps.getCodeLabelsList, newBodyLabels]
                simp only [limitLabels, midLabels] at two
                simp only [limitLabels] at one
                simp only [assignGetCodeLabel, Set.empty_union, labelsReverse, BvlProps.getCodeLabelsList,
                  BvlProps.getCodeLabels, mkLabel, mkConst, labelsVarList, Set.union_empty]
                have combined : BvlProps.getCodeLabels bout ∪ auxLabels final ⊆
                    (fun k => numStubs app + k) '' (getCodeLabels fnbody ∪ getCodeLabels body) ∪
                    auxLabels aux ∪ (sptDomain (initCode app) : Set Nat) ∪ {numStubs app - 2} := by
                  have h := chainLabels (X := ∅) (by simpa using one) two
                  simpa using h
                have iloc : (fun k : Nat => loc + 2 * k) '' Set.Iio 1 = {loc} := by
                  ext k
                  simp only [Set.mem_image, Set.mem_Iio, Set.mem_singleton_iff]
                  constructor
                  · rintro ⟨i, hi, rfl⟩
                    have : i = 0 := by omega
                    simp [this]
                  · intro h
                    subst k
                    exact ⟨0, by omega, by simp⟩
                simp only [ClosProps.getCodeLabels, ClosProps.getCodeLabelsFuns,
                  Set.union_empty, limitLabels, List.length_cons, List.length_nil, iloc]
                have smaller : getCodeLabels fnbody ∪ getCodeLabels body ⊆
                    ({loc} ∪ getCodeLabels body) ∪ getCodeLabels fnbody := by
                  intro k h
                  simp only [Set.mem_union] at h ⊢
                  aesop
                have widen : ((fun k => numStubs app + k) '' (getCodeLabels fnbody ∪ getCodeLabels body) ∪
                    auxLabels aux ∪ (sptDomain (initCode app) : Set Nat) ∪ {numStubs app - 2}) ⊆
                    ((fun k => numStubs app + k) '' (({loc} ∪ getCodeLabels body) ∪ getCodeLabels fnbody) ∪
                    auxLabels aux ∪ (sptDomain (initCode app) : Set Nat) ∪ {numStubs app - 2}) := by
                  exact Set.union_subset_union (Set.union_subset_union (Set.union_subset_union
                    (Set.image_mono smaller) (Set.Subset.refl _)) (Set.Subset.refl _)) (Set.Subset.refl _)
                intro key member
                simp only [Set.mem_union, Set.mem_singleton_iff] at member
                rcases member with (rfl | member) | member
                · left; left; left
                  exact ⟨loc, by simp, Nat.add_comm _ _⟩
                · exact widen (combined (Or.inl member))
                · exact widen (combined (Or.inr member))
        | cons second tail =>
          let fs := first :: second :: tail
          cases hfun : compileExpFunsHOL app fs aux with
          | mk compiled middle =>
            let cases := compiled.map fun p => codeForReccCase (fs.length + (vs.getD []).length) p.1 p.2
            cases hbuild : buildAux (loc + numStubs app) cases middle with
            | mk endLoc built =>
              cases hbody : compileExpHOL app body built with
              | mk bout final =>
                have one := funsLabels app fs aux positive noLabel.1 arity.1 locations.2.1
                have two := exprLabels app body built positive noLabel.2 arity.2 locations.2.2
                simp only [hfun] at one
                simp only [hbody] at two
                have buildBound := auxBuildLabels (loc + numStubs app) cases middle endLoc built hbuild
                simp only [cases, labelsCases] at buildBound
                simp only [compileExpHOL, Option.getD_some]
                rw [hfun]
                rw [hbuild]
                rw [hbody]
                change BvlProps.getCodeLabels
                  (buildReccLetsHOL (fs.map Prod.fst) (vs.getD []) (loc + numStubs app) fs.length bout) ∪
                    auxLabels final ⊆ _
                simp only [labelsBuildRecc, ClosProps.getCodeLabels, limitLabels]
                simp only [limitLabels] at one two
                have twoWidened := Set.Subset.trans two
                  (Set.union_subset_union (Set.union_subset_union (Set.union_subset_union
                    (Set.Subset.refl _) buildBound) (Set.Subset.refl _)) (Set.Subset.refl _))
                have combined := chainLabels (X := ∅) (by simpa using one) twoWidened
                have smaller : getCodeLabelsFuns fs ∪ getCodeLabels body ⊆
                    ((fun k => loc + 2 * k) '' Set.Iio fs.length ∪ getCodeLabels body) ∪ getCodeLabelsFuns fs := by
                  intro k h
                  simp only [Set.mem_union] at h ⊢
                  aesop
                have widen := Set.union_subset_union (Set.union_subset_union (Set.union_subset_union
                  (Set.image_mono (f := fun k => numStubs app + k) smaller) (Set.Subset.refl (auxLabels aux)))
                    (Set.Subset.refl (sptDomain (initCode app) : Set Nat)))
                    (Set.Subset.refl ({numStubs app - 2} : Set Nat))
                intro key member
                simp only [Set.mem_union, Set.mem_singleton_iff] at member
                rcases member with (((rfl | generated) | inBody) | inAux)
                · left; left; left
                  refine ⟨loc + 2 * (fs.length - 1), Or.inl (Or.inl ?_), by dsimp; omega⟩
                  exact ⟨fs.length - 1, by simp only [Set.mem_Iio, fs, List.length_cons]; omega, rfl⟩
                · rcases generated with ⟨index, indexBound, rfl⟩
                  left; left; left
                  refine ⟨loc + 2 * index, Or.inl (Or.inl ?_), by dsimp; omega⟩
                  exact ⟨index, by simp only [Set.mem_Iio, fs] at indexBound ⊢; omega, rfl⟩
                · apply widen
                  apply combined
                  simp only [Set.mem_union, Set.mem_empty_iff_false, false_or]
                  exact Or.inl inBody
                · apply widen
                  apply combined
                  simp only [Set.mem_union, Set.mem_empty_iff_false, false_or]
                  exact Or.inr inAux
  | op tr op args =>
    simp only [noLabels] at noLabel
    have ih := listLabels app args aux positive noLabel.2
      (by simpa [obeysMaxApp] using arity) (by simpa [fnLocationSomeExp] using locations)
    have absent : Flapjack.holOptionSome (fun n : Nat => op = .label n) = none := by
      simp [Flapjack.holOptionSome, noLabel.1]
    have compiled : assignGetCodeLabel (compileOp op) = ∅ := by
      rw [assignGetCodeLabel_compileOp, absent]
    have original : assignGetCodeLabel op = ∅ := by
      cases op <;> simp_all [assignGetCodeLabel]
    cases run : compileExpListHOL app args aux with
    | mk out next =>
      simp only [run] at ih
      simp only [compileExpHOL, run, ClosProps.getCodeLabels, original, Set.union_empty]
      split <;> simp_all [BvlProps.getCodeLabels, BvlProps.getCodeLabelsList,
        assignGetCodeLabel, limitLabels, Set.subset_def]
      all_goals aesop

termination_by sizeOf e

private theorem listLabels (app : Nat) (es : List Exp) (aux : Aux) (positive : 0 < app)
    (noLabel : noLabelsList es) (arity : obeysMaxAppList app es) (locations : everyFnLocationSome es) :
    BvlProps.getCodeLabelsList (compileExpListHOL app es aux).1 ∪
      auxLabels (compileExpListHOL app es aux).2 ⊆ limitLabels app (ClosProps.getCodeLabelsList es) aux := by
  cases es with
  | nil =>
    simp [compileExpListHOL, BvlProps.getCodeLabelsList, ClosProps.getCodeLabelsList, limitLabels]
    intro key member
    exact Or.inr (Set.mem_union_left _ member)
  | cons first rest =>
    simp only [noLabelsList] at noLabel
    simp only [obeysMaxAppList] at arity
    simp only [everyFnLocationSome] at locations
    cases hfirst : compileExpHOL app first aux with
    | mk target middle =>
      cases hrest : compileExpListHOL app rest middle with
      | mk targets final =>
        have firstIH := exprLabels app first aux positive noLabel.1 arity.1 locations.1
        have restIH := listLabels app rest middle positive noLabel.2 arity.2 locations.2
        simp only [hfirst] at firstIH
        simp only [hrest] at restIH
        simp only [compileExpListHOL, hfirst, hrest, BvlProps.getCodeLabelsList,
          ClosProps.getCodeLabelsList]
        exact chainLabels firstIH restIH
termination_by sizeOf es

private theorem funsLabels (app : Nat) (fs : List (Nat × Exp)) (aux : Aux) (positive : 0 < app)
    (noLabel : noLabelsFuns fs) (arity : obeysMaxAppFuns app fs) (locations : fnLocationSomeFuns fs) :
    BvlProps.getCodeLabelsList ((compileExpFunsHOL app fs aux).1.map Prod.snd) ∪
      auxLabels (compileExpFunsHOL app fs aux).2 ⊆ limitLabels app (ClosProps.getCodeLabelsFuns fs) aux := by
  cases fs with
  | nil =>
    simp [compileExpFunsHOL, BvlProps.getCodeLabelsList, ClosProps.getCodeLabelsFuns, limitLabels]
    intro key member
    exact Or.inr (Set.mem_union_left _ member)
  | cons first rest =>
    cases first with
    | mk arg body =>
      simp only [noLabelsFuns] at noLabel
      simp only [obeysMaxAppFuns] at arity
      simp only [fnLocationSomeFuns] at locations
      cases hfirst : compileExpHOL app body aux with
      | mk target middle =>
        cases hrest : compileExpFunsHOL app rest middle with
        | mk targets final =>
          have firstIH := exprLabels app body aux positive noLabel.1 arity.1 locations.1
          have restIH := funsLabels app rest middle positive noLabel.2 arity.2 locations.2
          simp only [hfirst] at firstIH
          simp only [hrest] at restIH
          simp only [compileExpFunsHOL, hfirst, hrest, List.map_cons,
            BvlProps.getCodeLabelsList, ClosProps.getCodeLabelsFuns]
          exact chainLabels firstIH restIH
termination_by sizeOf fs
end
end Flapjack.Compiler.Backend.ClosToBvl

namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack ClosLang ClosProps

/-- Code labels emitted by closure compilation arise from source labels,
existing auxiliary code, or the original compiler's reserved stubs. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_exps_code_labels"]
theorem compileExps_codeLabels (app : Nat) (es1 : List Exp) (aux1 : List (Nat × Nat × Bvl.Exp))
    (es2 : List Bvl.Exp) (aux2 : List (Nat × Nat × Bvl.Exp))
    (h : compileExpsHOL app es1 aux1 = (es2, aux2) ∧
      (∀ e ∈ es1, noLabels e) ∧ 0 < app ∧
      (∀ e ∈ es1, obeysMaxApp app e) ∧ everyFnLocationSome es1) :
    (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ es2})) ∪
      (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ aux2.map (fun t => t.2.2)})) ⊆
    (fun k => numStubs app + k) '' (⋃₀ (ClosProps.getCodeLabels '' {e | e ∈ es1})) ∪
      (⋃₀ (BvlProps.getCodeLabels '' {e | e ∈ aux1.map (fun t => t.2.2)})) ∪
      (sptDomain (initCode app) : Set Nat) ∪ {numStubs app - 2} := by
  have run : compileExpListHOL app es1 aux1 = (es2, aux2) := by
    rw [← compileExps_eq_list]
    exact h.1
  have result := listLabels app es1 aux1 h.2.2.1
    ((noLabelsList_iff es1).2 h.2.1)
    ((obeysMaxAppList_iff app es1).2 h.2.2.2.1) h.2.2.2.2
  simpa only [run, auxLabels, limitLabels, BvlProps.getCodeLabelsList_eq,
    ClosProps.getCodeLabelsList_eq] using result
end Flapjack.Compiler.Backend.ClosToBvl
