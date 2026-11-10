module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelsOriginal
public import Flapjack.Compiler.Backend.ClosCall.Proofs.InsertDomain
public import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations
import Mathlib.Data.List.Perm.Subperm

@[expose] public section

/-! Original direct-call location membership invariant. -/

namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

private theorem locations_variables (t : BackendCommon.Tra) (i n : Nat) :
    codeLocations (variablesSource t i n) = [] := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    simp [variablesSource, codeLocations_append, ih, codeLocations, codeLocationsExp]

private theorem locations_callsList {A : Type} (fns : List (Nat × A))
    (n : Nat) (tr : BackendCommon.Tra) (i : Nat) :
    codeLocations ((callsListSource tr i n fns).map Prod.snd) = [] := by
  induction fns generalizing n i with
  | nil => rfl
  | cons f fns ih =>
    obtain ⟨arity, body⟩ := f
    simp [callsListSource, codeLocations, codeLocationsExp, locations_variables, ih]

private theorem length_callsList {A : Type} (fns : List (Nat × A))
    (n : Nat) (tr : BackendCommon.Tra) (i : Nat) :
    (callsListSource tr i n fns).length = fns.length := by
  induction fns generalizing n i with
  | nil => rfl
  | cons f fns ih =>
    cases f
    simp [callsListSource, ih]

private theorem codeList_bodies {A C : Type} (fns : List (A × Exp))
    (loc : Nat) (state : C × List (Nat × A × Exp)) :
    ((codeListSource loc fns state).2.map (fun t => t.2.2)) =
      (fns.map Prod.snd).reverse ++ state.2.map (fun t => t.2.2) := by
  induction fns generalizing loc state with
  | nil => simp [codeListSource]
  | cons f fns ih =>
    obtain ⟨a, e⟩ := f
    obtain ⟨known, code⟩ := state
    simp [codeListSource, ih, List.reverse_cons, List.append_assoc]

private theorem locationSome_append (xs ys : List Exp) :
    everyFnLocationSome (xs ++ ys) ↔ everyFnLocationSome xs ∧ everyFnLocationSome ys := by
  induction xs with
  | nil => simp [everyFnLocationSome]
  | cons x xs ih => simp [everyFnLocationSome, ih, and_assoc]

private theorem varsNone_append (xs ys : List Exp) :
    everyFnVarsNone (xs ++ ys) ↔ everyFnVarsNone xs ∧ everyFnVarsNone ys := by
  induction xs with
  | nil => simp [everyFnVarsNone]
  | cons x xs ih => simp [everyFnVarsNone, ih, and_assoc]

private theorem locationSome_reverse (xs : List Exp) :
    everyFnLocationSome xs.reverse ↔ everyFnLocationSome xs := by
  induction xs with
  | nil => simp [everyFnLocationSome]
  | cons x xs ih => simp [List.reverse_cons, locationSome_append, everyFnLocationSome, ih, and_comm]

private theorem varsNone_reverse (xs : List Exp) :
    everyFnVarsNone xs.reverse ↔ everyFnVarsNone xs := by
  induction xs with
  | nil => simp [everyFnVarsNone]
  | cons x xs ih => simp [List.reverse_cons, varsNone_append, everyFnVarsNone, ih, and_comm]

/-- Generated variable lists contain no unlocated or annotated functions. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "every_Fn_GENLIST_Var"]
theorem everyFn_variables : ∀ n i t,
    everyFnLocationSome (variablesSource t i n) ∧ everyFnVarsNone (variablesSource t i n) := by
  intro n
  induction n with
  | zero => intro i t; simp [variablesSource, everyFnLocationSome, everyFnVarsNone]
  | succ n ih =>
    intro i t
    have h := ih (i + 1) t
    simpa [variablesSource, locationSome_append, varsNone_append,
      everyFnLocationSome, everyFnVarsNone, fnLocationSomeExp, fnVarsNoneExp] using h

/-- Generated direct-call stubs contain no unlocated or annotated functions. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "every_Fn_calls_list"]
theorem everyFn_callsList {α : Type} : ∀ (ls : List (Nat × α)) n i t,
    everyFnLocationSome ((callsListSource t i n ls).map Prod.snd) ∧
      everyFnVarsNone ((callsListSource t i n ls).map Prod.snd) := by
  intro ls
  induction ls with
  | nil => intro n i t; simp [callsListSource, everyFnLocationSome, everyFnVarsNone]
  | cons entry rest ih =>
    obtain ⟨arity, body⟩ := entry
    intro n i t
    have h := ih (n + 2) (i + 1) t
    have v := everyFn_variables arity 1 t
    simpa [callsListSource, everyFnLocationSome, everyFnVarsNone,
      fnLocationSomeExp, fnVarsNoneExp] using And.intro (And.intro v.1 h.1) (And.intro v.2 h.2)

/-- Auxiliary code insertion preserves exactly the two annotation predicates. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "every_Fn_code_list"]
theorem everyFn_codeList {α β : Type} : ∀ (ls : List (α × Exp)) n (rest : β × List (Nat × α × Exp)),
    (everyFnLocationSome ((codeListSource n ls rest).2.map (fun p => p.2.2)) ↔
      everyFnLocationSome (ls.map Prod.snd) ∧ everyFnLocationSome (rest.2.map (fun p => p.2.2))) ∧
    (everyFnVarsNone ((codeListSource n ls rest).2.map (fun p => p.2.2)) ↔
      everyFnVarsNone (ls.map Prod.snd) ∧ everyFnVarsNone (rest.2.map (fun p => p.2.2))) := by
  intro ls n rest
  rw [codeList_bodies]
  simp [locationSome_append, varsNone_append, locationSome_reverse, varsNone_reverse]

/-- Shared structural proof for direct-call annotation preservation. The two
HOL predicates differ only at function annotations. The `fns` parameter names
the recursive-group binder for each instance's termination proof. -/
local macro "preserveAnnotSingle " exp:ident state:ident single:ident many:ident
    one:ident all:ident funs:ident app:ident pick:ident fns:ident : tactic =>
  `(tactic| (
    intro h
    cases ($exp) with
    | var tr v => simpa [callsSing, $one:ident] using h
    | raise tr body =>
      have ih := $single body $state (by simpa [$one:ident] using h)
      cases hr : callsSing body $state with
      | mk out st => simpa [callsSing, hr, $one:ident] using ih
    | tick tr body =>
      have ih := $single body $state (by simpa [$one:ident] using h)
      cases hr : callsSing body $state with
      | mk out st => simpa [callsSing, hr, $one:ident] using ih
    | ifThenElse tr a b c =>
      simp only [$one:ident] at h
      cases ha : callsSing a $state with
      | mk oa sa =>
        have h1 := $single a $state ⟨h.1.1, h.2⟩
        simp only [ha] at h1
        cases hb : callsSing b sa with
        | mk ob sb =>
          have h2 := $single b sa ⟨h.1.2.1, h1.2⟩
          simp only [hb] at h2
          cases hc : callsSing c sb with
          | mk oc sc =>
            have h3 := $single c sb ⟨h.1.2.2, h2.2⟩
            simp only [hc] at h3
            simpa [callsSing, ha, hb, hc, $one:ident] using
              And.intro (And.intro h1.1 (And.intro h2.1 h3.1)) h3.2
    | «let» tr args body =>
      simp only [$one:ident] at h
      cases ha : callsSingList args $state with
      | mk oa sa =>
        have h1 := $many args $state ⟨h.1.2, h.2⟩
        simp only [ha] at h1
        have h2 := $single body sa ⟨h.1.1, h1.2⟩
        cases hb : callsSing body sa with
        | mk ob sb =>
          simp only [hb] at h2
          simpa [callsSing, ha, hb, $one:ident] using ⟨⟨h2.1, h1.1⟩, h2.2⟩
    | handle tr body handler =>
      simp only [$one:ident] at h
      cases ha : callsSing body $state with
      | mk oa sa =>
        have h1 := $single body $state ⟨h.1.1, h.2⟩
        simp only [ha] at h1
        have h2 := $single handler sa ⟨h.1.2, h1.2⟩
        cases hb : callsSing handler sa with
        | mk ob sb =>
          simp only [hb] at h2
          simpa [callsSing, ha, hb, $one:ident] using ⟨⟨h1.1, h2.1⟩, h2.2⟩
    | call tr ticks dest args =>
      have ih := $many args $state (by simpa [$one:ident] using h)
      cases hr : callsSingList args $state with
      | mk out st => simpa [callsSing, hr, $one:ident] using ih
    | op tr op args =>
      have ih := $many args $state (by simpa [$one:ident] using h)
      cases hr : callsSingList args $state with
      | mk out st => simpa [callsSing, hr, $one:ident] using ih
    | app tr loc body args =>
      simp only [$one:ident] at h
      cases ha : callsSingList args $state with
      | mk oa sa =>
        have h1 := $many args $state ⟨h.1.2, h.2⟩
        simp only [ha] at h1
        cases hb : callsSing body sa with
        | mk ob sb =>
          have h2 := $single body sa ⟨h.1.1, h1.2⟩
          simp only [hb] at h2
          simp only [callsSing, ha, hb]
          cases loc with
          | none => simpa [$one:ident] using And.intro (And.intro h2.1 h1.1) h2.2
          | some loc =>
            cases hl : (sptLookup loc sb.1).isSome <;> cases hp : ClosLang.pure body <;>
              simp_all [$one:ident, $app:ident, $all:ident,
                ($pick (everyFn_variables oa.length 2 BackendCommon.Tra.none)), h1.1, h2.1, h2.2]
    | fn name loc vs arity body =>
      simp only [$one:ident] at h
      let fresh := insertEachSource (loc.getD 0) 1 $state
      have haux : $all:ident (fresh.2.map (fun p => p.2.2)) := by
        simpa [fresh, insertEach_snd] using h.2
      cases hf : callsSing body fresh with
      | mk out st =>
        have ih := $single body fresh ⟨h.1.2, haux⟩
        simp only [hf] at ih
        dsimp [fresh] at hf
        simp only [callsSing, hf]
        split
        · simp [$one:ident, $all:ident,
            ($pick (everyFn_variables arity 1 BackendCommon.Tra.none)), h.1.1, ih.1, ih.2]
        · cases hr : callsSing body $state with
          | mk out st =>
            have ih := $single body $state ⟨h.1.2, h.2⟩
            simp only [hr] at ih
            simpa [hr, $one:ident, h.1.1] using ih
    | letrec names loc vs $fns body =>
      simp only [$one:ident, $funs:ident] at h
      let fresh := insertEachSource (loc.getD 0) ($fns).length $state
      have haux : $all:ident (fresh.2.map (fun p => p.2.2)) := by
        simpa [fresh, insertEach_snd] using h.2
      cases hf : callsSingList (($fns).map Prod.snd) fresh with
      | mk bodies st =>
        have ihF := $many (($fns).map Prod.snd) fresh ⟨h.1.2.1, haux⟩
        simp only [hf] at ihF
        have hlen : bodies.length = ($fns).length := by
          have len := callsSingList_length (($fns).map Prod.snd) fresh
          simpa [hf] using len
        have hzip : ((($fns).map Prod.fst).zip bodies).map Prod.snd = bodies := by
          simp [List.map_snd_zip, hlen]
        dsimp [fresh] at hf
        simp only [callsSing, hf]
        split
        · have hcode : $all:ident
              ((codeListSource (loc.getD 0) ((($fns).map Prod.fst).zip bodies) st).2.map
                (fun p => p.2.2)) := by
            rw [($pick (everyFn_codeList _ _ _)), hzip]
            exact ⟨ihF.1, ihF.2⟩
          cases hb : callsSing body
              (codeListSource (loc.getD 0) ((($fns).map Prod.fst).zip bodies) st) with
          | mk out final =>
            have ihB := $single body _ ⟨h.1.2.2, hcode⟩
            simp only [hb] at ihB
            have stubs := ($pick (everyFn_callsList $fns (loc.getD 0) 1 BackendCommon.Tra.none))
            simp [$one:ident, $funs:ident, h.1.1, stubs, ihB.1, ihB.2]
        · cases hg : callsSingList (($fns).map Prod.snd) $state with
          | mk bodies st =>
            have ihG := $many (($fns).map Prod.snd) $state ⟨h.1.2.1, h.2⟩
            simp only [hg] at ihG
            have hlen : bodies.length = ($fns).length := by
              have len := callsSingList_length (($fns).map Prod.snd) $state
              simpa [hg] using len
            have hzip : ((($fns).map Prod.fst).zip bodies).map Prod.snd = bodies := by
              simp [List.map_snd_zip, hlen]
            cases hb : callsSing body st with
            | mk out final =>
              have ihB := $single body st ⟨h.1.2.2, ihG.2⟩
              simp only [hb] at ihB
              simp [$one:ident, $funs:ident,
                hzip, h.1.1, ihG.1, ihB.1, ihB.2]
  ))

local macro "preserveAnnotMany " exps:ident state:ident single:ident many:ident all:ident : tactic =>
  `(tactic| (
    intro h
    cases ($exps) with
    | nil => simpa [callsSingList, $all:ident] using h.2
    | cons e $exps =>
      simp only [$all:ident] at h
      cases he : callsSing e $state with
      | mk out mid =>
        cases hs : callsSingList $exps mid with
        | mk outs final =>
          have h1 := $single e $state ⟨h.1.1, h.2⟩
          have h2 := $many $exps mid ⟨h.1.2, by simpa [he] using h1.2⟩
          simpa [callsSingList, he, hs, $all:ident] using
            And.intro (And.intro (by simpa [he] using h1.1) (by simpa [hs] using h2.1))
              (by simpa [hs] using h2.2)
  ))

mutual
private theorem callsSing_locationSome (e : Exp) (s : State) :
    (fnLocationSomeExp e ∧ everyFnLocationSome (s.2.map (fun p => p.2.2))) →
    fnLocationSomeExp (callsSing e s).1 ∧
      everyFnLocationSome ((callsSing e s).2.2.map (fun p => p.2.2)) := by
  preserveAnnotSingle e s callsSing_locationSome callsSingList_locationSome
    fnLocationSomeExp everyFnLocationSome fnLocationSomeFuns_eq_map locationSome_append And.left fns
termination_by sizeOf e
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  all_goals try have bound := sizeOf_map_snd_le fns
  all_goals omega

private theorem callsSingList_locationSome (es : List Exp) (s : State) :
    (everyFnLocationSome es ∧ everyFnLocationSome (s.2.map (fun p => p.2.2))) →
    everyFnLocationSome (callsSingList es s).1 ∧
      everyFnLocationSome ((callsSingList es s).2.2.map (fun p => p.2.2)) := by
  preserveAnnotMany es s callsSing_locationSome callsSingList_locationSome everyFnLocationSome
termination_by sizeOf es
decreasing_by all_goals subst_vars; all_goals simp_wf <;> omega
end

/-- Direct-call conversion preserves function locations in the output and
    in the accumulated auxiliary code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_preserves_every_Fn_SOME"]
theorem calls_preserves_everyFnLocationSome (xs : List Exp) (g0 : State)
    (ys : List Exp) (g : State) (run : calls xs g0 = (ys, g))
    (h : everyFnLocationSome xs ∧ everyFnLocationSome (g0.2.map (fun p => p.2.2))) :
    everyFnLocationSome ys ∧ everyFnLocationSome (g.2.map (fun p => p.2.2)) := by
  have ih := callsSingList_locationSome xs g0 h
  change callsSingList xs g0 = (ys, g) at run
  simpa [run] using ih

mutual
private theorem callsSing_varsNone (e : Exp) (s : State) :
    (fnVarsNoneExp e ∧ everyFnVarsNone (s.2.map (fun p => p.2.2))) →
    fnVarsNoneExp (callsSing e s).1 ∧
      everyFnVarsNone ((callsSing e s).2.2.map (fun p => p.2.2)) := by
  preserveAnnotSingle e s callsSing_varsNone callsSingList_varsNone
    fnVarsNoneExp everyFnVarsNone fnVarsNoneFuns_eq_map varsNone_append And.right fns
termination_by sizeOf e
decreasing_by
  all_goals subst_vars
  all_goals simp_wf
  all_goals try omega
  all_goals try have bound := sizeOf_map_snd_le fns
  all_goals omega

private theorem callsSingList_varsNone (es : List Exp) (s : State) :
    (everyFnVarsNone es ∧ everyFnVarsNone (s.2.map (fun p => p.2.2))) →
    everyFnVarsNone (callsSingList es s).1 ∧
      everyFnVarsNone ((callsSingList es s).2.2.map (fun p => p.2.2)) := by
  preserveAnnotMany es s callsSing_varsNone callsSingList_varsNone everyFnVarsNone
termination_by sizeOf es
decreasing_by all_goals subst_vars; all_goals simp_wf <;> omega
end

/-- Direct-call conversion preserves absent function-variable annotations in the output and
    in the accumulated auxiliary code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_preserves_every_Fn_vs_NONE"]
theorem calls_preserves_everyFnVarsNone (xs : List Exp) (g0 : State)
    (ys : List Exp) (g : State) (run : calls xs g0 = (ys, g))
    (h : everyFnVarsNone xs ∧ everyFnVarsNone (g0.2.map (fun p => p.2.2))) :
    everyFnVarsNone ys ∧ everyFnVarsNone (g.2.map (fun p => p.2.2)) := by
  have ih := callsSingList_varsNone xs g0 h
  change callsSingList xs g0 = (ys, g) at run
  simpa [run] using ih

private theorem locations_flatMap (xs : List Exp) :
    codeLocations xs = xs.flatMap codeLocationsExp := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [codeLocations, ih]

private theorem locations_perm {xs ys : List Exp} (h : xs.Perm ys) :
    (codeLocations xs).Perm (codeLocations ys) := by
  simp only [locations_flatMap]
  exact h.flatMap (fun _ _ => List.Perm.refl _)

private theorem codeLocations_codeList_perm {A C : Type} (ls : List (A × Exp))
    (n : Nat) (rest : C × List (Nat × A × Exp)) :
    (codeLocations ((codeListSource n ls rest).2.map (fun t => t.2.2))).Perm
      (codeLocations (rest.2.map (fun t => t.2.2) ++ ls.map Prod.snd)) := by
  rw [codeList_bodies, codeLocations_append, codeLocations_append]
  exact ((locations_perm (List.reverse_perm (ls.map Prod.snd))).append_right _).trans
    List.perm_append_comm

/-- Moving the bodies into the auxiliary code list preserves location
distinctness, including when the state and function metadata are polymorphic. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "code_locs_code_list_ALL_DISTINCT"]
theorem codeLocations_codeList_allDistinct {A C : Type} (ls : List (A × Exp))
    (n : Nat) (rest : C × List (Nat × A × Exp)) :
    (codeLocations ((codeListSource n ls rest).2.map (fun t => t.2.2))).Nodup ↔
      (codeLocations (rest.2.map (fun t => t.2.2) ++ ls.map Prod.snd)).Nodup := by
  exact (codeLocations_codeList_perm ls n rest).nodup_iff

private def cntExp (k : Nat) (e : Exp) := (codeLocationsExp e).count k
private def cntList (k : Nat) (es : List Exp) := (codeLocations es).count k
private def cntAux (k : Nat) (s : State) := (codeLocations (s.2.map (fun t => t.2.2))).count k

mutual
private theorem countExpr (e : Exp) (s : State) (k : Nat) :
    cntExp k (callsSing e s).1 + cntAux k (callsSing e s).2 ≤ cntExp k e + cntAux k s := by
  cases e with
  | var tr v => simp [callsSing, cntExp, codeLocationsExp]
  | raise tr body =>
    have h := countExpr body s k
    cases hr : callsSing body s with
    | mk out st => simpa [callsSing, hr, cntExp, codeLocationsExp] using h
  | tick tr body =>
    have h := countExpr body s k
    cases hr : callsSing body s with
    | mk out st => simpa [callsSing, hr, cntExp, codeLocationsExp] using h
  | ifThenElse tr a b c =>
    cases ha : callsSing a s with
    | mk oa sa =>
      cases hb : callsSing b sa with
      | mk ob sb =>
        cases hc : callsSing c sb with
        | mk oc sc =>
          have h1 := countExpr a s k
          have h2 := countExpr b sa k
          have h3 := countExpr c sb k
          simp only [ha] at h1
          simp only [hb] at h2
          simp only [hc] at h3
          simp only [callsSing, ha, hb, hc, cntExp, codeLocationsExp, List.count_append] at *
          omega
  | «let» tr args body =>
    cases ha : callsSingList args s with
    | mk oa sa =>
      cases hb : callsSing body sa with
      | mk ob sb =>
        have h1 := countList args s k
        have h2 := countExpr body sa k
        simp only [ha] at h1
        simp only [hb] at h2
        simp only [callsSing, ha, hb, cntExp, cntList, codeLocationsExp, List.count_append] at *
        omega
  | handle tr body handler =>
    cases ha : callsSing body s with
    | mk oa sa =>
      cases hb : callsSing handler sa with
      | mk ob sb =>
        have h1 := countExpr body s k
        have h2 := countExpr handler sa k
        simp only [ha] at h1
        simp only [hb] at h2
        simp only [callsSing, ha, hb, cntExp, codeLocationsExp, List.count_append] at *
        omega
  | call tr ticks dest args =>
    have h := countList args s k
    cases hr : callsSingList args s with
    | mk out st => simpa [callsSing, hr, cntExp, cntList, codeLocationsExp] using h
  | op tr op args =>
    have h := countList args s k
    cases hr : callsSingList args s with
    | mk out st => simpa [callsSing, hr, cntExp, cntList, codeLocationsExp] using h
  | app tr loc body args =>
    cases ha : callsSingList args s with
    | mk oa sa =>
      cases hb : callsSing body sa with
      | mk ob sb =>
        have h1 := countList args s k
        have h2 := countExpr body sa k
        simp only [ha] at h1
        simp only [hb] at h2
        simp only [callsSing, ha, hb]
        cases loc with
        | none =>
          simp only [cntExp, cntList, codeLocationsExp, List.count_append] at *
          omega
        | some loc =>
          cases hl : (sptLookup loc sb.1).isSome <;> cases hp : ClosLang.pure body <;>
            simp [hl, hp, cntExp, cntList, codeLocationsExp, codeLocations_append, codeLocations,
              locations_variables, List.count_append] at * <;> omega
  | fn name loc vs arity body =>
    let fresh := insertEachSource (loc.getD 0) 1 s
    cases hf : callsSing body fresh with
    | mk out st =>
      have ih := countExpr body fresh k
      simp only [hf] at ih
      have same : cntAux k fresh = cntAux k s := by
        cases s; rfl
      rw [same] at ih
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · simp only [cntExp, cntAux, codeLocationsExp, codeLocations, List.map_cons,
          List.count_append, locations_variables, List.count_nil] at *
        omega
      · have ih := countExpr body s k
        cases hr : callsSing body s with
        | mk out st =>
          simp only [hr] at ih ⊢
          simp only [cntExp, codeLocationsExp, List.count_append] at *
          omega
  | letrec names loc vs fns body =>
    let fresh := insertEachSource (loc.getD 0) fns.length s
    cases hf : callsSingList (fns.map Prod.snd) fresh with
    | mk bodies st =>
      have ihF := countList (fns.map Prod.snd) fresh k
      simp only [hf] at ihF
      have same : cntAux k fresh = cntAux k s := by
        simp [cntAux, fresh, insertEach_snd]
      rw [same] at ihF
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · have hlen : bodies.length = fns.length := by
          have h := callsSingList_length (fns.map Prod.snd) fresh
          simpa [hf, fresh] using h
        have hzip : ((fns.map Prod.fst).zip bodies).map Prod.snd = bodies := by
          simp [List.map_snd_zip, hlen]
        have cntCode :
            cntAux k (codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) st) =
              cntAux k st + cntList k bodies := by
          simp only [cntAux, cntList]
          rw [(codeLocations_codeList_perm ((fns.map Prod.fst).zip bodies) (loc.getD 0) st).count_eq k,
            codeLocations_append, List.count_append, hzip]
        have ihBody := countExpr body
          (codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) st) k
        cases hbody : callsSing body
          (codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) st) with
        | mk out final =>
          simp only [hbody, cntCode] at ihBody ⊢
          simp only [cntExp, cntList, codeLocationsExp, codeLocationsFuns_map,
            locations_callsList, length_callsList, List.count_nil, List.count_append,
            Nat.zero_add] at *
          omega
      · cases hg : callsSingList (fns.map Prod.snd) s with
        | mk bodies st =>
          have ihG := countList (fns.map Prod.snd) s k
          simp only [hg] at ihG ⊢
          have hlen : bodies.length = fns.length := by
            have h := callsSingList_length (fns.map Prod.snd) s
            simpa [hg] using h
          have hzip : ((fns.map Prod.fst).zip bodies).map Prod.snd = bodies := by
            simp [List.map_snd_zip, hlen]
          have ihBody := countExpr body st k
          cases hb : callsSing body st with
          | mk out final =>
            simp only [hb] at ihBody ⊢
            simp only [cntExp, cntList, codeLocationsExp, codeLocationsFuns_map,
              hzip, List.length_zip, List.length_map, hlen, min_self, List.count_append] at *
            omega
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have bound := sizeOf_map_snd_le fns
  all_goals omega

private theorem countList (es : List Exp) (s : State) (k : Nat) :
    cntList k (callsSingList es s).1 + cntAux k (callsSingList es s).2 ≤ cntList k es + cntAux k s := by
  cases es with
  | nil => simp [callsSingList, cntList, codeLocations]
  | cons e es =>
    cases he : callsSing e s with
    | mk out mid =>
      cases hs : callsSingList es mid with
      | mk outs final =>
        have h1 := countExpr e s k
        have h2 := countList es mid k
        simp only [he] at h1
        simp only [hs] at h2
        simp only [callsSingList, he, hs, cntList, cntExp, codeLocations,
          List.count_append] at *
        omega
termination_by sizeOf es
decreasing_by all_goals simp_wf <;> omega
end

/-- Direct-call conversion preserves the multiplicity bound for code locations.
This auxiliary invariant supports the incremental compiler address proof; it
is not a separate HOL declaration. -/
theorem callsLocations_subperm (xs : List Exp) (initial : State)
    (ys : List Exp) (final : State) (run : calls xs initial = (ys, final)) :
    List.Subperm (codeLocations ys ++ codeLocations (final.2.map (fun t => t.2.2)))
      (codeLocations xs ++ codeLocations (initial.2.map (fun t => t.2.2))) := by
  apply List.subperm_iff_count.mpr
  intro k
  have ih := countList xs initial k
  change callsSingList xs initial = (ys, final) at run
  rw [run] at ih
  simpa [cntList, cntAux, List.count_append] using ih

/-- Direct-call conversion introduces no closure-code locations: every
location in the result or its auxiliary code comes from the input or the
initial auxiliary code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_code_locs_MEM"]
theorem calls_codeLocations_mem (xs : List Exp) (initial : State) (ys : List Exp)
    (final : State) (run : calls xs initial = (ys, final)) (x : Nat)
    (member : x ∈ codeLocations ys ∨
      x ∈ codeLocations (final.2.map (fun t => t.2.2))) :
    x ∈ codeLocations xs ∨
      x ∈ codeLocations (initial.2.map (fun t => t.2.2)) := by
  exact List.mem_append.mp ((callsLocations_subperm xs initial ys final run).subset
    (List.mem_append.mpr member))

/-- Direct-call conversion preserves distinctness of input and auxiliary code locations. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_code_locs_ALL_DISTINCT"]
theorem calls_codeLocations_allDistinct (xs : List Exp) (initial : State)
    (ys : List Exp) (final : State) (run : calls xs initial = (ys, final))
    (distinct : (codeLocations xs ++
      codeLocations (initial.2.map (fun t => t.2.2))).Nodup) :
    (codeLocations ys ++ codeLocations (final.2.map (fun t => t.2.2))).Nodup := by
  have bound := callsLocations_subperm xs initial ys final run
  obtain ⟨middle, perm, sub⟩ := List.subperm_iff.mp bound
  exact sub.nodup (perm.nodup_iff.mpr distinct)

end Flapjack.Compiler.Backend.ClosCall
