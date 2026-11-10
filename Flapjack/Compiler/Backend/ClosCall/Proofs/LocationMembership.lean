module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelsOriginal
import Mathlib.Data.List.Perm.Subperm

@[expose] public section

/-! Original direct-call location membership invariant. -/

namespace Flapjack.Compiler.Backend.ClosCall
open ClosLang ClosProps

private theorem sizeOf_map_snd_le (xs : List (Nat × Exp)) :
    sizeOf (xs.map Prod.snd) ≤ sizeOf xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    cases x
    simp_wf
    omega

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

private theorem insertEach_snd (loc count : Nat) (state : State) :
    (insertEachSource loc count state).2 = state.2 := by
  induction count generalizing loc state with
  | zero => rfl
  | succ count ih =>
    cases state with
    | mk known code => simpa [insertEachSource] using ih (loc + 2) (sptInsert loc () known, code)

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

private theorem callsLocations_subperm (xs : List Exp) (initial : State)
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
