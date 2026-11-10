module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.LabelsOriginal

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

private def auxLoc (s : State) : Set Nat :=
  {x | x ∈ codeLocations (s.2.map (fun t => t.2.2))}
private def expLoc (e : Exp) : Set Nat := {x | x ∈ codeLocationsExp e}
private def listLoc (es : List Exp) : Set Nat := {x | x ∈ codeLocations es}

set_option maxHeartbeats 1000000 in
mutual
private theorem callsExpr_locs (e : Exp) (initial : State) :
    expLoc (callsSing e initial).1 ∪ auxLoc (callsSing e initial).2 ⊆
      expLoc e ∪ auxLoc initial := by
  cases e with
  | var tr v => simp [callsSing, expLoc, codeLocationsExp]
  | raise tr body =>
    have ih := callsExpr_locs body initial
    cases run : callsSing body initial with
    | mk out final =>
      simpa [callsSing, run, expLoc, codeLocationsExp] using ih
  | tick tr body =>
    have ih := callsExpr_locs body initial
    cases run : callsSing body initial with
    | mk out final =>
      simpa [callsSing, run, expLoc, codeLocationsExp] using ih
  | ifThenElse tr x y z =>
    cases hx : callsSing x initial with
    | mk ox sx =>
      cases hy : callsSing y sx with
      | mk oy sy =>
        cases hz : callsSing z sy with
        | mk oz sz =>
          have a := callsExpr_locs x initial
          have b := callsExpr_locs y sx
          have c := callsExpr_locs z sy
          simp only [hx] at a
          simp only [hy] at b
          simp only [hz] at c
          simp only [callsSing, hx, hy, hz]
          intro k hk
          have aa := @a k
          have bb := @b k
          have cc := @c k
          simp only [expLoc, auxLoc, Set.mem_union, Set.mem_ofPred_eq,
            codeLocationsExp, List.mem_append] at *
          aesop
  | «let» tr binds body =>
    cases hb : callsSingList binds initial with
    | mk out mid =>
      cases hx : callsSing body mid with
      | mk outB final =>
        have a := callsList_locs binds initial
        have b := callsExpr_locs body mid
        simp only [hb] at a
        simp only [hx] at b
        simp only [callsSing, hb, hx]
        intro k hk
        have aa := @a k
        have bb := @b k
        simp only [expLoc, listLoc, auxLoc, Set.mem_union, Set.mem_ofPred_eq,
          codeLocationsExp, List.mem_append] at *
        aesop
  | handle tr body handler =>
    cases hb : callsSing body initial with
    | mk out mid =>
      cases hh : callsSing handler mid with
      | mk outH final =>
        have a := callsExpr_locs body initial
        have b := callsExpr_locs handler mid
        simp only [hb] at a
        simp only [hh] at b
        simp only [callsSing, hb, hh]
        intro k hk
        have aa := @a k
        have bb := @b k
        simp only [expLoc, auxLoc, Set.mem_union, Set.mem_ofPred_eq,
          codeLocationsExp, List.mem_append] at *
        aesop
  | call tr ticks dest args =>
    have ih := callsList_locs args initial
    cases run : callsSingList args initial with
    | mk out final =>
      simpa [callsSing, run, expLoc, listLoc, codeLocationsExp] using ih
  | app tr loc body args =>
    cases ha : callsSingList args initial with
    | mk outA mid =>
      cases hb : callsSing body mid with
      | mk outB final =>
        have a := callsList_locs args initial
        have b := callsExpr_locs body mid
        simp only [ha] at a
        simp only [hb] at b
        simp only [callsSing, ha, hb]
        cases loc with
        | none =>
          intro k hk
          have aa := @a k
          have bb := @b k
          simp only [expLoc, listLoc, auxLoc, Set.mem_union, Set.mem_ofPred_eq,
            codeLocationsExp, List.mem_append] at *
          aesop
        | some loc =>
          split <;> (try split) <;> (try contradiction) <;> intro k hk <;>
            have aa := @a k <;> have bb := @b k <;>
            simp only [expLoc, listLoc, auxLoc, Set.mem_union, Set.mem_ofPred_eq,
              codeLocationsExp, List.mem_append] at * <;>
            aesop (add simp [codeLocationsExp, codeLocations, codeLocations_append, locations_variables])
  | fn name loc vs arity body =>
    let fresh := insertEachSource (loc.getD 0) 1 initial
    cases hr : callsSing body fresh with
    | mk outF stateF =>
      have ihF := callsExpr_locs body fresh
      simp only [hr] at ihF
      simp only [callsSing]
      split
      · have same : auxLoc fresh = auxLoc initial := by
          cases initial; rfl
        rw [same] at ihF
        intro k hk
        have hf := @ihF k
        simp only [expLoc, auxLoc, Set.mem_union, Set.mem_ofPred_eq,
          codeLocationsExp, codeLocations, List.map_cons, List.mem_append,
          List.mem_cons, locations_variables] at *
        aesop (add simp [codeLocationsExp, codeLocations, locations_variables])
      · have ih := callsExpr_locs body initial
        cases run : callsSing body initial with
        | mk out final =>
          simp only [run] at ih ⊢
          intro k hk
          have hh := @ih k
          simp only [expLoc, auxLoc, Set.mem_union, Set.mem_ofPred_eq,
            codeLocationsExp, List.mem_append, List.mem_singleton] at *
          aesop
  | letrec names loc vs fns body =>
    let fresh := insertEachSource (loc.getD 0) fns.length initial
    cases hf : callsSingList (fns.map Prod.snd) fresh with
    | mk bodies stateF =>
      have ihF := callsList_locs (fns.map Prod.snd) fresh
      simp only [hf] at ihF
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · have hlen : bodies.length = fns.length := by
          have h := callsSingList_length (fns.map Prod.snd) fresh
          simpa [hf, fresh] using h
        have hzip : ((fns.map Prod.fst).zip bodies).map Prod.snd = bodies := by
          simp [List.map_snd_zip, hlen]
        have haux : auxLoc fresh = auxLoc initial := by
          simp [auxLoc, fresh, insertEach_snd]
        rw [haux] at ihF
        have ihBody := callsExpr_locs body (codeListSource (loc.getD 0)
          ((fns.map Prod.fst).zip bodies) stateF)
        cases hbody : callsSing body (codeListSource (loc.getD 0)
          ((fns.map Prod.fst).zip bodies) stateF) with
        | mk out final =>
          simp only [hbody] at ihBody ⊢
          intro k hk
          have hF := @ihF k
          have hB := @ihBody k
          simp only [expLoc, listLoc, auxLoc, Set.mem_union, Set.mem_ofPred_eq,
            codeLocationsExp, codeLocationsFuns_map, locations_callsList,
            length_callsList, List.nil_append, List.mem_append, codeList_bodies, hzip,
            codeLocations_append, mem_codeLocations, List.mem_reverse] at *
          aesop
      · cases hgroup : callsSingList (fns.map Prod.snd) initial with
        | mk outs middle =>
          have ihGroup := callsList_locs (fns.map Prod.snd) initial
          simp only [hgroup] at ihGroup ⊢
          have hlen : outs.length = fns.length := by
            have h := callsSingList_length (fns.map Prod.snd) initial
            simpa [hgroup] using h
          have hzip : ((fns.map Prod.fst).zip outs).map Prod.snd = outs := by
            simp [List.map_snd_zip, hlen]
          have ihBody := callsExpr_locs body middle
          cases hbody : callsSing body middle with
          | mk out final =>
            simp only [hbody] at ihBody ⊢
            intro k hk
            have hG := @ihGroup k
            have hB := @ihBody k
            simp only [expLoc, listLoc, auxLoc, Set.mem_union, Set.mem_ofPred_eq,
              codeLocationsExp, codeLocationsFuns_map, hzip, List.length_zip,
              List.length_map, hlen, min_self, List.mem_append] at *
            aesop
  | op tr op args =>
    have ih := callsList_locs args initial
    cases run : callsSingList args initial with
    | mk out final =>
      simpa [callsSing, run, expLoc, listLoc, codeLocationsExp] using ih
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have bound := sizeOf_map_snd_le fns
  all_goals omega

private theorem callsList_locs (es : List Exp) (initial : State) :
    listLoc (callsSingList es initial).1 ∪ auxLoc (callsSingList es initial).2 ⊆
      listLoc es ∪ auxLoc initial := by
  cases es with
  | nil => simp [callsSingList, listLoc, codeLocations]
  | cons e es =>
    cases he : callsSing e initial with
    | mk out middle =>
      cases hs : callsSingList es middle with
      | mk outs final =>
        have a := callsExpr_locs e initial
        have b := callsList_locs es middle
        simp only [he] at a
        simp only [hs] at b
        simp only [callsSingList, he, hs]
        change ({k | k ∈ codeLocationsExp out ++ codeLocations outs} ∪ auxLoc final) ⊆ _
        simp only [List.mem_append] at *
        intro k hk
        have aa := @a k
        have bb := @b k
        simp only [expLoc, listLoc, auxLoc, Set.mem_union, Set.mem_ofPred_eq,
          codeLocations, List.mem_append] at *
        aesop
termination_by sizeOf es
decreasing_by all_goals simp_wf <;> omega
end

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
  have invariant := callsList_locs xs initial
  change callsSingList xs initial = (ys, final) at run
  rw [run] at invariant
  exact invariant member

end Flapjack.Compiler.Backend.ClosCall
