module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.InsertDomain
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMembership
public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.Compiler.Backend.ClosCall.Compile
public import Mathlib.Data.Set.Defs

@[expose] public section

/-! Origins of direct-call compiler state locations. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

private def DomainBound (initial final : State) (locations : List Nat) : Prop :=
  ∀ k, sptDomain final.1 k → sptDomain initial.1 k ∨ k ∈ locations

private theorem domainBound_refl (s : State) (locations : List Nat) : DomainBound s s locations :=
  fun _ h => Or.inl h

private theorem domainBound_mono {s t : State} {small large : List Nat}
    (h : DomainBound s t small) (sub : ∀ k ∈ small, k ∈ large) : DomainBound s t large := by
  intro k found
  rcases h k found with old | new
  · exact Or.inl old
  · exact Or.inr (sub k new)

private theorem domainBound_append {s t u : State} {xs ys : List Nat}
    (h₁ : DomainBound s t xs) (h₂ : DomainBound t u ys) : DomainBound s u (xs ++ ys) := by
  intro k found
  rcases h₂ k found with intermediate | new
  · rcases h₁ k intermediate with old | new
    · exact Or.inl old
    · exact Or.inr (List.mem_append_left _ new)
  · exact Or.inr (List.mem_append_right _ new)

private theorem domainBound_insert (s : State) (loc n : Nat) :
    DomainBound s (insertEachSource loc n s) ((List.range n).map (fun i => loc + 2 * i)) := by
  intro k found
  rw [domain_insertEach] at found
  rcases found with generated | old
  · right
    simp only [Set.mem_ofPred_eq, List.mem_map] at generated ⊢
    obtain ⟨i, hi, eq⟩ := generated
    exact ⟨i, hi, by omega⟩
  · exact Or.inl old

mutual
private theorem domainBound_expr (e : Exp) (s : State) :
    DomainBound s (callsSing e s).2 (codeLocationsExp e) := by
  cases e with
  | var tr n => simpa [callsSing] using domainBound_refl s (codeLocationsExp (.var tr n))
  | raise tr e | tick tr e =>
    have ih := domainBound_expr e s
    cases run : callsSing e s with
    | mk out next => simpa [callsSing, run, codeLocationsExp] using ih
  | ifThenElse tr x y z =>
    cases hx : callsSing x s with
    | mk ox sx =>
      cases hy : callsSing y sx with
      | mk oy sy =>
        cases hz : callsSing z sy with
        | mk oz sz =>
          have h₁ := domainBound_expr x s
          have h₂ := domainBound_expr y sx
          have h₃ := domainBound_expr z sy
          simp only [hx] at h₁
          simp only [hy] at h₂
          simp only [hz] at h₃
          simpa [callsSing, hx, hy, hz, codeLocationsExp] using
            domainBound_append (domainBound_append h₁ h₂) h₃
  | «let» tr args body =>
    cases hx : callsSingList args s with
    | mk ox sx =>
      cases hy : callsSing body sx with
      | mk oy sy =>
        have h₁ := domainBound_list args s
        have h₂ := domainBound_expr body sx
        simp only [hx] at h₁
        simp only [hy] at h₂
        simpa [callsSing, hx, hy, codeLocationsExp] using domainBound_append h₁ h₂
  | handle tr x y =>
    cases hx : callsSing x s with
    | mk ox sx =>
      cases hy : callsSing y sx with
      | mk oy sy =>
        have h₁ := domainBound_expr x s
        have h₂ := domainBound_expr y sx
        simp only [hx] at h₁
        simp only [hy] at h₂
        simpa [callsSing, hx, hy, codeLocationsExp] using domainBound_append h₁ h₂
  | call tr ticks dest args | op tr dest args =>
    have ih := domainBound_list args s
    cases run : callsSingList args s with
    | mk out next => simpa [callsSing, run, codeLocationsExp] using ih
  | app tr loc body args =>
    cases hx : callsSingList args s with
    | mk ox sx =>
      cases hy : callsSing body sx with
      | mk oy sy =>
        have h₁ := domainBound_list args s
        have h₂ := domainBound_expr body sx
        simp only [hx] at h₁
        simp only [hy] at h₂
        have combined := domainBound_append h₁ h₂
        cases loc with
        | none =>
          simp only [callsSing, hx, hy]
          apply domainBound_mono combined
          simp [codeLocationsExp, List.mem_append, or_comm]
        | some loc =>
          simp only [callsSing, hx, hy]
          cases (sptLookup loc sy.1).isSome <;> cases ClosLang.pure body <;>
            simp only [Bool.false_eq_true, ↓reduceIte] <;>
            apply domainBound_mono combined <;>
            simp [codeLocationsExp, List.mem_append, or_comm]
  | fn name loc vars arity body =>
    let fresh := insertEachSource (loc.getD 0) 1 s
    cases hf : callsSing body fresh with
    | mk out st =>
      have ih := domainBound_expr body fresh
      simp only [hf] at ih
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · have combined := domainBound_append (domainBound_insert s (loc.getD 0) 1) ih
        apply domainBound_mono combined
        simp [codeLocationsExp, List.mem_append, or_comm]
      · have ih := domainBound_expr body s
        cases hr : callsSing body s with
        | mk out next =>
          simp only [hr] at ih ⊢
          apply domainBound_mono ih
          intro k member
          simp [codeLocationsExp, member]
  | letrec names loc vars fns body =>
    let fresh := insertEachSource (loc.getD 0) fns.length s
    cases hf : callsSingList (fns.map Prod.snd) fresh with
    | mk bodies st =>
      have ihF := domainBound_list (fns.map Prod.snd) fresh
      simp only [hf] at ihF
      dsimp [fresh] at hf
      simp only [callsSing, hf]
      split
      · let emitted := codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) st
        have emitBound : DomainBound st emitted [] := by
          simp [DomainBound, emitted, codeListSource_fst]
        have ihBody := domainBound_expr body emitted
        cases hb : callsSing body emitted with
        | mk out final =>
          simp only [hb] at ihBody
          change DomainBound s final _
          have all := domainBound_append
            (domainBound_append (domainBound_append (domainBound_insert s (loc.getD 0) fns.length) ihF)
              emitBound) ihBody
          apply domainBound_mono all
          simp [codeLocationsExp, codeLocationsFuns_map, List.mem_append, or_comm, or_left_comm, or_assoc]
      · cases hg : callsSingList (fns.map Prod.snd) s with
        | mk bodies st =>
          have ihG := domainBound_list (fns.map Prod.snd) s
          simp only [hg] at ihG ⊢
          cases hb : callsSing body st with
          | mk out final =>
            have ihBody := domainBound_expr body st
            simp only [hb] at ihBody ⊢
            apply domainBound_mono (domainBound_append ihG ihBody)
            simp only [codeLocationsExp, codeLocationsFuns_map, List.mem_append]
            aesop
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have bound := sizeOf_map_snd_le fns
  all_goals omega

private theorem domainBound_list (es : List Exp) (s : State) :
    DomainBound s (callsSingList es s).2 (codeLocations es) := by
  cases es with
  | nil => simpa [callsSingList] using domainBound_refl s (codeLocations [])
  | cons e es =>
    cases he : callsSing e s with
    | mk out mid =>
      cases hs : callsSingList es mid with
      | mk outs final =>
        have h₁ := domainBound_expr e s
        have h₂ := domainBound_list es mid
        simp only [he] at h₁
        simp only [hs] at h₂
        simpa [callsSingList, he, hs, codeLocations] using domainBound_append h₁ h₂
termination_by sizeOf es
decreasing_by all_goals simp_wf <;> omega
end

/-- A direct-call traversal adds only locations occurring in its input. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_domain_locs"]
theorem calls_domainLocations (xs : List Exp) (g : State) (ys : List Exp) (g2 : State)
    (h : calls xs g = (ys, g2)) :
    Set.Subset (sptDomain g2.1) (Set.union (sptDomain g.1) {x | x ∈ codeLocations xs}) := by
  have bound := domainBound_list xs g
  change callsSingList xs g = (ys, g2) at h
  rw [h] at bound
  exact bound

/-- A location in a disjoint input remains fresh after compiling the other input. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "NOT_IN_domain_FST_g"]
theorem calls_preservesFreshLocation (xs ys : List Exp) (initial : State)
    (out : List Exp) (final : State) (x : Nat)
    (distinct : (codeLocations xs ++ codeLocations ys).Nodup)
    (run : calls ys initial = (out, final))
    (_well : wellFormed initial) (member : x ∈ codeLocations xs)
    (fresh : ¬ sptDomain initial.1 x) : ¬ sptDomain final.1 x := by
  intro present
  have bound := calls_domainLocations ys initial out final run present
  rcases bound with old | new
  · exact fresh old
  · exact (List.nodup_append.mp distinct).2.2 x member x new rfl

end Flapjack.Compiler.Backend.ClosCall
