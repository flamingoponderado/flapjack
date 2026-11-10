module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeList
public import Flapjack.Compiler.Backend.ClosCall.Proofs.InsertDomain
public import Flapjack.Compiler.Backend.ClosCall.Compile
@[expose] public section

/-! Direct-call traversal is independent of the existing code suffix. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang

private def Paired (s t u v : State) : Prop :=
  u.1 = v.1 ∧ ∃ entries, u.2 = entries ++ s.2 ∧ v.2 = entries ++ t.2

private theorem pairedRefl (s t : State) (same : s.1 = t.1) : Paired s t s t :=
  ⟨same, [], by simp, by simp⟩

private theorem pairedTrans {s t u v x y : State} (h : Paired s t u v)
    (h' : Paired u v x y) : Paired s t x y := by
  obtain ⟨_, p, left, right⟩ := h
  obtain ⟨same, q, left', right'⟩ := h'
  refine ⟨same, q ++ p, ?_, ?_⟩
  · rw [left', left, List.append_assoc]
  · rw [right', right, List.append_assoc]

private theorem pairedInsert (s t : State) (same : s.1 = t.1) (loc count : Nat) :
    Paired s t (insertEachSource loc count s) (insertEachSource loc count t) := by
  refine ⟨insertEach_fst_same loc count s t same, [], ?_, ?_⟩ <;> simp [insertEach_snd]

private theorem pairedCode {A B C : Type} (loc : Nat) (fns : List (A × B))
    (s t : C × List (Nat × A × B)) (same : s.1 = t.1) :
    (codeListSource loc fns s).1 = (codeListSource loc fns t).1 ∧
    ∃ entries, (codeListSource loc fns s).2 = entries ++ s.2 ∧
      (codeListSource loc fns t).2 = entries ++ t.2 := by
  refine ⟨by simpa [codeListSource_fst] using same, ?_⟩
  refine ⟨(((List.range fns.length).map (fun i => loc + 1 + 2 * i)).zip fns).reverse, ?_, ?_⟩
  · exact codeListSource_snd_zip loc fns s
  · exact codeListSource_snd_zip loc fns t

private theorem pairedCons {s t u v : State} (h : Paired s t u v) (entry : Nat × Nat × Exp) :
    Paired s t (u.1, entry :: u.2) (v.1, entry :: v.2) := by
  obtain ⟨same, entries, left, right⟩ := h
  refine ⟨same, entry :: entries, ?_, ?_⟩ <;> simp [left, right]

mutual
private theorem pairedExpr (e : Exp) (s t : State) (same : s.1 = t.1) :
    (callsSing e s).1 = (callsSing e t).1 ∧ Paired s t (callsSing e s).2 (callsSing e t).2 := by
  cases e with
  | var tr n => simpa [callsSing] using pairedRefl s t same
  | raise tr e | tick tr e =>
    have ih := pairedExpr e s t same
    cases a : callsSing e s with
    | mk out next =>
      cases b : callsSing e t with
      | mk out' next' =>
        simp only [a, b] at ih
        obtain ⟨rfl, related⟩ := ih
        simpa [callsSing, a, b] using related
  | call tr ticks dest xs | op tr dest xs =>
    have ih := pairedList xs s t same
    cases a : callsSingList xs s with
    | mk out next =>
      cases b : callsSingList xs t with
      | mk out' next' =>
        simp only [a, b] at ih
        obtain ⟨rfl, related⟩ := ih
        simpa [callsSing, a, b] using related
  | ifThenElse tr x y z =>
    have hx := pairedExpr x s t same
    cases a : callsSing x s with
    | mk out next =>
      cases b : callsSing x t with
      | mk out' next' =>
        simp only [a, b] at hx
        obtain ⟨rfl, first⟩ := hx
        have hy := pairedExpr y next next' first.1
        cases c : callsSing y next with
        | mk outy sy =>
          cases d : callsSing y next' with
          | mk outy' sy' =>
            simp only [c, d] at hy
            obtain ⟨rfl, second⟩ := hy
            have hz := pairedExpr z sy sy' second.1
            cases e : callsSing z sy with
            | mk outz sz =>
              cases f : callsSing z sy' with
              | mk outz' sz' =>
                simp only [e, f] at hz
                obtain ⟨rfl, third⟩ := hz
                simpa [callsSing, a, b, c, d, e, f] using pairedTrans (pairedTrans first second) third
  | «let» tr xs body =>
    have head := pairedList xs s t same
    cases a : callsSingList xs s with
    | mk out next =>
      cases b : callsSingList xs t with
      | mk out' next' =>
        simp only [a, b] at head
        obtain ⟨rfl, first⟩ := head
        have tail := pairedExpr body next next' first.1
        cases c : callsSing body next with
        | mk outs final =>
          cases d : callsSing body next' with
          | mk outs' final' =>
            simp only [c, d] at tail
            obtain ⟨rfl, rest⟩ := tail
            simpa [callsSing, a, b, c, d] using pairedTrans first rest
  | handle tr x y =>
    have head := pairedExpr x s t same
    cases a : callsSing x s with
    | mk out next =>
      cases b : callsSing x t with
      | mk out' next' =>
        simp only [a, b] at head
        obtain ⟨rfl, first⟩ := head
        have tail := pairedExpr y next next' first.1
        cases c : callsSing y next with
        | mk outs final =>
          cases d : callsSing y next' with
          | mk outs' final' =>
            simp only [c, d] at tail
            obtain ⟨rfl, rest⟩ := tail
            simpa [callsSing, a, b, c, d] using pairedTrans first rest
  | app tr loc x xs =>
    have hx := pairedList xs s t same
    cases a : callsSingList xs s with
    | mk out next =>
      cases b : callsSingList xs t with
      | mk out' next' =>
        simp only [a, b] at hx
        obtain ⟨rfl, first⟩ := hx
        have hy := pairedExpr x next next' first.1
        cases c : callsSing x next with
        | mk body final =>
          cases d : callsSing x next' with
          | mk body' final' =>
            simp only [c, d] at hy
            obtain ⟨rfl, second⟩ := hy
            have all := pairedTrans first second
            simp only [callsSing, a, b, c, d]
            cases loc with
            | none => simpa using all
            | some loc =>
              simp only
              rw [all.1]
              cases (sptLookup loc final'.1).isSome <;> cases ClosLang.pure x <;> simpa using all
  | fn name loc vars arity body =>
    let fresh := insertEachSource (loc.getD 0) 1 s
    let fresh' := insertEachSource (loc.getD 0) 1 t
    have inserted := pairedInsert s t same (loc.getD 0) 1
    have ih := pairedExpr body fresh fresh' inserted.1
    cases a : callsSing body fresh with
    | mk out next =>
      cases b : callsSing body fresh' with
      | mk out' next' =>
        simp only [a, b] at ih
        obtain ⟨rfl, related⟩ := ih
        dsimp [fresh] at a
        dsimp [fresh'] at b
        simp only [callsSing, a, b]
        cases closed (.fn name loc vars arity out) with
        | true =>
          simpa using pairedCons (pairedTrans inserted related) (loc.getD 0 + 1, arity, out)
        | false =>
          have fallback := pairedExpr body s t same
          cases c : callsSing body s with
          | mk retry final =>
            cases d : callsSing body t with
            | mk retry' final' =>
              simp only [c, d] at fallback
              obtain ⟨rfl, related⟩ := fallback
              simpa [c, d] using related
  | letrec names loc vars fns body =>
    let fresh := insertEachSource (loc.getD 0) fns.length s
    let fresh' := insertEachSource (loc.getD 0) fns.length t
    have inserted := pairedInsert s t same (loc.getD 0) fns.length
    have ih := pairedList (fns.map Prod.snd) fresh fresh' inserted.1
    cases a : callsSingList (fns.map Prod.snd) fresh with
    | mk bodies next =>
      cases b : callsSingList (fns.map Prod.snd) fresh' with
      | mk bodies' next' =>
        simp only [a, b] at ih
        obtain ⟨rfl, related⟩ := ih
        dsimp [fresh] at a
        dsimp [fresh'] at b
        simp only [callsSing, a, b]
        split
        · let code := codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) next
          let code' := codeListSource (loc.getD 0) ((fns.map Prod.fst).zip bodies) next'
          have added : Paired next next' code code' := pairedCode _ _ next next' related.1
          have prior := pairedTrans (pairedTrans inserted related) added
          have bodyRel := pairedExpr body code code' prior.1
          cases c : callsSing body code with
          | mk out final =>
            cases d : callsSing body code' with
            | mk out' final' =>
              simp only [c, d] at bodyRel
              obtain ⟨rfl, last⟩ := bodyRel
              simpa [code, code', c, d] using pairedTrans prior last
        · have fallback := pairedList (fns.map Prod.snd) s t same
          cases c : callsSingList (fns.map Prod.snd) s with
          | mk retry middle =>
            cases d : callsSingList (fns.map Prod.snd) t with
            | mk retry' middle' =>
              simp only [c, d] at fallback
              obtain ⟨rfl, first⟩ := fallback
              have bodyRel := pairedExpr body middle middle' first.1
              cases e : callsSing body middle with
              | mk out final =>
                cases f : callsSing body middle' with
                | mk out' final' =>
                  simp only [e, f] at bodyRel
                  obtain ⟨rfl, last⟩ := bodyRel
                  simpa [c, d, e, f] using pairedTrans first last
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals have bound := sizeOf_map_snd_le fns
  all_goals omega

private theorem pairedList (es : List Exp) (s t : State) (same : s.1 = t.1) :
    (callsSingList es s).1 = (callsSingList es t).1 ∧
      Paired s t (callsSingList es s).2 (callsSingList es t).2 := by
  cases es with
  | nil => simpa [callsSingList] using pairedRefl s t same
  | cons e es =>
    have head := pairedExpr e s t same
    cases a : callsSing e s with
    | mk out next =>
      cases b : callsSing e t with
      | mk out' next' =>
        simp only [a, b] at head
        obtain ⟨rfl, first⟩ := head
        have tail := pairedList es next next' first.1
        cases c : callsSingList es next with
        | mk outs final =>
          cases d : callsSingList es next' with
          | mk outs' final' =>
            simp only [c, d] at tail
            obtain ⟨rfl, rest⟩ := tail
            simpa [callsSingList, a, b, c, d] using pairedTrans first rest
termination_by sizeOf es
decreasing_by all_goals simp_wf <;> omega
end

/-- Replacing the initial code suffix preserves the transformed program and
the code generated by direct-call conversion. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "calls_replace_SND"]
theorem calls_replace_snd (xs : List Exp) (g0 : State) (ys : List Exp) (g : State)
    (g0' : State) (ls : List (Nat × Nat × Exp))
    (h : calls xs g0 = (ys, g) ∧ g0.1 = g0'.1 ∧ g.2 = ls ++ g0.2) :
    calls xs g0' = (ys, (g.1, ls ++ g0'.2)) := by
  have rel := pairedList xs g0 g0' h.2.1
  have run : callsSingList xs g0 = (ys, g) := h.1
  rw [run] at rel
  cases next : callsSingList xs g0' with
  | mk out state =>
    rw [next] at rel
    obtain ⟨outEq, first, entries, left, right⟩ := rel
    have eq : entries = ls := List.append_cancel_right (left.symm.trans h.2.2)
    subst entries
    change callsSingList xs g0' = _
    rw [next]
    apply Prod.ext
    · exact outEq.symm
    · apply Prod.ext
      · exact first.symm
      · exact right

end Flapjack.Compiler.Backend.ClosCall
