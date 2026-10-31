import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateApp

/-! Installed-code facts for known-location closure calls. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The code pointer in a related recursive closure is its source location,
shifted by the stub count and the recursive function index. -/
theorem clRel_recclosure_direct_address {maxApp : Nat} {fs : Nat → Prop}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {captured : List ClosSem.Value} {fields : List BvlSem.Value} {ptr index arity : Nat}
    {functions : List (Nat × ClosLang.Exp)} {body : ClosLang.Exp} {target : BvlSem.Value}
    (related : clRel maxApp fs refs code (captured, fields) (.recclosure (some ptr) [] captured functions index) target)
    (found : functions[index]? = some (arity, body)) :
    ∃ payload, target = .block 30
      (.codePtr ((ptr + 2 * index) + numStubs maxApp) :: .number (Int.ofNat (arity - 1)) :: payload) := by
  cases related with
  | singletonRec bound positive loc vars compiled installed lookup =>
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    exact ⟨fields, by simp⟩
  | @mutualRec exps entries ps rs loc r env ys k expsEq psEq positions values fresh stored many indexBound locations vars installed =>
    have entryBound : index < entries.length := by simpa [expsEq] using indexBound
    have entryEq : (entries[index]'entryBound).1 = (arity, body) := by
      have h : functions[index]? = some (arity, body) := found
      rw [expsEq, List.getElem?_map, List.getElem?_eq_getElem entryBound] at h
      simpa using h
    have entryAddress : (entries[index]'entryBound).2 = ptr + numStubs maxApp + 2 * index := by
      have actual : ps[index]? = some (entries[index]'entryBound).2 := by
        simp [psEq, List.getElem?_map, List.getElem?_eq_getElem entryBound]
      have expected : ps[index]? = some (ptr + numStubs maxApp + 2 * index) := by
        simp [positions, entryBound]
      exact Option.some.inj (actual.symm.trans expected)
    subst rs
    rw [Flapjack.holEl_eq_getElem index _ (by simpa using entryBound)]
    simp only [List.getElem_map]
    cases h : entries[index]'entryBound with
    | mk pair label =>
      have pairEq : pair = (arity, body) := by simpa [h] using entryEq
      have labelEq : label = (ptr + 2 * index) + numStubs maxApp := by
        have := entryAddress
        simp only [h] at this
        omega
      subst pair
      subst label
      exact ⟨_, rfl⟩

/-- A related recursive closure resolves its known-location target call with
one extra argument for the closure block itself. -/
theorem vRel_recclosure_direct_findCode {maxApp ptr index arity : Nat}
    {f : HolFiniteMapExact Nat Nat} {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {captured : List ClosSem.Value}
    {functions : List (Nat × ClosLang.Exp)} {sourceBody : ClosLang.Exp} {target : BvlSem.Value}
    {sourceArgs : List ClosSem.Value} {targetArgs : List BvlSem.Value}
    (related : vRel maxApp f refs code (.recclosure (some ptr) [] captured functions index) target)
    (found : functions[index]? = some (arity, sourceBody))
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) :
    ∃ entry, BvlSem.findCode (some ((ptr + 2 * index) + numStubs maxApp))
      (targetArgs ++ [target]) code = some (targetArgs ++ [target], entry) := by
  obtain ⟨fields, _, closure⟩ := vRel_recclosure_original related
  obtain ⟨expectedPayload, expectedShape⟩ := clRel_recclosure_direct_address closure found
  obtain ⟨address, payload, entry, actualShape, lookup⟩ := clRel_recclosure_target_code closure found
  have addressEq : address = (ptr + 2 * index) + numStubs maxApp := by
    have equal := actualShape.symm.trans expectedShape
    simp only [BvlSem.Value.block.injEq, List.cons.injEq, BvlSem.Value.codePtr.injEq] at equal
    exact equal.2.1
  subst address
  have length : targetArgs.length = arity := argsRel.length_eq.symm.trans arityMatch
  exact ⟨entry, by simp [BvlSem.findCode, lookup, length]⟩

/-- A related ordinary closure resolves its known-location target call with
one extra argument for the closure block itself. -/
theorem vRel_ordinary_direct_findCode {maxApp ptr arity : Nat}
    {f : HolFiniteMapExact Nat Nat} {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)}
    {code : Spt (Nat × Bvl.Exp)} {captured : List ClosSem.Value} {sourceBody : ClosLang.Exp}
    {target : BvlSem.Value} {sourceArgs : List ClosSem.Value} {targetArgs : List BvlSem.Value}
    (related : vRel maxApp f refs code (.closure (some ptr) [] captured arity sourceBody) target)
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (arityMatch : sourceArgs.length = arity) :
    ∃ entry, BvlSem.findCode (some (ptr + numStubs maxApp)) (targetArgs ++ [target]) code =
      some (targetArgs ++ [target], entry) := by
  obtain ⟨fields, _, closure⟩ := vRel_ordinary_closure related
  cases closure with
  | closure bound positive locations vars compiled installed lookup =>
    have length : targetArgs.length = arity := argsRel.length_eq.symm.trans arityMatch
    have has : ∃ entry, sptLookup (ptr + numStubs maxApp) code = some (arity + 1, entry) := ⟨_, lookup⟩
    obtain ⟨entry, entryLookup⟩ := has
    exact ⟨entry, by simp [BvlSem.findCode, entryLookup, length]⟩

/-- Whenever a related closure accepts a known-location application, the
compiled direct call resolves to installed code with the right arity. -/
theorem vRel_direct_findCode {maxApp address : Nat} {f : HolFiniteMapExact Nat Nat}
    {refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)} {code : Spt (Nat × Bvl.Exp)}
    {function : ClosSem.Value} {target : BvlSem.Value} {sourceArgs : List ClosSem.Value}
    {targetArgs : List BvlSem.Value} {application : ClosSem.AppKind}
    (related : vRel maxApp f refs code function target)
    (argsRel : List.Forall₂ (vRel maxApp f refs code) sourceArgs targetArgs)
    (found : ClosSem.destClosure maxApp (some address) function sourceArgs = some application) :
    ∃ entry, BvlSem.findCode (some (address + numStubs maxApp)) (targetArgs ++ [target]) code =
      some (targetArgs ++ [target], entry) := by
  cases function <;> simp only [ClosSem.destClosure] at found <;> try contradiction
  case closure location supplied captured arity body =>
    have shape := ClosSem.destClosure_direct_closure maxApp address location supplied captured sourceArgs arity body application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨rfl, rfl, arityEq, _, _⟩ := shape
    exact vRel_ordinary_direct_findCode related argsRel arityEq.symm
  case recclosure location supplied captured functions index =>
    have shape := ClosSem.destClosure_direct_recclosure maxApp address location supplied captured sourceArgs functions index application (by
      simpa only [ClosSem.destClosure] using found)
    obtain ⟨arity, body, selected, locationEq, rfl, arityEq, _, _⟩ := shape
    cases location with
    | none => simp at locationEq
    | some ptr =>
      simp only [Option.map, Option.some.injEq] at locationEq
      subst address
      have call := vRel_recclosure_direct_findCode related selected argsRel arityEq.symm
      simpa [Nat.add_comm] using call

end Flapjack.Compiler.Backend.ClosToBvl
