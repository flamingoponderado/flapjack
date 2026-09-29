import Flapjack.Pancake.CrepToLoop.Proofs.CodeRel2

/-!
# Call-entry projection from exact `code_rel2`

This is Flapjack-specific proof infrastructure, not a HOL theorem port. It
projects the exact code-table fact needed by
`code_rel_evaluate_call_correct` from `code_rel2_def`, before any semantic
evaluation argument is used.
-/

namespace Flapjack

/-- From the exact `code_rel2` relation, a source code entry with no arguments
    and its known target label/zero arity determine the compiled target body at
    that label. This is only a code-table projection: it assumes neither the
    source nor target evaluator result and proves no semantic correctness by
    itself. HOL `code_rel2_def` (crep_to_loopProofScript.sml:3842-3845) supplies
    the finite-map `map2` to `code_rel_def`; the final target-body equation is
    the per-entry existential in `code_rel_def` (lines 76-88). -/
theorem crepToLoopCodeRel2CallEntryLookupExact {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact)
    (s_code : HolFiniteMapExact Flapjack.Basis.Pure.MlString.MlString
      (List Nat × CrepProgHOL width))
    (t_code : Spt (List Nat × HolLoopProg width))
    (start : Flapjack.Basis.Pure.MlString.MlString)
    (program : CrepProgHOL width) (label : Nat)
    (hRel : crepToLoopCodeRel2Exact ctxt s_code t_code)
    (hSource : s_code.lookup start = some ([], program))
    (hLabel : ctxt.funcs.lookup start = some (label, 0)) :
    sptLookup label t_code =
      some ([], ocompileHOLExact
        (ctxtFcExact ctxt.target ctxt.funcs [] [])
        (listToNumSetHOLExact []) (crepSimpProgHOL program)) := by
  change crepToLoopCodeRelExact ctxt
    (s_code.map2 (fun entry =>
      match entry with
      | (_, parameters, body) => (parameters, crepSimpProgHOL body)))
    t_code at hRel
  have hMapped :
      (s_code.map2 (fun entry =>
        match entry with
        | (_, parameters, body) => (parameters, crepSimpProgHOL body))).lookup
          start = some ([], crepSimpProgHOL program) := by
    simp [HolFiniteMapExact.lookup_map2, hSource]
  obtain ⟨targetLabel, arity, hContext, hArity, hCode⟩ :=
    hRel.2 start [] (crepSimpProgHOL program) hMapped
  have hPair : (targetLabel, arity) = (label, 0) := by
    apply Option.some.inj
    exact hContext.symm.trans hLabel
  have hLabelEq : targetLabel = label := congrArg Prod.fst hPair
  have hArityEq : arity = 0 := congrArg Prod.snd hPair
  subst targetLabel
  subst arity
  simpa [List.range_zero, listToNumSetHOLExact_nil] using hCode

end Flapjack
