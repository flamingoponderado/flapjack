module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.AnnotationAddresses
public import Flapjack.Compiler.Backend.ClosCall.Proofs.LocationMembership
public import Flapjack.Compiler.Backend.ClosCall.Proofs.SyntaxOk
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationDistinct
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.LocationInvariants
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.VarsNone
import Mathlib.Data.List.Perm.Subperm

@[expose] public section

/-! Address preservation for conditional direct-call conversion. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open ClosLang ClosProps

/-- The direct-call compiler preserves the singleton result shape. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "HD_FST_calls"]
theorem head_calls_singleton (x : ClosLang.Exp) (y : ClosCall.State) :
    [Flapjack.holHd (ClosCall.calls [x] y).1] = (ClosCall.calls [x] y).1 := by
  rw [ClosCall.callsSing_eq.1 x y]
  cases ClosCall.callsSing x y
  simp [Flapjack.holHd]

/-- Numbering produces valid direct-call syntax from unannotated inputs. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "renumber_code_locs_list_csyntax_ok"]
theorem renumberList_callSyntaxOk (n : Nat) (es : List ClosLang.Exp) (k : Nat) (out : List ClosLang.Exp)
    (h : ClosNumber.renumberList n es = (k, out) ∧ everyFnVarsNone es) :
    ClosCall.syntaxOk out := by
  have locations := ClosNumber.renumberCodeLocs_everyFnSome.1 n es
  have vars := (ClosNumber.renumberCodeLocs_everyFnVarsNone.1 n es).2 h.2
  have distinct := (ClosNumber.renumberList_codeLocations_distinct n es).1
  simpa [ClosCall.syntaxOk, h.1] using And.intro locations (And.intro vars distinct)

/-- Direct-call compilation retains absent variable annotations in both outputs. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "calls_compile_csyntax_ok"]
theorem callsCompile_callSyntaxOk (enabled : Bool) (xs ys : List ClosLang.Exp) (g : NumSet)
    (aux : List (Nat × Nat × ClosLang.Exp)) (run : ClosCall.compile enabled xs = (ys, (g, aux)))
    (safe : ClosCall.syntaxOk xs) :
    everyFnVarsNone ys ∧ everyFnVarsNone (aux.map (fun p => p.2.2)) := by
  cases enabled with
  | false =>
    simp [ClosCall.compile] at run
    obtain ⟨rfl, _, rfl⟩ := run
    simpa [everyFnVarsNone] using safe.2.1
  | true =>
    apply ClosCall.calls_preserves_everyFnVarsNone xs (.ln, []) ys (g, aux)
      (by simpa [ClosCall.compile] using run)
    simpa [everyFnVarsNone] using safe.2.1

/-- Direct-call compilation preserves distinct code locations across both outputs. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "compile_code_locs_ALL_DISTINCT"]
theorem compile_codeLocations_allDistinct (enabled : Bool) (es xs : List ClosLang.Exp)
    (g : NumSet) (aux : List (Nat × Nat × ClosLang.Exp))
    (h : ClosCall.compile enabled es = (xs, (g, aux)) ∧ (codeLocations es).Nodup) :
    (codeLocations xs ++ codeLocations (aux.map (fun p => p.2.2))).Nodup := by
  cases enabled with
  | false =>
    simp [ClosCall.compile] at h
    obtain ⟨⟨rfl, _, rfl⟩, distinct⟩ := h
    simpa [codeLocations] using distinct
  | true =>
    apply ClosCall.calls_codeLocations_allDistinct es (.ln, []) xs (g, aux)
      (by simpa [ClosCall.compile] using h.1)
    simpa [codeLocations] using h.2
/-- Conditional direct-call conversion preserves absent variable annotations. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "every_Fn_vs_NONE_cond_call_compile_inc"]
theorem everyFnVarsNone_condCallCompileInc (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))
    (enabled : Bool) (known : NumSet) :
    (everyFnVarsNone program.1 →
      everyFnVarsNone (ClosCall.condCallCompileInc enabled known program).2.1) ∧
    (everyFnVarsNone program.1 ∧ everyFnVarsNone (program.2.map (fun p => p.2.2)) →
      everyFnVarsNone ((ClosCall.condCallCompileInc enabled known program).2.2.map (fun p => p.2.2))) := by
  cases enabled with
  | false => simp [ClosCall.condCallCompileInc]
  | true =>
    cases hrun : ClosCall.calls program.1 (known, []) with
    | mk output state =>
      have preserve := ClosCall.calls_preserves_everyFnVarsNone program.1 (known, []) output state hrun
      simp only [ClosCall.condCallCompileInc, ↓reduceIte,
        ClosCall.compileInc, hrun]
      constructor
      · intro h
        exact (preserve ⟨h, by simp [everyFnVarsNone]⟩).1
      · intro h
        exact (preserve ⟨h.1, by simp [everyFnVarsNone]⟩).2

/-- Optional direct-call conversion preserves locations in both the program
    and its auxiliary code. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "every_Fn_SOME_cond_call_compile_inc"]
theorem everyFnLocationSome_condCallCompileInc
    (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp)) (enabled : Bool) (known : NumSet) :
    (everyFnLocationSome program.1 →
      everyFnLocationSome (ClosCall.condCallCompileInc enabled known program).2.1) ∧
    (everyFnLocationSome program.1 ∧ everyFnLocationSome (program.2.map (fun p => p.2.2)) →
      everyFnLocationSome ((ClosCall.condCallCompileInc enabled known program).2.2.map
        (fun p => p.2.2))) := by
  obtain ⟨exps, code⟩ := program
  cases enabled with
  | false => simp [ClosCall.condCallCompileInc]
  | true =>
    cases run : ClosCall.calls exps (known, []) with
    | mk out final =>
      have preserve : everyFnLocationSome exps →
          everyFnLocationSome out ∧ everyFnLocationSome (final.2.map (fun p => p.2.2)) := by
        intro h
        apply ClosCall.calls_preserves_everyFnLocationSome exps (known, []) out final run
        simpa [everyFnLocationSome] using h
      simp only [ClosCall.condCallCompileInc, ↓reduceIte, ClosCall.compileInc, run]
      exact ⟨fun h => (preserve h).1, fun h => (preserve h.1).2⟩

private theorem calls_preserve_extract (xs : List ClosLang.Exp) (s : ClosCall.State)
    (extractable : canExtract xs) :
    extractedAddrs (ClosCall.calls xs s).1 = extractedAddrs xs ∧
      canExtract (ClosCall.calls xs s).1 := by
  obtain ⟨tr, n, rest, rfl⟩ := extractable
  cases run : ClosCall.callsSingList rest s with
  | mk out final =>
    have len := ClosCall.callsSingList_length rest s
    simp only [run] at len
    have empty : out = [] ↔ rest = [] := by
      constructor <;> intro h
      · subst out; cases rest <;> simp_all
      · subst rest; cases out <;> simp_all
    simp only [ClosCall.calls, ClosCall.callsSingList, ClosCall.callsSing, run]
    constructor
    · by_cases h : rest = []
      · have hout : out = [] := empty.mpr h
        simp [extractedAddrs, extractNameSource_eq_extractName, extractName, h, hout]
      · have hout : out ≠ [] := fun hh => h (empty.mp hh)
        simp [extractedAddrs, extractNameSource_eq_extractName, extractName, h, hout, len]
    · exact ⟨tr, n, out, rfl⟩

private theorem req_empty_sublist (exps : List ClosLang.Exp)
    (code : List (Nat × Nat × ClosLang.Exp)) :
    (reqCompileIncAddrs [] (exps, code)).Sublist
      (reqCompileIncAddrs [Nat.succ] (exps, code)) := by
  simp only [reqCompileIncAddrs, List.map_nil, List.flatten_nil, List.append_nil,
    List.map_cons, List.flatten_cons]
  apply List.sublist_append_left

/-- Conditional direct-call conversion preserves extractability and required
address distinctness, and introduces no required addresses. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "cond_call_compile_inc_req"]
theorem condCallCompileInc_req (program : List ClosLang.Exp × List (Nat × Nat × ClosLang.Exp))
    (enabled : Bool) (known : NumSet) :
    canExtract program.1 →
      ((reqCompileIncAddrs [Nat.succ] program).Nodup →
        (reqCompileIncAddrs [] (ClosCall.condCallCompileInc enabled known program).2).Nodup) ∧
      canExtract (ClosCall.condCallCompileInc enabled known program).2.1 ∧
      {x | x ∈ reqCompileIncAddrs [] (ClosCall.condCallCompileInc enabled known program).2} ⊆
        {x | x ∈ reqCompileIncAddrs [Nat.succ] program} := by
  obtain ⟨exps, code⟩ := program
  intro extractable
  cases enabled with
  | false =>
    have sub := req_empty_sublist exps code
    simpa only [ClosCall.condCallCompileInc, Bool.false_eq_true, ↓reduceIte] using
      (show ((reqCompileIncAddrs [Nat.succ] (exps, code)).Nodup →
        (reqCompileIncAddrs [] (exps, code)).Nodup) ∧ canExtract exps ∧
          {x | x ∈ reqCompileIncAddrs [] (exps, code)} ⊆
            {x | x ∈ reqCompileIncAddrs [Nat.succ] (exps, code)} from
        ⟨fun h => sub.nodup h, extractable, fun _ h => sub.subset h⟩)
  | true =>
    cases run : ClosCall.calls exps (known, []) with
    | mk out final =>
      have extract := calls_preserve_extract exps (known, []) extractable
      simp only [run] at extract
      simp only [ClosCall.condCallCompileInc, ↓reduceIte,
        ClosCall.compileInc, run]
      constructor
      · intro distinct
        have distinctOriginal := distinct
        simp only [reqCompileIncAddrs, List.map_nil, List.flatten_nil, List.map_cons,
          List.flatten_cons, List.append_nil, List.nodup_append] at distinct
        have locNodup : (codeLocations exps).Nodup := distinct.1.1.1.2.1
        have labelsNodup : (final.2.map Prod.fst).Nodup := by
          apply ClosCall.calls_allDistinct exps (known, []) out final
          refine ⟨run, ?_, locNodup, ?_⟩ <;> simp
        have labelsSubset : final.2.map Prod.fst ⊆ (codeLocations exps).map Nat.succ := by
          intro k hk
          have h := ClosCall.calls_addSucc_codeLocations exps (known, []) out final run hk
          simp only [List.map_nil, List.not_mem_nil, Set.mem_ofPred_eq,
            Set.mem_union, Set.mem_image, false_or] at h
          rcases h with ⟨x, hx, rfl⟩
          exact List.mem_map.mpr ⟨x, hx, rfl⟩
        have labelSub := labelsNodup.subperm labelsSubset
        have locSub := ClosCall.callsLocations_subperm exps (known, []) out final run
        simp only [List.map_nil, codeLocations, List.append_nil] at locSub
        have coreSub := locSub.append labelSub
        have swap :
            (codeLocations out ++ final.2.map Prod.fst ++
              codeLocations (final.2.map (fun t => t.2.2))).Perm
            ((codeLocations out ++ codeLocations (final.2.map (fun t => t.2.2))) ++
              final.2.map Prod.fst) := by
          simpa [List.append_assoc] using
            (List.perm_append_comm (l₁ := final.2.map Prod.fst)
              (l₂ := codeLocations (final.2.map (fun t => t.2.2)))).append_left (codeLocations out)
        have outputSub := (List.Subperm.refl (extractedAddrs exps)).append (swap.subperm.trans coreSub)
        have oldSub : (extractedAddrs exps ++ codeLocations exps ++
            (codeLocations exps).map Nat.succ).Sublist
            (reqCompileIncAddrs [Nat.succ] (exps, code)) := by
          simp only [reqCompileIncAddrs, List.map_cons, List.map_nil, List.flatten_cons,
            List.flatten_nil, List.append_nil]
          simp [List.append_assoc]
        have targetSub : List.Subperm
            (extractedAddrs exps ++ (codeLocations exps ++ (codeLocations exps).map Nat.succ))
            (reqCompileIncAddrs [Nat.succ] (exps, code)) := by
          simpa [List.append_assoc] using oldSub.subperm
        have total := outputSub.trans targetSub
        have inputNodup := distinctOriginal
        obtain ⟨middle, perm, sub⟩ := List.subperm_iff.mp total
        have result := sub.nodup (perm.nodup_iff.mpr inputNodup)
        simpa [reqCompileIncAddrs, extract.1, List.append_assoc] using result
      · constructor
        · exact extract.2
        · have locs := ClosCall.calls_codeLocations_mem exps (known, []) out final run
          have labels := ClosCall.calls_addSucc_codeLocations exps (known, []) out final run
          intro k hk
          simp only [Set.mem_ofPred_eq, reqCompileIncAddrs, List.map_nil, List.flatten_nil,
            List.map_cons, List.flatten_cons, List.append_nil, extract.1,
            List.mem_append] at hk ⊢
          rcases hk with (((hk | hk) | hk) | hk)
          · exact Or.inl (Or.inl (Or.inl (Or.inl hk)))
          · have h := locs k (Or.inl hk)
            simp only [List.map_nil, codeLocations, List.not_mem_nil, or_false] at h
            exact Or.inl (Or.inl (Or.inl (Or.inr h)))
          · have h := labels hk
            simp only [List.map_nil, List.not_mem_nil, Set.mem_ofPred_eq,
              Set.mem_union, Set.mem_image, false_or] at h
            rcases h with ⟨x, hx, rfl⟩
            exact Or.inr (List.mem_map.mpr ⟨x, hx, rfl⟩)
          · have h := locs k (Or.inr hk)
            simp only [List.map_nil, codeLocations, List.not_mem_nil, or_false] at h
            exact Or.inl (Or.inl (Or.inl (Or.inr h)))
end Flapjack.Compiler.Backend.ClosToBvl
