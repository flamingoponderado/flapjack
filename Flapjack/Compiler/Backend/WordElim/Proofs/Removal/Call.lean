module

public import Flapjack.Compiler.Backend.WordElim.Proofs.Removal.CallSupport

@[expose] public section

/-!
# `word_removal_lemma`: the `Call` case

The `Call` case of HOL `word_removal_lemma` (`word_elimProofScript.sml:1296-1542`).
The piece is HOL's statement (`WordRemovalGoal`) for `Call`, given exactly the
four induction hypotheses of the rebound `evaluate_ind` `Call` clause (return
handler, exception handler, returning call body, tail call body) instantiated
at that statement.
-/

namespace Flapjack.Compiler.Backend.WordElim
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordProps
open Flapjack.Compiler.Backend.FlatElim

namespace WordElimRemovalCallSupport
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end WordElimRemovalCallSupport

section CallCase
variable {width : Nat} [NeZero width] {C F : Type}

/-- Case `Call` of HOL `word_removal_lemma` (`Resume word_removal_lemma[Call]`). -/
@[hol "cakeml/compiler/backend/proofs/word_elimProofScript.sml" "word_removal_lemma"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem word_removal_lemma_Call {width : Nat} [NeZero width] {C F : Type} :
    ∀ (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
      (dest : Option Nat) (args : List Nat)
      (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
      (s : WordSemStateFiniteExact width C F),
      ((∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs v5 s2 v8 x ys s1,
          WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
          wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
          v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
          v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
          wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 ∧
          evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) = (v5, s2) ∧
          v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ n.length) ∧
          popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
        WordRemovalGoal retHandler (setVars n ys s1)) ∧
      (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs v5 s2 v8 x' y v n' v2 h
          v4 l1' l2',
          WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
          wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
          v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
          v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
          wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 ∧
          evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) = (v5, s2) ∧
          v5 = some v8 ∧ v8 = .exception x' y ∧ handler = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
          v4 = (l1', l2') ∧ x' = .loc l1' l2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
        WordRemovalGoal h (setVar n' y s2)) ∧
      (∀ xs v3 args1 v10 prog ss v1 n v6 names v9 retHandler v11 l1 l2 envs,
          WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
          wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
          v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (names, v9) ∧
          v9 = (retHandler, v11) ∧ v11 = (l1, l2) ∧ ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup) ∧
          wordSemCutEnvs names s.locals = some envs ∧ s.clock ≠ 0 →
        WordRemovalGoal prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))) ∧
      (∀ xs v3 args1 v10 prog ss,
          WordSemStateFiniteExact.getVars args s = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
          wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize = some v3 ∧
          v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = none ∧ handler = none ∧ s.clock ≠ 0 →
        WordRemovalGoal prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)))) →
      WordRemovalGoal (.call ret dest args handler) s := by
  intro ret dest args handler s ⟨ihRet, ihExc, ihProg, ihTail⟩ result new_state reachable t
    ⟨hev, herr, hrel, hg, hni, hnic, hnict, hfwr, hcc⟩
  obtain ⟨code, rfl⟩ := wordStateRel_exists_withCode hrel
  have hR := wordStateRel_locs hrel
  have hcodeRel : codeRel reachable code s.code :=
    hrel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  -- the references of the call itself
  have hfwrDest : ∀ l, dest = some l → sptMem l reachable := by
    rintro l rfl
    apply hfwr
    show sptMem l (findWordRef (.call ret (some l) args handler : WordLangProgHOL (BitVec width)))
    rw [findWordRef_call]; simp [sptMem_sptUnion, sptMem_sptInsert]
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht] at hev
  rw [ht]
  have hgv' : WordSemStateFiniteExact.getVars args { s with code := code } = WordSemStateFiniteExact.getVars args s :=
    word_state_rel_get_vars hrel
  rw [hgv']
  rcases hgv : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only [hgv] at hev
    cases hev
    exact absurd rfl herr
  simp only [hgv] at hev ⊢
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true] at hev
    cases hev
    exact absurd rfl herr
  simp only [hbad, Bool.false_eq_true, if_false] at hev ⊢
  -- the arguments of the call (with the return location) are reachable
  have hxsR : ∀ v ∈ wordSemAddRetLoc ret xs, ∀ n o, v = .loc n o → sptMem n reachable := by
    rintro v hv n o rfl
    rcases ret with _ | ⟨rn, rnames, rh, rl1, rl2⟩
    · exact hR n (locOf_getVars s args hgv _ hv n o rfl)
    · rcases List.mem_cons.mp hv with h | h
      · cases h
        apply hfwr
        show sptMem n (findWordRef (.call (some (rn, rnames, rh, n, _)) dest args handler :
          WordLangProgHOL (BitVec width)))
        rw [findWordRef_call]; simp [sptMem_sptUnion, sptMem_sptInsert]
      · exact hR n (locOf_getVars s args hgv _ h n o rfl)
  have hfc : wordSemFindCode dest (wordSemAddRetLoc ret xs) code s.stackSize =
      wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize := by
    apply findCode_congr
    rintro l (hl | ⟨-, hne, hlast⟩)
    · exact hcodeRel l (hfwrDest l hl)
    · apply hcodeRel l
      have hmem := List.getLast_mem hne
      revert hlast
      generalize (wordSemAddRetLoc ret xs).getLast hne = w at hmem
      intro hlast
      rcases w with _ | ⟨b, _ | o⟩
      · cases hlast
      · cases hlast
        exact hxsR _ hmem _ 0 rfl
      · cases hlast
  rw [hfc]
  rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
    _ | ⟨args1, prog, ss⟩
  · simp only [hf] at hev
    cases hev
    exact absurd rfl herr
  simp only [hf] at hev ⊢
  obtain ⟨⟨lab, hlab, arity, hlk⟩, hargs⟩ := findCode_some hf
  have hlabR : sptMem lab reachable := by
    rcases hlab with hl | ⟨-, hne, hlast⟩
    · exact hfwrDest lab hl
    · have hmem := List.getLast_mem hne
      revert hlast
      generalize (wordSemAddRetLoc ret xs).getLast hne = w at hmem
      intro hlast
      rcases w with _ | ⟨b, _ | o⟩
      · cases hlast
      · cases hlast
        exact hxsR _ hmem _ 0 rfl
      · cases hlast
  have hniprog := noInstallFindCode s.code dest _ _ _ prog _ ⟨hnic, hf⟩
  have hfwrprog := codeClosed_findWordRef hcc hlabR hlk
  have hargs1 : ∀ v ∈ args1, ∀ n o, v = .loc n o → sptMem n reachable := by
    intro v hv
    rcases hargs with rfl | rfl
    · exact hxsR v hv
    · exact hxsR v (List.dropLast_subset _ hv)
  cases ret with
  | none =>
    cases handler with
    | some hv =>
      simp only at hev
      cases hev
      exact absurd rfl herr
    | none =>
      simp only at hev ⊢
      by_cases hz : s.clock = 0
      · rw [if_pos hz] at hev
        rw [if_pos hz]
        cases hev
        exact ⟨_, rfl, wordStateRel_flushState hrel true, fun n hn => hn.elim⟩
      simp only [hz, if_false] at hev ⊢
      rw [decClock_withCode, callEnv_withCode]
      have hrel' := wordStateRel_withCode (s1 := WordSemStateFiniteExact.callEnv args1 ss (decClock s))
        hrel rfl (callEnv_locsIn args1 ss (decClock s) (fun n h => hR n h) hargs1)
      rcases h1 : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with ⟨r, s2⟩
      rw [h1] at hev
      have hr : r ≠ some .error := by
        rintro rfl
        simp only [wordSemBadFunReturn, Bool.false_eq_true, if_false] at hev
        cases hev
        exact herr rfl
      obtain ⟨t2, ht2, hrel2, hloc2⟩ := ihTail xs _ args1 _ prog ss
        ⟨hgv, hbad, hf, rfl, rfl, rfl, rfl, hz⟩ r s2 reachable _
        ⟨h1, hr, hrel', hg, hniprog, hnic, hnict, hfwrprog, hcc⟩
      rw [ht2]
      simp only at hev ⊢
      split at hev
      · cases hev
        exact absurd rfl herr
      · rename_i hbr
        simp only [hbr, Bool.false_eq_true, if_false]
        cases hev
        exact ⟨t2, rfl, hrel2, hloc2⟩
  | some rv =>
    obtain ⟨n, names, retHandler, l1, l2⟩ := rv
    simp only at hev ⊢
    by_cases hdc : sptDomainEmpty names.1 ∨ ¬ n.Nodup
    · simp only [hdc, if_true] at hev
      cases hev
      exact absurd rfl herr
    simp only [hdc, if_false] at hev ⊢
    rcases hce : wordSemCutEnvs names s.locals with _ | envs
    · simp only [hce] at hev
      cases hev
      exact absurd rfl herr
    simp only [hce] at hev ⊢
    by_cases hz : s.clock = 0
    · rw [if_pos hz] at hev
      rw [if_pos hz]
      cases hev
      refine ⟨_, rfl, ?_, fun n hn => hn.elim⟩
      obtain ⟨X, hX⟩ : ∃ X,
          X = (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler s)).stackMax :=
        ⟨_, rfl⟩
      have hin := wordStateRel_withCode (s1 := { s with stack := [], stackMax := X }) hrel rfl
        (fun n hn => hR n (locsWithin_stackNil s X n hn))
      subst hX
      rcases handler with _ | ⟨_, _, _, _⟩ <;> exact wordStateRel_flushState hin true
    simp only [hz, if_false] at hev ⊢
    rw [decClock_withCode, pushEnv_withCode, callEnv_withCode]
    have hs'cg := pushEnv_code_gcFun envs handler (decClock s)
    have hrel' := wordStateRel_withCode
      (s1 := WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))
      hrel hs'cg.1 (callEnv_locsIn args1 ss _
        ((pushEnv_locsWithin (decClock s) names envs hce handler).locsIn (fun n h => hR n h))
        hargs1)
    rcases h1 : evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) with ⟨r, s2⟩
    rw [h1] at hev
    have hr : r ≠ some .error := by
      rintro rfl
      simp only at hev
      cases hev
      exact herr rfl
    have hgs' : gcNoNewLocs
        (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).gcFun := by
      rw [show (WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv envs handler (decClock s))).gcFun = s.gcFun from hs'cg.2]
      exact hg
    have hcs' : (WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv envs handler (decClock s))).code = s.code := hs'cg.1
    obtain ⟨t2, ht2, hrel2, hloc2⟩ := ihProg xs _ args1 _ prog ss _ n _ names _ retHandler _ l1 l2 envs
      ⟨hgv, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hdc, hce, hz⟩ r s2 reachable _
      ⟨h1, hr, hrel', hgs', hniprog, hcs' ▸ hnic, hnict, hfwrprog, hcs' ▸ hcc⟩
    rw [ht2]
    have hs2code : s2.code = s.code :=
      (code_of_evaluate h1 hniprog (hcs' ▸ hnic)).trans hcs'
    have ht2code : t2.code = code := code_of_evaluate ht2 hniprog hnict
    have hs2gc : s2.gcFun = s.gcFun := (gcFun_of_evaluate h1).trans hs'cg.2
    rcases r with _ | (⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | ev | _)
    · simp only at hev
      cases hev
      exact absurd rfl herr
    · -- the call returned
      simp only at hev ⊢
      by_cases hx : x ≠ .loc l1 l2 ∨ ys.length ≠ n.length
      · simp only [hx, if_true] at hev
        cases hev
        exact absurd rfl herr
      simp only [hx, if_false] at hev ⊢
      rcases hp : popEnv s2 with _ | s1
      · simp only [hp] at hev
        cases hev
        exact absurd rfl herr
      obtain ⟨t1, hpt, hrel1⟩ :=
        word_state_rel_pop_env (δ := Unit) (ε := Unit) reachable s2 t2 s1 () () hrel2 hp
      simp only [hp] at hev
      simp only [hpt]
      rw [show t1.locals = s1.locals from hrel1.1]
      by_cases hdu : sptDomainEqUnion s1.locals envs.1 envs.2
      · simp only [hdu, if_true] at hev ⊢
        have hs1 := popEnvConst s2 s1 hp
        have ht1 := popEnvConst t2 t1 hpt
        have hs1code : s1.code = s.code := hs1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans hs2code
        have ht1code : t1.code = code := ht1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans ht2code
        have hs1gc : s1.gcFun = s.gcFun := hs1.2.2.2.2.2.2.2.2.2.2.1.trans hs2gc
        have hys : ⋃₀ {S | S ∈ ys.map (fun x' => match destWordLoc x' with
            | none => (∅ : Set Nat) | some x => {x})} ⊆ sptDomainSet reachable := by
          rintro m ⟨S, hS, hm⟩
          obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hS
          cases hd : destWordLoc v with
          | none => simp [hd] at hm
          | some b =>
            simp only [hd, Set.mem_singleton_iff] at hm
            subst hm
            exact hloc2 ⟨v, hv, hd⟩
        have hlen : n.length = ys.length := by
          simp only [not_or, not_not] at hx
          exact hx.2.symm
        have hfwrRet : sptDomainSet (findWordRef retHandler) ⊆ sptDomainSet reachable := by
          intro m hm
          apply hfwr
          show sptMem m (findWordRef (.call (some (n, names, retHandler, l1, l2)) dest args handler :
            WordLangProgHOL (BitVec width)))
          rw [findWordRef_call]
          simp only [sptMem_sptUnion, sptMem_sptInsert]
          exact Or.inr (Or.inl (Or.inr hm))
        exact ihRet xs _ args1 _ prog ss _ n _ names _ retHandler _ l1 l2 envs _ s2 _ x ys s1
          ⟨hgv, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hdc, hce, hz, h1, rfl, rfl, hx, hp, hdu⟩
          result new_state reachable (setVars n ys t1)
          ⟨hev, herr, word_state_rel_set_vars ⟨hrel1, hys, hlen⟩,
            (show (setVars n ys s1).gcFun = s.gcFun from hs1gc) ▸ hg,
            noInstall_call_ret hni,
            (show (setVars n ys s1).code = s.code from hs1code) ▸ hnic,
            (show (setVars n ys t1).code = code from ht1code) ▸ hnict,
            hfwrRet, (show (setVars n ys s1).code = s.code from hs1code) ▸ hcc⟩
      · simp only [hdu, if_false] at hev
        cases hev
        exact absurd rfl herr
    · -- the call raised an exception
      rcases handler with _ | ⟨n', hprog, l1', l2'⟩
      · simp only at hev ⊢
        cases hev
        exact ⟨t2, rfl, hrel2, hloc2⟩
      · simp only at hev ⊢
        by_cases hx : x ≠ .loc l1' l2'
        · rw [if_pos hx] at hev
          cases hev
          exact absurd rfl herr
        simp only [hx, if_false] at hev ⊢
        rw [show t2.locals = s2.locals from hrel2.1]
        by_cases hdu : sptDomainEqUnion s2.locals envs.1 envs.2
        · simp only [hdu, if_true] at hev ⊢
          have hy : (match destWordLoc y with
              | none => (∅ : Set Nat) | some n => ({n} : Set Nat)) ⊆ sptDomainSet reachable := by
            cases y with
            | word w => simp
            | loc b o =>
              intro m hm
              simp only [destWordLoc_loc, Set.mem_singleton_iff] at hm
              subst hm
              exact hloc2 (show destResultLoc (some (.exception x (.loc m o))) m from rfl)
          have hfwrH : sptDomainSet (findWordRef hprog) ⊆ sptDomainSet reachable := by
            intro m hm
            apply hfwr
            show sptMem m (findWordRef (.call (some (n, names, retHandler, l1, l2)) dest args
              (some (n', hprog, l1', l2')) : WordLangProgHOL (BitVec width)))
            rw [findWordRef_call]
            simp only [sptMem_sptUnion, sptMem_sptInsert]
            exact Or.inr (Or.inr hm)
          exact ihExc xs _ args1 _ prog ss _ n _ names _ retHandler _ l1 l2 envs _ s2 _ x y _ n' _
            hprog _ l1' l2'
            ⟨hgv, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hdc, hce, hz, h1, rfl, rfl, rfl, rfl,
              rfl, rfl, not_not.mp hx, hdu⟩
            result new_state reachable (setVar n' y t2)
            ⟨hev, herr, word_state_rel_set_var ⟨hrel2, hy⟩,
              (show (setVar n' y s2).gcFun = s.gcFun from hs2gc) ▸ hg,
              noInstall_call_handler hni,
              (show (setVar n' y s2).code = s.code from hs2code) ▸ hnic,
              (show (setVar n' y t2).code = code from ht2code) ▸ hnict,
              hfwrH, (show (setVar n' y s2).code = s.code from hs2code) ▸ hcc⟩
        · simp only [hdu, if_false] at hev
          cases hev
          exact absurd rfl herr
    · simp only at hev
      cases hev
      exact absurd rfl herr
    · simp only at hev
      cases hev
      exact absurd rfl herr
    · simp only at hev ⊢
      cases hev
      exact ⟨t2, rfl, hrel2, hloc2⟩
    · simp only at hev ⊢
      cases hev
      exact ⟨t2, rfl, hrel2, hloc2⟩
    · simp only at hev ⊢
      cases hev
      exact ⟨t2, rfl, hrel2, hloc2⟩
    · exact absurd rfl hr

end CallCase

end Flapjack.Compiler.Backend.WordElim
