import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Control
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingle
import Flapjack.Misc.Sptree.FromList2

/-!
# `word_to_wordProof` `compile_single_correct`: the `Call` case

The `Call` `Resume` case of HOL `compile_single_correct`
(`word_to_wordProofScript.sml:347-589`). The callee body is looked up in the
source code table and, by `find_code_thm`, its `compile_single` image in the
compiled table; HOL's outer induction hypothesis runs the compiled body on both
code tables, `compile_single_lem` relates the source body to its compiled
image, and `permute_swap_lemma` aligns the final permutation.
-/

namespace Flapjack.Compiler.Backend.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm

namespace CompileSingleCorrectCallCarrier

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CompileSingleCorrectCallCarrier

section Helpers

variable {width : Nat} [NeZero width] {C F : Type}

/-- The `Call` clause of `evaluate` (Flapjack restatement of the last
    `evaluate_def` conjunct). -/
theorem evaluate_call_eq (s : WordSemStateFiniteExact width C F)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) (dest : Option Nat)
    (args : List Nat) :
    evaluate (.call ret dest args handler) s =
      match WordSemStateFiniteExact.getVars args s with
      | none => (some .error, s)
      | some xs =>
          if wordSemBadDestArgs dest args then (some .error, s)
          else
            match wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
            | none => (some .error, s)
            | some (args1, prog, ss) =>
                match ret with
                | none =>
                    match handler with
                    | none =>
                        if s.clock = 0 then (some .timeOut, flushState true s)
                        else
                          match evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with
                          | (res, s) =>
                              if wordSemBadFunReturn res then (some .error, s) else (res, s)
                    | some _ => (some .error, s)
                | some (n, names, retHandler, l1, l2) =>
                    if sptDomainEmpty names.1 ∨ ¬ n.Nodup then (some .error, s)
                    else
                      match wordSemCutEnvs names s.locals with
                      | none => (some .error, s)
                      | some envs =>
                          if s.clock = 0 then
                            (some .timeOut, flushState true
                              { s with stack := [],
                                       stackMax := (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler s)).stackMax })
                          else
                            match evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) with
                            | (some (.result x ys), s2) =>
                                if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then (some .error, s2)
                                else
                                  match popEnv s2 with
                                  | none => (some .error, s2)
                                  | some s1 =>
                                      if sptDomainEqUnion s1.locals envs.1 envs.2 then
                                        evaluate retHandler (setVars n ys s1)
                                      else (some .error, s1)
                            | (some (.exception x y), s2) =>
                                match handler with
                                | none => (some (.exception x y), s2)
                                | some (n, hprog, l1, l2) =>
                                    if x ≠ .loc l1 l2 then (some .error, s2)
                                    else if sptDomainEqUnion s2.locals envs.1 envs.2 then
                                      evaluate hprog (setVar n y s2)
                                    else (some .error, s2)
                            | (none, s) => (some .error, s)
                            | (some (.break _), s) => (some .error, s)
                            | (some (.continue _), s) => (some .error, s)
                            | res => res :=
  (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    s ret handler dest args

/-- States related by `word_state_eq_rel` with equal locals differ only in the
    permutation (Flapjack infrastructure). -/
theorem eqRel_permute {s t : WordSemStateFiniteExact width C F} (h : WordAlloc.wordStateEqRel s t)
    (hl : s.locals = t.locals) : ({ s with permute := t.permute } : WordSemStateFiniteExact width C F) = t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21⟩ := h
  cases s; cases t
  simp_all

end Helpers

/-- `code_rel` in the existential order of `find_code_thm` (Flapjack infrastructure). -/
theorem codeRel_findCode {width : Nat} [NeZero width] {stc ttc : Spt (Nat × WordLangProgHOL (BitVec width))}
    (h : codeRel stc ttc) :
    ∀ n v, sptLookup n stc = some v →
      ∃ (t : Bool) (k a : Nat) (c : AsmConfigExact width) (col : Option (Spt Nat)),
        sptLookup n ttc = some (compileSingle t k a c ((n, v), col)).2 := by
  intro n v hv
  obtain ⟨col, t, k, a, c, hl⟩ := h n v hv
  exact ⟨t, k, a, c, col, hl⟩

open Classical in
/-- The tail-call branch of the `Call` case (Flapjack factoring of HOL's
    `(*Tail calls*)` subproof). -/
theorem compileSingleCorrect_callTail {width : Nat} [NeZero width] {C F : Type}
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) (dest : Option Nat) (args : List Nat)
    (st : WordSemStateFiniteExact width C F) (ih : CompileSingleCorrectLowerIH tt kk aa co st) :
    CompileSingleCorrectAt tt kk aa co (.call none dest args none) st := by
  rintro l coracle cc ⟨hrel, hdom, hcomp, rfl, hgc⟩
  rcases hxs : WordSemStateFiniteExact.getVars args st with _ | xs
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp
  by_cases hbad : wordSemBadDestArgs dest args = true
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp [hbad]
  rcases hfc : wordSemFindCode dest (wordSemAddRetLoc none xs) st.code st.stackSize with
    _ | ⟨args1, prog, ss⟩
  · refine ⟨st.permute, ?_⟩
    rw [evaluate_call_eq, hxs]
    simp [hbad, hfc]
  obtain ⟨t, k, a, c, col, n, prog', hcs, hfcT⟩ :=
    find_code_thm st l dest none xs args1 prog ss ⟨codeRel_findCode hrel, hfc⟩
  let O := Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ st.compileOracle
  let T : WordSemStateFiniteExact width C F :=
    { st with
      code := l
      compileOracle := O
      compile := cc }
  -- the two runs of the call, from the callee runs
  have srcRun : ∀ (P : Nat → Nat → Nat) (r : Option (WordSemResult width))
      (s' : WordSemStateFiniteExact width C F),
      evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock { st with permute := P })) =
        (r, s') →
      evaluate (.call none dest args none) { st with permute := P } =
        if st.clock = 0 then (some .timeOut, flushState true { st with permute := P })
        else if wordSemBadFunReturn r then (some .error, s') else (r, s') := by
    intro P r s' h
    rw [evaluate_call_eq, show WordSemStateFiniteExact.getVars args { st with permute := P } = some xs
      from (getVars_congr st { st with permute := P } rfl args).trans hxs]
    dsimp only
    rw [if_neg hbad, show wordSemFindCode dest (wordSemAddRetLoc none xs) st.code st.stackSize =
      some (args1, prog, ss) from hfc]
    dsimp only
    split
    · rfl
    · rw [h]
  have tgtRun : ∀ (r : Option (WordSemResult width)) (s' : WordSemStateFiniteExact width C F),
      evaluate prog' (WordSemStateFiniteExact.callEnv args1 ss (decClock T)) = (r, s') →
      evaluate (.call none dest args none) T =
        if st.clock = 0 then (some .timeOut, flushState true T)
        else if wordSemBadFunReturn r then (some .error, s') else (r, s') := by
    intro r s' h
    rw [evaluate_call_eq, show WordSemStateFiniteExact.getVars args T = some xs
      from (getVars_congr st T rfl args).trans hxs]
    dsimp only
    rw [if_neg hbad, show wordSemFindCode dest (wordSemAddRetLoc none xs) l st.stackSize =
      some (args1, prog', ss) from hfcT]
    dsimp only
    split
    · rfl
    · rw [h]
  by_cases hz : st.clock = 0
  · refine ⟨st.permute, ?_⟩
    obtain ⟨r0, s0⟩ := evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock st))
    rcases h1 : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock st)) with ⟨r0, s0⟩
    rcases h2 : evaluate prog' (WordSemStateFiniteExact.callEnv args1 ss (decClock T)) with ⟨r1, s1⟩
    rw [srcRun st.permute r0 s0 h1, tgtRun r1 s1 h2]
    simp only [hz, if_true]
    rw [if_neg (show some WordSemResult.timeOut ≠ some WordSemResult.error by simp)]
    exact ⟨trivial, hrel, hdom, by simp [flushState, T, O, hz]⟩
  -- the callee state
  let stt : WordSemStateFiniteExact width C F := WordSemStateFiniteExact.callEnv args1 ss (decClock st)
  obtain ⟨perm1, H1⟩ := ih prog' stt (Or.inr ⟨rfl, by
      show st.clock - 1 < st.clock; omega⟩) l O cc ⟨hrel, hdom, hcomp, rfl, hgc⟩
  rcases hA : evaluate prog' { stt with permute := perm1 } with ⟨resA, rA⟩
  rw [hA] at H1
  dsimp only at H1
  have hcs' : compileSingle t k a c ((n, args1.length, prog), col) = (n, args1.length, prog') :=
    Prod.ext rfl hcs
  obtain ⟨perm2, H2⟩ := compile_single_lem t k a c n col prog args1.length { stt with permute := perm1 }
    ⟨sptDomainFromList2 args1, hgc⟩
  rw [hcs'] at H2
  rcases hR : evaluate prog { { stt with permute := perm1 } with permute := perm2 } with ⟨res, rst⟩
  rw [hR] at H2
  dsimp only at H2
  by_cases herr : res = some .error
  · refine ⟨perm2, ?_⟩
    rcases h2 : evaluate prog' (WordSemStateFiniteExact.callEnv args1 ss (decClock T)) with ⟨r1, s1⟩
    rw [srcRun perm2 res rst hR, tgtRun r1 s1 h2]
    subst herr
    simp only [hz, if_false, ite_self]
    simp
  rw [if_neg herr, hA] at H2
  dsimp only at H2
  obtain ⟨hres, heq, hloc⟩ := H2
  subst resA
  rw [if_neg herr] at H1
  rcases hB : evaluate prog' { stt with code := l, compileOracle := O, compile := cc } with
    ⟨resB, rB⟩
  rw [hB] at H1
  dsimp only at H1
  obtain ⟨hresB, hcB, hdB, hsB⟩ := H1
  subst resB
  have hsw := permute_swap_lemma prog { stt with permute := perm2 } rA.permute
  rw [show evaluate prog { stt with permute := perm2 } = (res, rst) from hR] at hsw
  obtain ⟨perm3, hP⟩ := hsw herr
  refine ⟨perm3, ?_⟩
  rw [srcRun perm3 res _ hP, tgtRun res rB hB]
  simp only [hz, if_false]
  by_cases hbr : wordSemBadFunReturn res = true
  · simp [hbr]
  simp only [hbr, Bool.false_eq_true, if_false]
  have hlocal : rst.locals = rA.locals := by
    rcases res with _ | r
    · exact absurd rfl hbr
    cases r <;> first | exact absurd rfl hbr | exact hloc
  have hcode : rst.code = rA.code := heq.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm
  have hst : ({ rst with permute := rA.permute } : WordSemStateFiniteExact width C F) = rA :=
    eqRel_permute heq hlocal
  rw [if_neg herr]
  refine ⟨by simp, ?_, ?_, ?_⟩
  · show codeRel rst.code rB.code; rw [hcode]; exact hcB
  · show sptDomain rst.code = sptDomain rB.code; rw [hcode]; exact hdB
  · rw [← hst] at hsB; exact hsB

end Flapjack.Compiler.Backend.WordToWord
