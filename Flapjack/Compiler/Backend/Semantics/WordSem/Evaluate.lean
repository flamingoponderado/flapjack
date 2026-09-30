import Flapjack.Compiler.Backend.Semantics.WordSem.Inst
import Flapjack.Compiler.Backend.Semantics.WordSem.ShMem
import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
import Flapjack.Compiler.Backend.Semantics.WordSem.Domain
import Flapjack.Misc.ShiftSeq
import Flapjack.Pancake.Semantics.LoopSem

/-!
# Exact HOL `wordSem$evaluate_def`

Counterpart of `cakeml/compiler/backend/semantics/wordSemScript.sml:1016-1260`
(bead `flapjack-h29l.8.2`): the big-step, clocked semantics of
`wordLang$prog`, over the tagged `WordSemStateFiniteExact` and the tagged
wordSem helpers.

HOL proves termination with the lexicographic measure
`(s.termdep, s.clock, prog_size)`, using `fix_clock` to bound the clock of an
intermediate result.  The Lean definition uses the same measure, with Lean's
derived `sizeOf` for the program size.  The `decreasing_by` obligations
follow HOL's `fix_clock_IMP_LESS_EQ` (`fixClock_IMP_LESS_EQ`) and
`termdep_rw`.  Because `inst` rounds and chooses NaNs through the IEEE
renderings, `evaluate` is `noncomputable`.  HOL equality on the compiler
configuration type `'c` in the `Install` clause is decided classically.
-/

namespace Flapjack

namespace WordSemEvaluateSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged `evaluate`. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemEvaluateSupport

namespace WordSemStateFiniteExact

section Measure

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

theorem pushEnv_termdep (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (b : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) : (pushEnv envs b s).termdep = s.termdep := by
  rcases b with _ | ⟨_, _, _, _⟩ <;> rfl

theorem popEnv_termdep (s s1 : WordSemStateFiniteExact width C F) :
    popEnv s = some s1 → s1.termdep = s.termdep := by
  unfold popEnv
  split
  · intro h; cases h; rfl
  · intro h; cases h; rfl
  · intro h; cases h

theorem cutState_clock_termdep (names : WordLangCutsetsHOL)
    (s s1 : WordSemStateFiniteExact width C F) :
    cutState names s = some s1 → s1.clock = s.clock ∧ s1.termdep = s.termdep := by
  unfold cutState
  split
  · intro h; cases h
  · intro h; cases h; exact ⟨rfl, rfl⟩

/-- The lexicographic order on `(termdep, clock, size)` from its three cases. -/
theorem wordSemLex {a b c a' b' c' : Nat}
    (h : a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c')))) :
    Prod.Lex (fun a₁ a₂ => a₁ < a₂) (Prod.Lex (fun a₁ a₂ => a₁ < a₂) fun a₁ a₂ => a₁ < a₂)
      (a, b, c) (a', b', c') := by
  rcases h with h | ⟨rfl, h | ⟨rfl, h⟩⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ (Prod.Lex.left _ _ h)
  · exact Prod.Lex.right _ (Prod.Lex.right _ h)

end Measure

open Classical in
/-- Rendering of HOL `evaluate_def` (`wordSemScript.sml:1016-1260`), clause by clause
    over the tagged helpers:
    * straight-line forms: `Skip`, `Alloc`, `StoreConsts`, `Move`, `Inst`,
      `Assign`, `Get`, `Set`, `OpCurrHeap`, `Store`, and `Tick`;
    * control forms: `MustTerminate`, `Seq`, `Return`, `Raise`,
      `Break`/`Continue`, `If`, and `Loop`;
    * `LocValue`, `Install`, `CodeBufferWrite`/`DataBufferWrite`, `FFI`, and
      `ShareInst`;
    * `Call`: tail calls, and returning calls with their result, exception
      and handler cases.
    HOL's equality tests on results are rendered as matches, and set
    conditions on `domain` use `sptDomainEmpty`/`sptDomainEqUnion`.

    Not an exact port: the `@[hol]` tag is withdrawn (bead `flapjack-2hoy.2`,
    coordinator decision 2026-09-30).  The `Inst` clause delegates to the
    untagged `inst`, whose `FPSqrt` clause is the rational-cut reformulation
    of HOL `fp64_sqrt` (see `inst`).  The faithful prerequisite is bead
    `flapjack-dshl`.  Every other clause follows HOL clause by clause. -/
noncomputable def evaluate {width : Nat} [NeZero width] {C : Type} {F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    Option (WordSemResult width) × WordSemStateFiniteExact width C F :=
  match p with
  | .skip => (none, s)
  | .alloc n names =>
      match getVar n s with
      | some (.word w) => alloc w names s
      | _ => (some .error, s)
  | .storeConsts t1 t2 addr offset words =>
      match getVar addr s, getVar offset s with
      | some (.word a), some (.word off) =>
          if ¬ wordSemConstAddresses a words s.mdomain = true then (some .error, s)
          else
            let s := { s with memory := wordSemConstWrites a off words s.memory }
            let s := setVar offset (.word off) (unsetVar t1 (unsetVar t2 s))
            (none, setVar addr (.word (a + wordSemBytesInWord * BitVec.ofNat width words.length)) s)
      | _, _ => (some .error, s)
  | .move _ moves =>
      if (moves.map Prod.fst).Nodup then
        match getVars (moves.map Prod.snd) s with
        | none => (some .error, s)
        | some vs => (none, setVars (moves.map Prod.fst) vs s)
      else (some .error, s)
  | .inst i =>
      match inst i s with
      | some s1 => (none, s1)
      | none => (some .error, s)
  | .assign v exp =>
      match wordExp s exp with
      | none => (some .error, s)
      | some w => (none, setVar v w s)
  | .get v name =>
      match getStore name s with
      | none => (some .error, s)
      | some x => (none, setVar v x s)
  | .set v exp =>
      if v = .handler ∨ v = .bitmapBase then (some .error, s)
      else
        match wordExp s exp with
        | none => (some .error, s)
        | some w => (none, setStore v w s)
  | .opCurrHeap b dst src =>
      match wordExp s (.op b [.var src, .lookup .currHeap]) with
      | none => (some .error, s)
      | some w => (none, setVar dst w s)
  | .store exp v =>
      match wordExp s exp, getVar v s with
      | some (.word a), some w =>
          match memStore a w s with
          | some s1 => (none, s1)
          | none => (some .error, s)
      | _, _ => (some .error, s)
  | .tick =>
      if s.clock = 0 then (some .timeOut, flushState true s) else (none, decClock s)
  | .mustTerminate p =>
      if _h : s.termdep = 0 then (some .error, s)
      else
        match evaluate p { s with clock := wordSemMustTerminateLimit width,
                                  termdep := s.termdep - 1 } with
        | (res, s1) =>
            match res with
            | some .timeOut => (some .error, s)
            | _ => (res, { s1 with clock := s.clock, termdep := s.termdep })
  | .seq c1 c2 =>
      match _h : fixClock s (evaluate c1 s) with
      | (res, s1) =>
          match (generalizing := false) res with
          | none => evaluate c2 s1
          | _ => (res, s1)
  | .return n ms =>
      match getVar n s, getVars ms s with
      | some (.loc l1 l2), some ys => (some (.result (.loc l1 l2) ys), flushState false s)
      | _, _ => (some .error, s)
  | .raise n =>
      match getVar n s with
      | none => (some .error, s)
      | some w =>
          match jumpExc s with
          | none => (some .error, s)
          | some (s, l1, l2) => (some (.exception (.loc l1 l2) w), s)
  | .break k => (some (.break k), s)
  | .continue k => (some (.continue k), s)
  | .ite cmp r1 ri c1 c2 =>
      match getVar r1 s, getVarImm ri s with
      | some x, some y =>
          match wordSemWordCmp cmp x y with
          | some true => evaluate c1 s
          | some false => evaluate c2 s
          | none => (some .error, s)
      | _, _ => (some .error, s)
  | .loop names c exitNames =>
      match _hs : cutState (names, .ln) s with
      | none => (some .error, s)
      | some s' =>
          match _h : fixClock s' (evaluate c s') with
          | (res, s1) =>
              if wordSemContLoop res then
                (if _hc : s1.clock = 0 then (some .timeOut, flushState true s1)
                 else evaluate (wordSemSTOP (.loop names c exitNames)) (decClock s1))
              else
                match (generalizing := false) res with
                | some (.break 0) =>
                    match (generalizing := false) cutState (exitNames, .ln) s1 with
                    | none => (some .error, s1)
                    | some s2 => (none, s2)
                | _ => (wordSemExitLoop res, s1)
  | .locValue r l1 =>
      if sptMem l1 s.code then (none, setVar r (.loc l1 0) s) else (some .error, s)
  | .install ptr len dptr dlen names =>
      match wordSemCutEnv names s.locals with
      | none => (some .error, s)
      | some env =>
          match getVar ptr s, getVar len s, getVar dptr s, getVar dlen s with
          | some (.word w1), some (.word w2), some (.word w3), some (.word w4) =>
              let (cfg, progs) := s.compileOracle 0
              match wordSemBufferFlush s.codeBuffer w1 w2, wordSemBufferFlush s.dataBuffer w3 w4 with
              | some (bytes, cb), some (data, db) =>
                  let newOracle := holShiftSeq 1 s.compileOracle
                  match s.compile cfg progs, progs with
                  | some (bytes', data', cfg'), (k, _) :: _ =>
                      if bytes = bytes' ∧ data = data' ∧ (newOracle 0).1 = cfg' then
                        (none, { s with
                          codeBuffer := cb
                          dataBuffer := db
                          code := sptUnion s.code (sptFromAList progs)
                          locals := sptInsert ptr (.loc k 0) env
                          fpRegs := HolFiniteMapExact.empty
                          compileOracle := newOracle
                          stackMax := none
                          stackSize := .ln })
                      else (some .error, s)
                  | _, _ => (some .error, s)
              | _, _ => (some .error, s)
          | _, _, _, _ => (some .error, s)
  | .codeBufferWrite r1 r2 =>
      match getVar r1 s, getVar r2 s with
      | some (.word w1), some (.word w2) =>
          match wordSemBufferWrite s.codeBuffer w1 (w2.setWidth 8) with
          | some newCb => (none, { s with codeBuffer := newCb })
          | none => (some .error, s)
      | _, _ => (some .error, s)
  | .dataBufferWrite r1 r2 =>
      match getVar r1 s, getVar r2 s with
      | some (.word w1), some (.word w2) =>
          match wordSemBufferWrite s.dataBuffer w1 w2 with
          | some newDb => (none, { s with dataBuffer := newDb })
          | none => (some .error, s)
      | _, _ => (some .error, s)
  | .ffi ffiIndex ptr1 len1 ptr2 len2 names =>
      match getVar len1 s, getVar ptr1 s, getVar len2 s, getVar ptr2 s with
      | some (.word w), some (.word w2), some (.word w3), some (.word w4) =>
          match wordSemCutEnv names s.locals with
          | none => (some .error, s)
          | some env =>
              match readBytearrayWordHOL w2 w.toNat (memLoadByteAuxExact s.memory s.mdomain s.be),
                  readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
              | some bytes, some bytes2 =>
                  match callFFIHOL s.ffi (.extCall ffiIndex) bytes bytes2 with
                  | .final outcome => (some (.finalFfi outcome), flushState true s)
                  | .ret newFfi newBytes =>
                      let newM := writeBytearrayExact w4 newBytes s.memory s.mdomain s.be
                      (none, { s with memory := newM, locals := env,
                                      fpRegs := HolFiniteMapExact.empty, ffi := newFfi })
              | _, _ => (some .error, s)
      | _, _, _, _ => (some .error, s)
  | .shareInst op v exp =>
      match wordExp s exp with
      | some (.word ad) => shareInst op v ad s
      | _ => (some .error, s)
  | .call ret dest args handler =>
      match (generalizing := false) getVars args s with
      | none => (some .error, s)
      | some xs =>
          if wordSemBadDestArgs dest args then (some .error, s)
          else
            match (generalizing := false) wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
            | none => (some .error, s)
            | some (args1, prog, ss) =>
                match (generalizing := false) ret with
                | none =>
                    match (generalizing := false) handler with
                    | none =>
                        if _hc : s.clock = 0 then (some .timeOut, flushState true s)
                        else
                          match evaluate prog (callEnv args1 ss (decClock s)) with
                          | (res, s) =>
                              if wordSemBadFunReturn res then (some .error, s) else (res, s)
                    | some _ => (some .error, s)
                | some (n, names, retHandler, l1, l2) =>
                    if sptDomainEmpty names.1 ∨ ¬ n.Nodup then (some .error, s)
                    else
                      match (generalizing := false) wordSemCutEnvs names s.locals with
                      | none => (some .error, s)
                      | some envs =>
                          if _hc : s.clock = 0 then
                            (some .timeOut, flushState true
                              { s with stack := [],
                                       stackMax := (callEnv args1 ss (pushEnv envs handler s)).stackMax })
                          else
                            match _h : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s)))
                                (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))) with
                            | (some (.result x ys), s2) =>
                                if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then (some .error, s2)
                                else
                                  match (generalizing := false) _hp : popEnv s2 with
                                  | none => (some .error, s2)
                                  | some s1 =>
                                      if sptDomainEqUnion s1.locals envs.1 envs.2 then
                                        evaluate retHandler (setVars n ys s1)
                                      else (some .error, s1)
                            | (some (.exception x y), s2) =>
                                match (generalizing := false) handler with
                                | none => (some (.exception x y), s2)
                                | some (n, hprog, l1, l2) =>
                                    if x ≠ .loc l1 l2 then (some .error, s2)
                                    else if sptDomainEqUnion s2.locals envs.1 envs.2 then
                                      evaluate hprog (setVar n y s2)
                                    else (some .error, s2)
                            | (none, s) => (some .error, s)
                            | (some (.break _), s) => (some .error, s)
                            | (some (.continue _), s) => (some .error, s)
                            | res => res
termination_by (s.termdep, s.clock, sizeOf p)
decreasing_by
  all_goals
    simp_wf
    apply wordSemLex
    try (have hfc := fixClock_IMP_LESS_EQ _ _ _ _ _h)
    try (have hcs := cutState_clock_termdep _ _ _ _hs)
    try (have hpc := popEnv_clock _ _ _hp)
    try (have hpt := popEnv_termdep _ _ _hp)
    try simp only [callEnv, decClock, setVars, setVar, pushEnv_clock, pushEnv_termdep,
      wordSemSTOP, true_and] at *
    omega

end WordSemStateFiniteExact

end Flapjack
