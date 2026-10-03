import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Jumps
import Flapjack.Compiler.Backend.StackToLab.Proofs.Prelude

/-! `flatten_correct` case `Call` (`stack_to_labProofScript.sml:2041-2397`):
tail calls jump to the callee; returning calls first load the return label
into the link register, jump, and continue with the return handler or the
exception handler. -/

namespace Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers

section
variable {width : Nat} [NeZero width] {C F : Type}

/-- A fetched register jump to a zero-offset location. -/
theorem jumpRegStep {t : Flapjack.Compiler.Backend.LabSem.State width C F} {reg d p : Nat}
    (c : Nat) (fetch : asmFetchAux t.pc t.code = some (.asm (.asmi (.jumpReg reg)) [] 0))
    (hreg : t.regs reg = .loc d 0) (hpc : locToPc d 0 t.code = some p) :
    evaluate { t with clock := c + 1 } = evaluate { t with pc := p, clock := c } := by
  rw [evaluate]
  simp [asmFetch, fetch, hreg, hpc, updPc, decClock]

/-- The compiled jump of a call target found by `find_code`, entering the
callee's installed code. -/
theorem compileJumpEnter {s : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {dest : Nat ⊕ Nat}
    {regs : HolFiniteMapExact Nat (WordLocW width)} {prog : HolProg width}
    (hregs : ∀ r v, regs.lookup r = some v → t1.regs r = v)
    (rel : stateRel s t1)
    (fetch : asmFetchAux t1.pc t1.code = some (compileJumpHOL dest))
    (hfind : StackSemControl.findCode dest regs s.code = some prog) :
    ∃ d pc', sptLookup d s.code = some prog ∧ locToPc d 0 t1.code = some pc' ∧
      StackProps.callArgs prog t1.ptrReg t1.lenReg t1.ptr2Reg t1.len2Reg t1.linkReg ∧
      codeInstalled pc' (appListAppend (flattenHOL true prog d
        (StackAlloc.nextLabHOL prog 2) [] []).1) t1.code ∧
      ∀ c, evaluate { t1 with clock := c + 1 } = evaluate { t1 with pc := pc', clock := c } := by
  cases dest with
  | inl d =>
    have hlook : sptLookup d s.code = some prog := by
      simpa [StackSemControl.findCode] using hfind
    obtain ⟨ca, pc', inst, entry⟩ := relCode rel hlook
    exact ⟨d, pc', hlook, entry, ca, inst, fun c => jumpStep c fetch entry⟩
  | inr r =>
    simp only [StackSemControl.findCode] at hfind
    split at hfind
    · rename_i d hr
      obtain ⟨ca, pc', inst, entry⟩ := relCode rel hfind
      exact ⟨d, pc', hfind, entry, ca, inst, fun c => jumpRegStep c fetch (hregs r _ hr) entry⟩
    · simp at hfind

/-- `Call` case without a return handler (a tail call). -/
theorem flattenCorrectCallTail (s1 : StackSemStateFiniteExact width C F) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (ih : FlattenIH (.call none dest handler) s1) :
    FlattenProp (.call none dest handler) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_call] at ev
  simp only at ev
  have fetch : asmFetchAux t1.pc t1.code = some (compileJumpHOL dest) :=
    fetchSingle (Prelude.notIsLabelCompileJump dest)
      (by simpa [flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  rcases hfind : StackSemControl.findCode dest s1.regs s1.code with _ | prog
  · rw [hfind] at ev; exact (err ev).elim
  rw [hfind] at ev
  simp only at ev
  rcases handler with _ | hd
  swap; · exact (err ev).elim
  simp only at ev
  obtain ⟨d, pc', -, entry, caP, instP, step⟩ :=
    compileJumpEnter (fun r v h => InstCorrect.regOfLookup rel h) rel fetch hfind
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, t1, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0, StackSemEvaluateClock.fixClockEvaluate] at ev
  rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) with ⟨res, s'⟩
  rw [e2] at ev
  simp only at ev
  by_cases hbad : StackSemControl.badFunReturn res = true
  · rw [if_pos hbad] at ev; exact (err ev).elim
  rw [if_neg hbad] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  obtain ⟨x', rfl⟩ := notBadFunReturnImpSome _ hbad
  have rel' : stateRel (StackSemStateOps.decClock s1)
      { t1 with pc := pc', clock := t1.clock - 1 } := StateRel.stateRelDecClock rel
  have lt : MeasureLt prog (StackSemStateOps.decClock s1) (.call none dest none) s1 :=
    .inl (by simp [StackSemStateOps.decClock]; omega)
  have ph := ih prog _ lt true (some x') s' d (StackAlloc.nextLabHOL prog 2) [] []
    { t1 with pc := pc', clock := t1.clock - 1 }
    ⟨e2, nerr, rel', caP, instP, by simp [entry]⟩
  exact flattenConclComposeSome (runEnter (by omega) step) rfl rfl rfl rfl rfl
    (List.prefix_refl _)
    (flattenConclResult (p' := prog) (t' := true) (l' := 0) (h := ph) rfl
      (resultViewIndep hbad _ _ _ _ _ _))

/-- A fetched `LocValue` of an installed label. -/
theorem locValueStep {t : Flapjack.Compiler.Backend.LabSem.State width C F} {reg a b q : Nat}
    (c : Nat)
    (fetch : asmFetchAux t.pc t.code = some (.labAsm (.locValue reg (.lab a b)) 0 [] 0))
    (hpc : locToPc a b t.code = some q) :
    evaluate { t with clock := c + 1 } = evaluate { t with
      regs := fun key => if key = reg then .loc a b else t.regs key
      pc := t.pc + 1
      clock := c } := by
  rw [evaluate]
  simp [asmFetch, fetch, getPcValue, hpc, incPc, decClock, updReg, labToLoc]

/-- Entry of a returning call: the return label is loaded into the link
register and control jumps into the callee, consuming two target clock ticks
for the source's one. -/
theorem callEnter {s1 : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {link l1 l2 : Nat}
    {dest : Nat ⊕ Nat} {prog : HolProg width} (rel : stateRel s1 t1) (h0 : s1.clock ≠ 0)
    (fetchA : asmFetchAux t1.pc t1.code =
      some (.labAsm (.locValue link (.lab l1 l2)) 0 [] 0))
    (fetchB : asmFetchAux (t1.pc + 1) t1.code = some (compileJumpHOL dest))
    (locL : locToPc l1 l2 t1.code = some (t1.pc + 2))
    (hfind : StackSemControl.findCode dest (s1.regs.eraseEq link) s1.code = some prog) :
    ∃ (d pc' : Nat) (tE : Flapjack.Compiler.Backend.LabSem.State width C F),
      (∀ ck1, evaluate { t1 with clock := t1.clock + 1 + ck1 } =
        evaluate { tE with clock := tE.clock + ck1 }) ∧
      tE.lenReg = t1.lenReg ∧ tE.ptrReg = t1.ptrReg ∧ tE.len2Reg = t1.len2Reg ∧
      tE.ptr2Reg = t1.ptr2Reg ∧ tE.linkReg = t1.linkReg ∧ tE.code = t1.code ∧ tE.pc = pc' ∧
      stateRel (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) s1)) tE ∧
      locToPc d 0 t1.code = some pc' ∧
      StackProps.callArgs prog t1.ptrReg t1.lenReg t1.ptr2Reg t1.len2Reg t1.linkReg ∧
      codeInstalled pc' (appListAppend (flattenHOL true prog d
        (StackAlloc.nextLabHOL prog 2) [] []).1) t1.code := by
  have clk := relClock rel
  let tB : Flapjack.Compiler.Backend.LabSem.State width C F :=
    { t1 with
      regs := fun key => if key = link then .loc l1 l2 else t1.regs key
      pc := t1.pc + 1 }
  have relB : stateRel (StackSemStateOps.setVar link (.loc l1 l2) s1) tB :=
    StateRel.setVarUpdReg rel
  have hregs : ∀ r v, (s1.regs.eraseEq link).lookup r = some v → tB.regs r = v := by
    intro r v h
    simp only [HolFiniteMapExact.eraseEq, FDOMSUB_HOL] at h
    split_ifs at h with e
    simp only [tB, e, if_false]
    exact InstCorrect.regOfLookup rel h
  obtain ⟨d, pc', -, entry, caP, instP, stepB⟩ :=
    compileJumpEnter (t1 := tB) (s := StackSemStateOps.setVar link (.loc l1 l2) s1) hregs relB
      fetchB hfind
  refine ⟨d, pc', { tB with pc := pc', clock := t1.clock - 1 }, fun ck1 => ?_, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, StateRel.stateRelDecClock relB, entry, caP, instP⟩
  rw [show t1.clock + 1 + ck1 = (t1.clock - 1 + ck1 + 1) + 1 by omega,
    locValueStep _ fetchA locL]
  exact stepB (t1.clock - 1 + ck1)

theorem chainRun {t1 t2 t3 : Flapjack.Compiler.Backend.LabSem.State width C F} {a b : Nat}
    (r1 : ∀ ck1, evaluate { t1 with clock := t1.clock + a + ck1 } =
      evaluate { t2 with clock := t2.clock + ck1 })
    (r2 : ∀ ck1, evaluate { t2 with clock := t2.clock + b + ck1 } =
      evaluate { t3 with clock := t3.clock + ck1 }) :
    ∀ ck1, evaluate { t1 with clock := t1.clock + (a + b) + ck1 } =
      evaluate { t3 with clock := t3.clock + ck1 } := by
  intro ck1
  rw [show t1.clock + (a + b) + ck1 = t1.clock + a + (b + ck1) by omega, r1,
    ← Nat.add_assoc, r2]

theorem setVarDecClockLt {s : StackSemStateFiniteExact width C F} {link : Nat}
    {v : WordLocW width} (h0 : s.clock ≠ 0) :
    (StackSemStateOps.decClock (StackSemStateOps.setVar link v s)).clock < s.clock := by
  simp [StackSemStateOps.decClock, StackSemStateOps.setVar]; omega

/-- The returning call's evaluation equation, with the callee result exposed. -/
theorem callRetEval {s1 : StackSemStateFiniteExact width C F} {rp : HolProg width}
    {link l1 l2 : Nat} {handler : Option (HolProg width × Nat × Nat)}
    {prog : HolProg width} {res0 : Option (StackSemResult width)}
    {s2' : StackSemStateFiniteExact width C F} {r : Option (StackSemResult width)}
    {s2 : StackSemStateFiniteExact width C F}
    (e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) s1)) = (res0, s2'))
    (ev : (match StackSemControl.fixClock (StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1))
        (StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
          (StackSemStateOps.setVar link (.loc l1 l2) s1))) with
      | (some (.result x), s2) =>
          if x ≠ .loc l1 l2 then (some .error, s2) else StackSemEvaluate.evaluate (rp, s2)
      | (some (.exception x), s2) =>
          match handler with
          | none => (some (.exception x), s2)
          | some (h, hl1, hl2) =>
              if x ≠ .loc hl1 hl2 then (some .error, s2) else StackSemEvaluate.evaluate (h, s2)
      | (none, s2) => (some .error, s2)
      | (some (.break _), s2) => (some .error, s2)
      | (some (.continue _), s2) => (some .error, s2)
      | (res, s2) => (res, s2)) = (r, s2)) :
    (match (generalizing := false) res0 with
      | some (.result x) =>
          if x ≠ .loc l1 l2 then (some .error, s2') else StackSemEvaluate.evaluate (rp, s2')
      | some (.exception x) =>
          match handler with
          | none => (some (.exception x), s2')
          | some (h, hl1, hl2) =>
              if x ≠ .loc hl1 hl2 then (some .error, s2') else StackSemEvaluate.evaluate (h, s2')
      | none => (some .error, s2')
      | some (.break _) => (some .error, s2')
      | some (.continue _) => (some .error, s2')
      | res => (res, s2')) = (r, s2) := by
  rw [StackSemEvaluateClock.fixClockEvaluate, e2] at ev
  rcases res0 with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _⟩ <;>
    first | exact ev | (rcases handler with _ | ⟨h, hl1, hl2⟩ <;> exact ev)

/-- Unpacked `Vloc` conclusion. -/
theorem flattenConclVloc {p : HolProg width} {t : Bool} {x : StackSemResult width}
    {s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {n1 n2 : Nat}
    (hh : haltView (some x) = none) (hr : resultView x n cs bs = .vloc n1 n2)
    (h : FlattenConcl p t (some x) s2 n l cs bs t1) :
    ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      ∀ w, locToPc n1 n2 t2.code = some w → w = t2.pc ∧ stateRel s2 t2 := by
  obtain ⟨ck, t2, h⟩ := h
  refine ⟨ck, t2, ?_⟩
  revert h
  rw [hh]
  simp only [Option.map_some, hr]
  rintro ⟨a, b, c, d, e, f, g, -, w⟩
  exact ⟨a, b, c, d, e, f, g, w⟩

/-- Shared structure of a returning call: the prelude lines and the
continuation code. -/
theorem callRetPrelude {t : Bool} {rp : HolProg width} {link l1 l2 : Nat}
    {dest : Nat ⊕ Nat} {handler : Option (HolProg width × Nat × Nat)} {n l : Nat}
    {cs bs : List Nat} {xs : AppList (LabLineHOL width)} {nr1 : Bool} {m1 : Nat}
    (h1 : flattenHOL false rp n l cs bs = (xs, nr1, m1)) :
    ∃ rest, appListAppend (flattenHOL t (.call (some (rp, link, l1, l2)) dest handler)
        n l cs bs).1 = .labAsm (.locValue link (.lab l1 l2)) 0 [] 0 :: compileJumpHOL dest ::
          .label l1 l2 0 :: (appListAppend xs ++ rest) ∧
      (handler = none → rest = []) := by
  rcases handler with _ | ⟨hp, hs, hl⟩
  · exact ⟨[], by rw [flattenHOL]; simp [h1, appListAppendAppend, appListAppendList], fun _ => rfl⟩
  · rcases h2 : flattenHOL false hp n m1 cs bs with ⟨ys, nr2, m2⟩
    exact ⟨.labAsm (.jump (.lab n m2)) 0 [] 0 :: .label hs hl 0 ::
        (appListAppend ys ++ [.label n m2 0]),
      by rw [flattenHOL]; simp [h1, h2, appListAppendAppend, appListAppendList],
      fun h => by cases h⟩

/-- Result propagation through a returning call (results other than a
matching return or a handled exception). -/
theorem callPropagate {p p' : HolProg width} {t : Bool} {x : StackSemResult width}
    {s2 : StackSemStateFiniteExact width C F} {d n l l' : Nat} {cs bs : List Nat}
    {t1 tE : Flapjack.Compiler.Backend.LabSem.State width C F}
    (run1 : ∀ ck1, evaluate { t1 with clock := t1.clock + 1 + ck1 } =
      evaluate { tE with clock := tE.clock + ck1 })
    (f1 : tE.lenReg = t1.lenReg) (f2 : tE.ptrReg = t1.ptrReg) (f3 : tE.len2Reg = t1.len2Reg)
    (f4 : tE.ptr2Reg = t1.ptr2Reg) (f5 : tE.linkReg = t1.linkReg) (fcode : tE.code = t1.code)
    (hind : ∀ cs bs cs' bs' : List Nat, ∀ m m', resultView x m cs bs = resultView x m' cs' bs')
    (ph : FlattenConcl p true (some x) s2 d l' [] [] tE) :
    FlattenConcl p' t (some x) s2 n l cs bs t1 :=
  flattenConclComposeSome run1 f1 f2 f3 f4 f5 (by rw [fcode])
    (flattenConclResult (p' := p) (t' := true) (l' := 0) (h := ph) rfl (hind _ _ _ _ _ _))

end

end Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
