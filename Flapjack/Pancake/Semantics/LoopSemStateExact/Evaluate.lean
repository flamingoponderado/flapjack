import Flapjack.Pancake.Semantics.LoopSemStateExact.ShMem
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Compiler.Encoders.Asm

namespace Flapjack
namespace LoopSemStateFiniteExact

theorem cutState_clock {width : Nat} [NeZero width] {F : Type} {live : NumSet}
    {s s1 : LoopSemStateFiniteExact width F} (h : cutState live s = some s1) :
    s1.clock = s.clock :=
  cutState_some_clock h

theorem cutRes_none_clock {width : Nat} [NeZero width] {F : Type} {live : NumSet}
    {s s' : LoopSemStateFiniteExact width F} (h : cutRes live (none, s) = (none, s')) :
    s'.clock < s.clock := by
  simp only [cutRes] at h
  cases hc : cutState live s with
  | none => rw [hc] at h; simp at h
  | some s1 =>
    rw [hc] at h; simp only at h
    split at h
    · simp at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h
      simp only [decClock]; have := cutState_clock hc; omega

theorem fixClock_clock_le {width : Nat} [NeZero width] {F : Type} {β : Type}
    (old : LoopSemStateFiniteExact width F) (step : β × LoopSemStateFiniteExact width F) :
    (fixClock old step).2.clock ≤ old.clock := by
  simp only [fixClock]; split <;> omega

theorem fixClock_eq_clock_le {width : Nat} [NeZero width] {F : Type} {β : Type}
    {old s' : LoopSemStateFiniteExact width F} {step : β × LoopSemStateFiniteExact width F} {r : β}
    (h : fixClock old step = (r, s')) : s'.clock ≤ old.clock := by
  have := fixClock_clock_le old step; rw [h] at this; exact this

theorem lexLt {a a' b b' : Nat} (ha : a' ≤ a) (hb : b' < b) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := by
  rcases Nat.lt_or_eq_of_le ha with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ hb

theorem lexLtClock {a a' b b' : Nat} (ha : a' < a) :
    Prod.Lex (· < ·) (· < ·) (a', b') (a, b) := Prod.Lex.left _ _ ha

namespace LoopEvaluateFiniteSupport

/-- Local same-module witness for the canonical finite-support
`LoopSemStateFiniteExact` carrier used by the qualified `evaluate_def` port below
(re-exports the checked witness of `Flapjack/Pancake/Semantics/LoopSemStateExact.lean`). -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {F : Type} :
    (∀ (state : LoopSemStateBroad width F) (h : state.FiniteSupport),
        (LoopSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : LoopSemStateFiniteExact width F,
        LoopSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.LoopSemStateFiniteExact.holFmapAsFiniteSupportWitness

end LoopEvaluateFiniteSupport

open Flapjack.Compiler.Encoders.Asm in
/-- Exact HOL `loopSem$evaluate_def` (`loopSemScript.sml:278-440`) over
    `HolLoopProg` and `LoopSemStateFiniteExact`, clause for clause.  HOL proves
    termination by `inv_image (measure I LEX measure (prog_size (K 0)))
    (\\(xs,s). (s.clock,xs))`; this definition uses the same lexicographic
    `(s.clock, sizeOf prog)` measure.  `fix_clock` supplies the non-increasing
    clock after `Seq`, `Loop` and non-tail `Call` sub-evaluations and `cut_res`
    the strict decrease before re-entering `Loop` or a callee, exactly as in the
    HOL termination proof.

    The only presentational differences are: `If` is `if b then cut_res l
    (evaluate c1) else cut_res l (evaluate c2)` (HOL: `cut_res l (evaluate (if b
    then c1 else c2, s))`, equal by `apply_ite`); `res = NONE` / `res ≠ NONE`
    tests are the corresponding `Option` patterns; `l1 ∈ domain s.code` is
    `(lookup l1 s.code).isSome`; HOL `w2w` is `BitVec.setWidth`; and `is_load`
    over the Crep/Loop `memop` carrier is `crepIsLoadMemOp`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "evaluate_def" 278
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
def evaluate {width : Nat} [NeZero width] {F : Type} :
    HolLoopProg width → LoopSemStateFiniteExact width F →
      Option (LoopResultExact width) × LoopSemStateFiniteExact width F
  | .skip, s => (none, s)
  | .fail, s => (some .error, s)
  | .assign v exp, s =>
      match eval s exp with
      | none => (some .error, s)
      | some w => (none, setVar v w s)
  | .primitive lhss pop rhss, s =>
      match getVars rhss s with
      | some ws =>
          match loopPrimop pop ws with
          | some resWs =>
              if lhss.length = resWs.length then (none, setVars lhss resWs s)
              else (some .error, s)
          | none => (some .error, s)
      | none => (some .error, s)
  | .arith arith, s =>
      match loopArith s arith with
      | none => (some .error, s)
      | some s' => (none, s')
  | .store exp v, s =>
      match eval s exp, sptLookup v s.locals with
      | some (.word adr), some w =>
          match memStore adr w s with
          | some st => (none, st)
          | none => (some .error, s)
      | _, _ => (some .error, s)
  | .setGlobal dst exp, s =>
      match eval s exp with
      | some w => (none, setGlobals dst w s)
      | _ => (some .error, s)
  | .load32 a v, s =>
      match sptLookup a s.locals with
      | some (.word w) =>
          match memLoad32Exact s.memory s.mdomain s.be w with
          | some b => (none, setVar v (.word (b.setWidth width)) s)
          | _ => (some .error, s)
      | _ => (some .error, s)
  | .loadByte a v, s =>
      match sptLookup a s.locals with
      | some (.word w) =>
          match memLoadByteAuxExact s.memory s.mdomain s.be w with
          | some b => (none, setVar v (.word (b.setWidth width)) s)
          | _ => (some .error, s)
      | _ => (some .error, s)
  | .store32 a w, s =>
      match sptLookup a s.locals, sptLookup w s.locals with
      | some (.word w), some (.word b) =>
          match memStore32Exact s.memory s.mdomain s.be w (b.setWidth 32) with
          | some m => (none, { s with memory := m })
          | _ => (some .error, s)
      | _, _ => (some .error, s)
  | .storeByte a w, s =>
      match sptLookup a s.locals, sptLookup w s.locals with
      | some (.word w), some (.word b) =>
          match memStoreByteAuxExact s.memory s.mdomain s.be w (b.setWidth 8) with
          | some m => (none, { s with memory := m })
          | _ => (some .error, s)
      | _, _ => (some .error, s)
  | .seq c1 c2, s =>
      match _h : fixClock s (evaluate c1 s) with
      | (none, s1) => evaluate c2 s1
      | (res, s1) => (res, s1)
  | .ite cmp r1 ri c1 c2 liveOut, s =>
      match sptLookup r1 s.locals, getVarImm ri s with
      | some (.word x), some (.word y) =>
          if wordCmpHOL cmp x y then cutRes liveOut (evaluate c1 s)
          else cutRes liveOut (evaluate c2 s)
      | _, _ => (some .error, s)
  | .mark p, s => evaluate p s
  | .break k, s => (some (.break k), s)
  | .continue k, s => (some (.continue k), s)
  | .loop liveIn body liveOut, s =>
      match _hc : cutRes liveIn (none, s) with
      | (none, s1) =>
          match _hb : fixClock s1 (evaluate body s1) with
          | (none, s2) => evaluate (.loop liveIn body liveOut) s2
          | (some (.continue 0), s2) => evaluate (.loop liveIn body liveOut) s2
          | (some (.break 0), s2) => cutRes liveOut (none, s2)
          | (res, s2) => (exitLoop res, s2)
      | res => res
  | .raise n, s =>
      match sptLookup n s.locals with
      | none => (some .error, s)
      | some w => (some (.exception w), callEnv [] s)
  | .return ns, s =>
      match getVars ns s with
      | some vs => (some (.result vs), callEnv [] s)
      | _ => (some .error, s)
  | .shMem op v ad, s =>
      match eval s ad with
      | some (.word addr) =>
          if crepIsLoadMemOp op then
            match sptLookup v s.locals with
            | some _ => shMemOp op v addr s
            | _ => (some .error, s)
          else
            match sptLookup v s.locals with
            | some (.word _) => shMemOp op v addr s
            | _ => (some .error, s)
      | _ => (some .error, s)
  | .tick, s =>
      if s.clock = 0 then (some .timeOut, { s with locals := .ln })
      else (none, decClock s)
  | .locValue r l1, s =>
      if (sptLookup l1 s.code).isSome then (none, setVar r (.loc l1 0) s)
      else (some .error, s)
  | .call ret dest argvars handler, s =>
      match getVars argvars s with
      | none => (some .error, s)
      | some argvals =>
          match findCode dest argvals s.code with
          | none => (some .error, s)
          | some (env, prog) =>
              match ret with
              | none =>
                  if handler.isSome then (some .error, s) else
                  if _hz : s.clock = 0 then (some .timeOut, { s with locals := .ln })
                  else
                    match evaluate prog { decClock s with locals := env } with
                    | (none, s') => (some .error, s')
                    | (some (.continue _), s') => (some .error, s')
                    | (some (.break _), s') => (some .error, s')
                    | (some res, s') => (some res, s')
              | some (ns, live) =>
                  if ¬ ns.Nodup then (some .error, s) else
                  match _hc : cutRes live (none, s) with
                  | (none, s1) =>
                      match _hf : fixClock { s1 with locals := env }
                          (evaluate prog { s1 with locals := env }) with
                      | (some (.result retvs), st) =>
                          if retvs.length ≠ ns.length then (some .error, st) else
                          match handler with
                          | none => (none, setVars ns retvs { st with locals := s1.locals })
                          | some (_, _, r, liveOut) =>
                              cutRes liveOut
                                (evaluate r (setVars ns retvs { st with locals := s1.locals }))
                      | (some (.exception exn), st) =>
                          match handler with
                          | none => (some (.exception exn), { st with locals := .ln })
                          | some (n, h, _, liveOut) =>
                              cutRes liveOut
                                (evaluate h (setVar n exn { st with locals := s1.locals }))
                      | (some (.continue _), st) => (some .error, st)
                      | (some (.break _), st) => (some .error, st)
                      | (none, st) => (some .error, st)
                      | res => res
                  | res => res
  | .ffi idx ptr1 len1 ptr2 len2 cutset, s =>
      match sptLookup len1 s.locals, sptLookup ptr1 s.locals, sptLookup len2 s.locals,
          sptLookup ptr2 s.locals, cutState cutset s with
      | some (.word w), some (.word w2), some (.word w3), some (.word w4), some s' =>
          match readBytearrayWordHOL w2 w.toNat (memLoadByteAuxExact s'.memory s'.mdomain s'.be),
              readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s'.memory s'.mdomain s'.be) with
          | some bytes, some bytes2 =>
              match callFFIHOL s'.ffi (.extCall idx) bytes bytes2 with
              | .final outcome => (some (.finalFfi outcome), callEnv [] s')
              | .ret newFfi newBytes =>
                  (none, { s' with memory := writeBytearrayExact w4 newBytes s'.memory s'.mdomain s'.be,
                                   ffi := newFfi })
          | _, _ => (some .error, s')
      | _, _, _, _, _ => (some .error, s)
termination_by prog s => (s.clock, sizeOf prog)
decreasing_by
  all_goals try simp only [setVars, setVar, decClock]
  all_goals first
    | exact lexLt (Nat.le_refl _) (by simp +arith)
    | exact lexLt (fixClock_eq_clock_le ‹_›) (by simp +arith)
    | exact lexLtClock (cutRes_none_clock ‹_›)
    | exact lexLtClock (Nat.lt_of_le_of_lt (fixClock_eq_clock_le ‹_›) (cutRes_none_clock ‹_›))
    | exact lexLtClock (by omega)
    | exact lexLtClock (by
        have h1 := fixClock_eq_clock_le _hf; have h2 := cutRes_none_clock _hc
        simp only at h1; omega)

end LoopSemStateFiniteExact
end Flapjack

namespace Flapjack
namespace LoopSemStateFiniteExact

theorem memStore_clock {width : Nat} [NeZero width] {F : Type} {a : BitVec width}
    {v : WordLocW width} {s st : LoopSemStateFiniteExact width F}
    (h : memStore a v s = some st) : st.clock = s.clock := by
  unfold memStore at h; split at h <;> simp at h; subst h; rfl

theorem loopArith_clock {width : Nat} [NeZero width] {F : Type} {op : LoopArith}
    {s st : LoopSemStateFiniteExact width F}
    (h : loopArith s op = some st) : st.clock = s.clock := by
  cases op <;> simp only [loopArith] at h <;> split at h <;> (try split at h) <;>
    simp only [Option.some.injEq, reduceCtorEq] at h <;> (subst h; rfl)

theorem shMemLoad_clock {width : Nat} [NeZero width] {F : Type} (v : Nat)
    (a : BitVec width) (nb : Nat) (s : LoopSemStateFiniteExact width F) :
    (shMemLoad v a nb s).2.clock = s.clock := by
  unfold shMemLoad; split <;> split <;> (try split) <;> rfl

theorem shMemStore_clock {width : Nat} [NeZero width] {F : Type} (v : Nat)
    (a : BitVec width) (nb : Nat) (s : LoopSemStateFiniteExact width F) :
    (shMemStore v a nb s).2.clock = s.clock := by
  unfold shMemStore; split <;> (try split) <;> (try split) <;> (try split) <;> rfl

theorem shMemOp_clock {width : Nat} [NeZero width] {F : Type} (op : CrepMemOp) (v : Nat)
    (a : BitVec width) (s : LoopSemStateFiniteExact width F) :
    (shMemOp op v a s).2.clock = s.clock := by
  cases op <;> simp only [shMemOp, shMemLoad_clock, shMemStore_clock]

theorem cutRes_clock_le {width : Nat} [NeZero width] {F : Type} (live : NumSet)
    (r : Option (LoopResultExact width) × LoopSemStateFiniteExact width F) :
    (cutRes live r).2.clock ≤ r.2.clock := by
  obtain ⟨res, s⟩ := r
  cases res with
  | some _ => simp [cutRes]
  | none =>
    simp only [cutRes]
    cases hc : cutState live s with
    | none => simp
    | some s1 =>
      simp only; have := cutState_clock hc
      split <;> simp [decClock] <;> omega

theorem evaluate_clock_snd {width : Nat} [NeZero width] {F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    (evaluate p s).2.clock ≤ s.clock := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock, sizeOf p) = x → (evaluate p s).2.clock ≤ s.clock := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx
      have ih : ∀ (p' : HolLoopProg width) (s' : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (s'.clock, sizeOf p') (s.clock, sizeOf p) →
            (evaluate p' s').2.clock ≤ s'.clock :=
        fun p' s' hlt => ih0 _ (hx ▸ hlt) p' s' rfl
      clear ih0 hx
      have ihEq : ∀ (p' : HolLoopProg width) (s' : LoopSemStateFiniteExact width F) r t,
          evaluate p' s' = (r, t) →
          Prod.Lex (· < ·) (· < ·) (s'.clock, sizeOf p') (s.clock, sizeOf p) →
            t.clock ≤ s'.clock := by
        intro p' s' r t he hl; have := ih p' s' hl; rw [he] at this; exact this
      cases p <;> rw [evaluate]
      all_goals (repeat' split)
      all_goals (try simp only [setVar, setVars, setGlobals, callEnv, decClock, shMemOp_clock])
      all_goals (try (exact Nat.le_refl _))
      all_goals (try refine Nat.le_trans (cutRes_clock_le _ _) ?_)
      all_goals (try dsimp only)
      all_goals (try have h_ms := memStore_clock ‹_›)
      all_goals (try have h_la := loopArith_clock ‹_›)
      all_goals (try have h_fc := fixClock_eq_clock_le ‹_›)
      all_goals (try have h_cr := cutRes_none_clock ‹_›)
      all_goals (try have h_cs := cutState_clock ‹_›)
      all_goals (try have h_ev := ihEq _ _ _ _ ‹evaluate _ _ = (_, _)› ?_)
      all_goals (try refine Nat.le_trans (ih _ _ ?_) ?_)
      all_goals (try simp only [decClock] at *)
      all_goals first
        | omega
        | exact lexLt (by omega) (by simp +arith)
        | exact lexLtClock (by omega)
        | (refine Nat.le_trans (fixClock_clock_le _ _) ?_; dsimp only; omega)
  exact key _ p s rfl

/-- Exact HOL `evaluate_clock` (`loopSemScript.sml:458-486`):
    `!xs s1 vs s2. (evaluate (xs,s1) = (vs,s2)) ==> s2.clock <= s1.clock`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "evaluate_clock"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem evaluate_clock {width : Nat} [NeZero width] {F : Type}
    (xs : HolLoopProg width) (s1 : LoopSemStateFiniteExact width F)
    (vs : Option (LoopResultExact width)) (s2 : LoopSemStateFiniteExact width F)
    (h : evaluate xs s1 = (vs, s2)) : s2.clock ≤ s1.clock := by
  have := evaluate_clock_snd xs s1; rw [h] at this; exact this

/-- Exact HOL `fix_clock_evaluate` (`loopSemScript.sml:488-493`):
    `fix_clock s (evaluate (c1,s)) = evaluate (c1,s)`. -/
@[hol "cakeml/pancake/semantics/loopSemScript.sml" "fix_clock_evaluate"
  (fmap_as_finite_support := [globals]) (words_as_type_indexed_bitvec)]
theorem fix_clock_evaluate {width : Nat} [NeZero width] {F : Type}
    (c1 : HolLoopProg width) (s : LoopSemStateFiniteExact width F) :
    fixClock s (evaluate c1 s) = evaluate c1 s := by
  have hle := evaluate_clock_snd c1 s
  generalize evaluate c1 s = e at hle ⊢
  obtain ⟨r, t⟩ := e
  simp only [fixClock] at hle ⊢
  split
  · omega
  · rfl

end LoopSemStateFiniteExact
end Flapjack
