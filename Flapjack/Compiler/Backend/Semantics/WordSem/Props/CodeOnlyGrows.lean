import Flapjack.HolRef
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackMax
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd
import Flapjack.Misc.Sptree.Subspt

/-!
# `wordPropsScript.sml` 4589-4634: code growth and stack-size constancy

`evaluate_code_only_grows` is proved, as in HOL, by `evaluate_ind` from the
per-constructor cases, using the `*_const` field lemmas for `alloc`, `inst`,
`mem_store`, `jump_exc`, `share_inst`, `cut_state` and `pop_env`; only
`Install` changes the code, by `union`. `evaluate_NONE_stack_size_const`
follows from `evaluate_stack_swap` and `s_key_eq_stack_size`.
-/

namespace Flapjack

namespace WordSemStateFiniteExact

namespace CodeOnlyGrowsWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end CodeOnlyGrowsWitnesses

open CodeOnlyGrowsWitnesses

/-- `subspt` is reflexive (Flapjack infrastructure). -/
private theorem subRefl {α : Type} (t : Spt α) : sptSubspt t t :=
  (sptSubsptLookup t t).mpr fun _ _ h => h

private theorem subTrans {α : Type} {a b c : Spt α} (h1 : sptSubspt a b) (h2 : sptSubspt b c) :
    sptSubspt a c :=
  sptSubsptTrans a b c ⟨h1, h2⟩

private theorem alloc_code {width : Nat} [NeZero width] {C F : Type}
    (w : BitVec width) (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F) :
    (alloc w names s).2.code = s.code :=
  (allocConst w names s _ _ rfl).2.2.1

private theorem shareInst_code {width : Nat} [NeZero width] {C F : Type}
    (op : WordMemOp) (v : Nat) (c : BitVec width) (s : WordSemStateFiniteExact width C F) :
    (shareInst (rw := width) op v c s).2.code = s.code :=
  (shareInstConst op v c s _ _ rfl).2.2.2.2.1

private theorem cutState_code {width : Nat} [NeZero width] {C F : Type}
    {names : WordLangCutsetsHOL} {s next : WordSemStateFiniteExact width C F}
    (h : cutState names s = some next) : next.code = s.code := by
  obtain ⟨l, rfl⟩ := cutStateConst names s next h
  rfl

private theorem popEnv_code {width : Nat} [NeZero width] {C F : Type}
    {s next : WordSemStateFiniteExact width C F} (h : popEnv s = some next) :
    next.code = s.code := by
  have := popEnvConst s next h
  exact this.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

private theorem pushEnv_code {width : Nat} [NeZero width] {C F : Type}
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) : (pushEnv envs handler s).code = s.code := by
  cases handler with
  | none => rfl
  | some value => obtain ⟨n, prog, l1, l2⟩ := value; rfl

private theorem seq_code {width : Nat} [NeZero width] {C F : Type}
    (c1 c2 : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (hfirst : sptSubspt s.code (evaluate c1 s).2.code)
    (hsecond : ∀ res next, evaluate c1 s = (res, next) → res = none →
      sptSubspt next.code (evaluate c2 next).2.code) :
    sptSubspt s.code (evaluate (.seq c1 c2) s).2.code := by
  rw [evaluate, fix_clock_evaluate]
  cases hstep : evaluate c1 s with
  | mk result next =>
      rw [hstep] at hfirst
      cases result with
      | none => exact subTrans hfirst (hsecond none next hstep rfl)
      | some result => exact hfirst

private theorem loop_code {width : Nat} [NeZero width] {C F : Type}
    (names exitNames : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (hbody : ∀ v, cutState (names, .ln) s = some v →
      sptSubspt v.code (evaluate body v).2.code)
    (hrecur : ∀ v res next, cutState (names, .ln) s = some v →
      evaluate body v = (res, next) → wordSemContLoop res = true → next.clock ≠ 0 →
      sptSubspt (decClock next).code
        (evaluate (wordSemSTOP (.loop names body exitNames)) (decClock next)).2.code) :
    sptSubspt s.code (evaluate (.loop names body exitNames) s).2.code := by
  rw [evaluate]
  cases hcut : cutState (names, .ln) s with
  | none => exact subRefl _
  | some v =>
      dsimp only
      rw [fix_clock_evaluate]
      have hfirst := hbody v hcut
      rw [cutState_code hcut] at hfirst
      cases hstep : evaluate body v with
      | mk result next =>
          dsimp only
          rw [hstep] at hfirst
          by_cases hcont : wordSemContLoop result = true
          · simp only [if_pos hcont]
            by_cases hz : next.clock = 0
            · simpa only [hz, ↓reduceDIte, flushState] using hfirst
            · simp only [hz, ↓reduceDIte]
              exact subTrans hfirst (hrecur v result next hcut hstep hcont hz)
          · simp only [if_neg hcont]
            repeat' split
            all_goals first
              | exact hfirst
              | (rename_i hc; dsimp only; rw [cutState_code hc]; exact hfirst)

private theorem returningCall_code {width : Nat} [NeZero width] {C F : Type}
    (n : List Nat) (names : WordLangCutsetsHOL) (retHandler : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (xs args1 : List (WordLocW width))
    (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (hg : getVars args s = some xs) (hbad : ¬ wordSemBadDestArgs dest args = true)
    (hf : wordSemFindCode dest (wordSemAddRetLoc (some (n, names, retHandler, l1, l2)) xs)
      s.code s.stackSize = some (args1, prog, ss))
    (hnames : ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup))
    (henvs : wordSemCutEnvs names s.locals = some envs) (hz : s.clock ≠ 0)
    (hcallee : sptSubspt (callEnv args1 ss (pushEnv envs handler (decClock s))).code
      (evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s)))).2.code)
    (hreturn : ∀ x ys t popped,
      evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) =
        (some (.result x ys), t) →
      ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ n.length) → popEnv t = some popped →
      sptDomainEqUnion popped.locals envs.1 envs.2 →
      sptSubspt popped.code (evaluate retHandler (setVars n ys popped)).2.code)
    (hexception : ∀ x y t n' hprog l1' l2',
      evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) =
        (some (.exception x y), t) →
      handler = some (n', hprog, l1', l2') → x = .loc l1' l2' →
      sptDomainEqUnion t.locals envs.1 envs.2 →
      sptSubspt t.code (evaluate hprog (setVar n' y t)).2.code) :
    sptSubspt s.code
      (evaluate (.call (some (n, names, retHandler, l1, l2)) dest args handler) s).2.code := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht]
  simp only [hg, hbad, Bool.false_eq_true, if_false, hf, hnames, henvs, hz]
  have hstart : (callEnv args1 ss (pushEnv envs handler (decClock s))).code = s.code := by
    change (pushEnv envs handler (decClock s)).code = s.code
    rw [pushEnv_code]
    rfl
  rw [hstart] at hcallee
  rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with ⟨rc, t⟩
  rw [hcv] at hcallee
  rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
  · exact hcallee
  · simp only
    split
    · exact hcallee
    · rename_i hvalid
      cases hp : popEnv t with
      | none => exact hcallee
      | some popped =>
          dsimp only
          have hcode := popEnv_code hp
          split
          · rename_i hdom
            have hnext := hreturn x ys t popped hcv hvalid hp hdom
            rw [hcode] at hnext
            exact subTrans hcallee hnext
          · simpa only [hcode] using hcallee
  · cases hh : handler with
    | none => exact hcallee
    | some hv =>
        obtain ⟨n', hprog, l1', l2'⟩ := hv
        dsimp only
        split
        · exact hcallee
        · rename_i hloc
          split
          · rename_i hdom
            exact subTrans hcallee (hexception x y t n' hprog l1' l2' hcv hh
              (Classical.byContradiction hloc) hdom)
          · exact hcallee
  all_goals exact hcallee

private theorem tailCall_code {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args : List Nat) (s : WordSemStateFiniteExact width C F)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat)
    (hg : getVars args s = some xs) (hbad : ¬ wordSemBadDestArgs dest args = true)
    (hf : wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) s.code s.stackSize =
      some (args1, prog, ss)) (hz : s.clock ≠ 0)
    (hcallee : sptSubspt (callEnv args1 ss (decClock s)).code
      (evaluate prog (callEnv args1 ss (decClock s))).2.code) :
    sptSubspt s.code (evaluate (.call none dest args none) s).2.code := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht]
  simp only [hg, hbad, Bool.false_eq_true, if_false, hf, hz]
  rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨result, next⟩
  rw [hcv] at hcallee
  split <;> exact hcallee

private theorem mustTerminate_code {width : Nat} [NeZero width] {C F : Type}
    (body : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (hbody : s.termdep ≠ 0 →
      sptSubspt s.code (evaluate body
        { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 }).2.code) :
    sptSubspt s.code (evaluate (.mustTerminate body) s).2.code := by
  rw [evaluate]
  split
  · exact subRefl _
  · rename_i hdep
    have hsub := hbody hdep
    cases hstep : evaluate body
        { s with clock := wordSemMustTerminateLimit width, termdep := s.termdep - 1 } with
    | mk result next =>
        rw [hstep] at hsub
        dsimp only
        repeat' split
        all_goals first | exact subRefl _ | exact hsub

/-- `evaluate` never shrinks the code table: the per-program motive used for
`evaluate_ind` (Flapjack infrastructure for the tagged theorem below). -/
theorem evaluate_code_subspt {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    sptSubspt s.code (evaluate p s).2.code := by
  apply evaluate_ind (fun p s => sptSubspt s.code (evaluate p s).2.code) ?_ p s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; rw [evaluate]; exact subRefl _
  · intro n names s
    rw [evaluate]
    repeat' split
    all_goals first
      | exact subRefl _
      | (rw [alloc_code]; exact subRefl _)
  · intro t1 t2 addr offset words s
    rw [evaluate]
    repeat' split
    all_goals exact subRefl _
  · intro pri moves s
    rw [evaluate]
    repeat' split
    all_goals exact subRefl _
  · intro i s
    rw [evaluate]
    cases hi : inst i s with
    | none => exact subRefl _
    | some next => rw [(instConstFull i s next hi).1]; exact subRefl _
  · intro v exp s
    rw [evaluate]
    repeat' split
    all_goals exact subRefl _
  · intro v name s
    rw [evaluate]
    repeat' split
    all_goals exact subRefl _
  · intro v exp s
    rw [evaluate]
    repeat' split
    all_goals exact subRefl _
  · intro b dst src s
    rw [evaluate]
    repeat' split
    all_goals exact subRefl _
  · intro exp v s
    rw [evaluate]
    repeat' split
    all_goals first
      | exact subRefl _
      | (rename_i hm; dsimp only; rw [(memStoreConst _ _ _ _ hm).2.2.2.2.2.2.2.2.1]
         exact subRefl _)
  · intro s
    rw [evaluate]
    split <;> exact subRefl _
  · exact mustTerminate_code
  · intro c1 c2 s ih
    exact seq_code c1 c2 s ih.2
      (fun res next heval hnone => ih.1 res next ⟨heval.symm, hnone⟩)
  · intro n ms s
    rw [evaluate]
    repeat' split
    all_goals exact subRefl _
  · intro n s
    rw [evaluate]
    repeat' split
    all_goals first
      | exact subRefl _
      | (rename_i hj; dsimp only; rw [(jumpExcConst _ _ _ hj).2.2.2.2.1]; exact subRefl _)
  · intro k s; rw [evaluate]; exact subRefl _
  · intro k s; rw [evaluate]; exact subRefl _
  · intro cmp r1 ri c1 c2 s ih
    rw [evaluate]
    repeat' split
    all_goals first
      | exact subRefl _
      | exact ih.1 (some _) (some _) _ _ true
          ⟨by rw [‹getVar r1 s = some _›, ‹getVarImm ri s = some _›], rfl, rfl,
            ‹wordSemWordCmp _ _ _ = some true›, rfl⟩
      | exact ih.2 (some _) (some _) _ _ false
          ⟨by rw [‹getVar r1 s = some _›, ‹getVarImm ri s = some _›], rfl, rfl,
            ‹wordSemWordCmp _ _ _ = some false›, Bool.noConfusion⟩
  · intro names body exitNames s ih
    exact loop_code names exitNames body s ih.2
      (fun v res next hcut heval hcont hz => ih.1 v res next ⟨hcut, heval.symm, hcont, hz⟩)
  · intro r l1 s
    rw [evaluate]
    split <;> exact subRefl _
  · intro ptr len dptr dlen names s
    rw [evaluate]
    repeat' split
    all_goals dsimp only
    all_goals repeat' split
    all_goals first
      | exact subRefl _
      | exact sptSubsptUnion _ _
  · intro r1 r2 s
    rw [evaluate]
    repeat' split
    all_goals exact subRefl _
  · intro r1 r2 s
    rw [evaluate]
    repeat' split
    all_goals exact subRefl _
  · intro fi p1 l1 p2 l2 names s
    unfold evaluate
    repeat' split
    all_goals exact subRefl _
  · intro op v exp s
    rw [evaluate]
    repeat' split
    all_goals first
      | exact subRefl _
      | (rw [shareInst_code]; exact subRefl _)
  · intro ret dest args handler s ih
    rcases ih with ⟨hreturn, hexception, hcallee, htail⟩
    have hcall := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    cases hg : getVars args s with
    | none => rw [hcall]; simp only [hg]; exact subRefl _
    | some xs =>
      by_cases hbad : wordSemBadDestArgs dest args = true
      · rw [hcall]; simp only [hg, hbad, ↓reduceIte]; exact subRefl _
      · cases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        | none =>
          rw [hcall]; simp only [hg, hbad, hf]; exact subRefl _
        | some triple =>
          obtain ⟨args1, prog, ss⟩ := triple
          cases ret with
          | none =>
            cases handler with
            | some handler =>
              rw [hcall]; simp only [hg, hbad, hf]; exact subRefl _
            | none =>
              by_cases hz : s.clock = 0
              · rw [hcall]; simp only [hg, hbad, ↓reduceIte, hf, hz]; exact subRefl _
              · apply tailCall_code dest args s xs args1 prog ss hg hbad hf hz
                exact htail xs (args1, prog, ss) args1 (prog, ss) prog ss
                  ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, hz⟩
          | some ret =>
            obtain ⟨n, names, retHandler, l1, l2⟩ := ret
            by_cases hnames : sptDomainEmpty names.1 ∨ ¬ n.Nodup
            · rw [hcall]; simp only [hg, hbad, ↓reduceIte, hf, hnames]; exact subRefl _
            · cases he : wordSemCutEnvs names s.locals with
              | none =>
                rw [hcall]; simp only [hg, hbad, ↓reduceIte, hf, hnames, he]; exact subRefl _
              | some envs =>
                by_cases hz : s.clock = 0
                · rw [hcall]; simp only [hg, hbad, ↓reduceIte, hf, hnames, he, hz]
                  exact subRefl _
                · apply returningCall_code n names retHandler l1 l2 dest args handler
                    s xs args1 prog ss envs hg hbad hf hnames he hz
                  · exact hcallee xs (args1, prog, ss) args1 (prog, ss) prog ss
                      (n, names, retHandler, l1, l2) n (names, retHandler, l1, l2) names
                      (retHandler, l1, l2) retHandler (l1, l2) l1 l2 envs
                      ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz⟩
                  · intro x ys t popped hev hv hp hd
                    exact hreturn xs (args1, prog, ss) args1 (prog, ss) prog ss
                      (n, names, retHandler, l1, l2) n (names, retHandler, l1, l2) names
                      (retHandler, l1, l2) retHandler (l1, l2) l1 l2 envs
                      (some (.result x ys)) t (.result x ys) x ys popped
                      ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz,
                        hev, rfl, rfl, hv, hp, hd⟩
                  · intro x y t n' hprog l1' l2' hev hh hl hd
                    exact hexception xs (args1, prog, ss) args1 (prog, ss) prog ss
                      (n, names, retHandler, l1, l2) n (names, retHandler, l1, l2) names
                      (retHandler, l1, l2) retHandler (l1, l2) l1 l2 envs
                      (some (.exception x y)) t (.exception x y) x y
                      (n', hprog, l1', l2') n' (hprog, l1', l2') hprog (l1', l2') l1' l2'
                      ⟨hg, hbad, hf, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hnames, he, hz,
                        hev, rfl, rfl, hh, rfl, rfl, rfl, hl, hd⟩

/-- Full original `evaluate_code_only_grows` (`wordPropsScript.sml:4589-4626`):
`!p s r t. evaluate (p,s) = (r,t) ==> subspt s.code t.code`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_code_only_grows {width : Nat} [NeZero width] {C F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
      (r : Option (WordSemResult width)) (t : WordSemStateFiniteExact width C F),
      evaluate p s = (r, t) → sptSubspt s.code t.code := by
  intro p s r t h
  have := evaluate_code_subspt p s
  rw [h] at this
  exact this

end WordSemStateFiniteExact

namespace WordSemStackEq

open WordSemStateFiniteExact

/-- Full original `evaluate_NONE_stack_size_const` (`wordPropsScript.sml:4628-4634`):
`!p s t. evaluate (p,s) = (NONE,t) ==> stack_size t.stack = stack_size s.stack`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluate_NONE_stack_size_const {width : Nat} [NeZero width] {C F : Type} :
    ∀ (p : WordLangProgHOL (BitVec width)) (s t : WordSemStateFiniteExact width C F),
      evaluate p s = (none, t) → wordSemStackSize t.stack = wordSemStackSize s.stack := by
  intro p s t h
  have hs := evaluateStackSwap p s
  unfold stackSwapPost at hs
  rw [h] at hs
  exact (sKeyEqStackSize _ _ hs.1).symm

end WordSemStackEq

end Flapjack
