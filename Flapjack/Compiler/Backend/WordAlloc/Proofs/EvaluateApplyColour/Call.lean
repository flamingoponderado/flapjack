import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.Alloc
import Flapjack.Compiler.Backend.WordAlloc.Proofs.PermuteSwap
import Flapjack.Compiler.Backend.WordAlloc.Proofs.Updates
import Flapjack.Compiler.Backend.WordAlloc.Proofs.CutNames
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EnvFrame
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateStackSwap
import Flapjack.Compiler.Backend.Semantics.WordSem.EvaluateInd

/-!
# `evaluate_apply_colour` `Call` case

The `Call` case of `word_allocProofScript.sml:1105-1130` `evaluate_apply_colour`
(`Resume evaluate_apply_colour[Call]`, `word_allocProofScript.sml:1449-1809`).
Tail calls run the callee on identical source and coloured states; returning
calls push related frames (`push_env_s_val_eq`), choose the callee's oracle by
`permute_swap_lemma4`, transport the coloured run by `evaluate_stack_swap`, and
apply the induction hypotheses to the return and exception handlers. The
untagged helpers are Flapjack proof infrastructure for the tagged case.
-/

namespace Flapjack.WordAlloc

open WordSemStateFiniteExact WordSemStackEq

namespace EvaluateApplyColourCallWitnesses

/-- Canonical imported WordSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
      (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end EvaluateApplyColourCallWitnesses

open EvaluateApplyColourCallWitnesses

section CallCase

variable {width : Nat} [NeZero width] {C F : Type}

/-- `word_state_eq_rel` is reflexive (Flapjack infrastructure). -/
theorem wsrRefl (s : WordSemStateFiniteExact width C F) : wordStateEqRel s s := by
  unfold wordStateEqRel; simp

/-- Related states with the coloured oracle and locals are equal (Flapjack
infrastructure: `word_state_eq_rel` covers every other field). -/
theorem wsrEq {s t : WordSemStateFiniteExact width C F} (h : wordStateEqRel s t) :
    { s with permute := t.permute, locals := t.locals } = t := by
  unfold wordStateEqRel at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  cases t
  simp only at *
  subst_vars
  rfl

/-- The callee environment only depends on the related fields. -/
theorem callEnv_decClock_wsr {s t : WordSemStateFiniteExact width C F} (h : wordStateEqRel s t)
    (a : List (WordLocW width)) (ss : Option Nat) :
    WordSemStateFiniteExact.callEnv a ss (decClock t) =
      WordSemStateFiniteExact.callEnv a ss (decClock { s with permute := t.permute }) := by
  rw [← wsrEq h]
  rfl

open Classical in
/-- The continuation of a returning call after its callee run `r` (the
`evaluate_def` `Call` clause past the callee). Flapjack infrastructure. -/
noncomputable def callRetTail (n : List Nat) (rh : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (r : Option (WordSemResult width) × WordSemStateFiniteExact width C F) :
    Option (WordSemResult width) × WordSemStateFiniteExact width C F :=
  match r with
  | (some (.result x ys), s2) =>
      if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then (some .error, s2)
      else
        match popEnv s2 with
        | none => (some .error, s2)
        | some s1 =>
            if sptDomainEqUnion s1.locals envs.1 envs.2 then
              evaluate rh (WordSemStateFiniteExact.setVars n ys s1)
            else (some .error, s1)
  | (some (.exception x y), s2) =>
      match handler with
      | none => (some (.exception x y), s2)
      | some (n, hprog, l1, l2) =>
          if x ≠ .loc l1 l2 then (some .error, s2)
          else if sptDomainEqUnion s2.locals envs.1 envs.2 then
            evaluate hprog (WordSemStateFiniteExact.setVar n y s2)
          else (some .error, s2)
  | (none, s) => (some .error, s)
  | (some (.break _), s) => (some .error, s)
  | (some (.continue _), s) => (some .error, s)
  | res => res

/-- A returning call past its guards runs the callee and continues with
`callRetTail`. -/
theorem evaluate_call_ret_eq (s : WordSemStateFiniteExact width C F)
    (n : List Nat) (names : WordLangCutsetsHOL) (rh : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (xv args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (hgv : WordSemStateFiniteExact.getVars args s = some xv)
    (hbad : ¬ wordSemBadDestArgs dest args = true)
    (hfc : wordSemFindCode dest (wordSemAddRetLoc (some (n, names, rh, l1, l2)) xv) s.code
      s.stackSize = some (args1, prog, ss))
    (hg : ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup))
    (hce : wordSemCutEnvs names s.locals = some envs) (hz : ¬ s.clock = 0) :
    evaluate (.call (some (n, names, rh, l1, l2)) dest args handler) s =
      callRetTail n rh l1 l2 envs handler
        (evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))) := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)
    ).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht, hgv]
  dsimp only
  rw [if_neg hbad, hfc]
  dsimp only
  rw [if_neg hg, hce]
  dsimp only
  rw [if_neg hz]
  rfl

/-- The source oracle of a returning call: `perm 0` orders the pushed frame,
`perm''` drives the callee. -/
def ppPerm (perm perm'' : Nat → Nat → Nat) : Nat → Nat → Nat :=
  fun k => if k = 0 then perm 0 else perm'' (k - 1)

/-- `env_to_list` under `ppPerm` (Flapjack infrastructure). -/
theorem envToList_ppPerm (x : Spt (WordLocW width)) (perm perm'' : Nat → Nat → Nat) :
    wordSemEnvToList x (ppPerm perm perm'') = ((wordSemEnvToList x perm).1, perm'') := by
  simp only [wordSemEnvToList, ppPerm, Nat.add_one_ne_zero, ↓reduceIte,
    Nat.add_sub_cancel]

/-- Pushing under `ppPerm` leaves `perm''` as the callee oracle (Flapjack
infrastructure). -/
theorem pushEnv_ppPerm (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (t : WordSemStateFiniteExact width C F) (perm perm'' : Nat → Nat → Nat) :
    pushEnv envs h { t with permute := ppPerm perm perm'' } =
      { pushEnv envs h { t with permute := perm } with permute := perm'' } := by
  rcases h with _ | ⟨_, _, _, _⟩ <;>
    (simp only [pushEnv]; rw [envToList_ppPerm])

/-- The fields of a callee environment that come from the caller. -/
theorem callEnv_pushEnv_fields (a : List (WordLocW width)) (ss : Option Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (t : WordSemStateFiniteExact width C F) :
    let S := WordSemStateFiniteExact.callEnv a ss (pushEnv envs h t)
    S.fpRegs = t.fpRegs ∧ S.store = t.store ∧ S.localsSize = ss ∧ S.stackLimit = t.stackLimit ∧
      S.stackMax = wordSemOptionMax (wordSemOptionMax t.stackMax
        (wordSemStackSize (pushEnv envs h t).stack))
        (wordSemOptionAdd (wordSemStackSize (pushEnv envs h t).stack) ss) ∧
      S.stackSize = t.stackSize ∧ S.memory = t.memory ∧ S.mdomain = t.mdomain ∧
      S.shMdomain = t.shMdomain ∧ S.gcFun = t.gcFun ∧
      S.handler = (match h with | none => t.handler | some _ => t.stack.length) ∧
      S.clock = t.clock ∧ S.code = t.code ∧ S.ffi = t.ffi ∧ S.be = t.be ∧
      S.termdep = t.termdep ∧ S.compile = t.compile ∧ S.compileOracle = t.compileOracle ∧
      S.codeBuffer = t.codeBuffer ∧ S.dataBuffer = t.dataBuffer ∧
      S.locals = sptFromList2 a ∧ S.stack = (pushEnv envs h t).stack ∧
      S.permute = (wordSemEnvToList envs.2 t.permute).2 := by
  rcases h with _ | ⟨_, _, _, _⟩ <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- States agreeing on every field but the stack, locals and oracle. -/
theorem stateEq_of_fields (s t : WordSemStateFiniteExact width C F)
    (h : t.fpRegs = s.fpRegs ∧ t.store = s.store ∧ t.localsSize = s.localsSize ∧
      t.stackLimit = s.stackLimit ∧ t.stackMax = s.stackMax ∧ t.stackSize = s.stackSize ∧
      t.memory = s.memory ∧ t.mdomain = s.mdomain ∧ t.shMdomain = s.shMdomain ∧
      t.gcFun = s.gcFun ∧ t.handler = s.handler ∧ t.clock = s.clock ∧ t.code = s.code ∧
      t.ffi = s.ffi ∧ t.be = s.be ∧ t.termdep = s.termdep ∧ t.compile = s.compile ∧
      t.compileOracle = s.compileOracle ∧ t.codeBuffer = s.codeBuffer ∧
      t.dataBuffer = s.dataBuffer) :
    { s with permute := t.permute, locals := t.locals, stack := t.stack } = t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := h
  cases t
  simp only at *
  subst_vars
  rfl

/-- HOL's `stack_swap` step of the `Call` case: the coloured callee state is the
source callee state with the coloured stack. -/
theorem calleeSwap {st cst : WordSemStateFiniteExact width C F} (hs : wordStateEqRel st cst)
    (x1 x2 y1 y2 : Spt (WordLocW width))
    (handler h' : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (hhs : handler.isSome = h'.isSome) (perm : Nat → Nat → Nat)
    (hperm : (wordSemEnvToList x2 perm).2 = (wordSemEnvToList y2 cst.permute).2)
    (hsv : sValEq (pushEnv (x1, x2) handler { decClock st with permute := perm }).stack
      (pushEnv (y1, y2) h' (decClock cst)).stack)
    (a : List (WordLocW width)) (ss : Option Nat) :
    { WordSemStateFiniteExact.callEnv a ss (pushEnv (x1, x2) handler
        { decClock st with permute := perm }) with
      stack := (WordSemStateFiniteExact.callEnv a ss (pushEnv (y1, y2) h' (decClock cst))).stack } =
      WordSemStateFiniteExact.callEnv a ss (pushEnv (y1, y2) h' (decClock cst)) := by
  have hS := callEnv_pushEnv_fields a ss (x1, x2) handler { decClock st with permute := perm }
  have hC := callEnv_pushEnv_fields a ss (y1, y2) h' (decClock cst)
  simp only at hS hC
  have hsz := sValEqStackSize _ _ hsv
  have hlen := sValEqLength _ _ hsv
  unfold wordStateEqRel at hs
  obtain ⟨efp, est, els, estk, eslim, esmax, essz, emem, emd, esmd, egc, eh, eclk, ecode, effi,
    ebe, etd, ecomp, ecor, ecb, edb⟩ := hs
  have hP : (WordSemStateFiniteExact.callEnv a ss (pushEnv (y1, y2) h' (decClock cst))).permute =
      (WordSemStateFiniteExact.callEnv a ss (pushEnv (x1, x2) handler
        { decClock st with permute := perm })).permute := by
    rw [hC.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
      hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
    exact hperm.symm
  have hL : (WordSemStateFiniteExact.callEnv a ss (pushEnv (y1, y2) h' (decClock cst))).locals =
      (WordSemStateFiniteExact.callEnv a ss (pushEnv (x1, x2) handler
        { decClock st with permute := perm })).locals := rfl
  rw [← stateEq_of_fields (WordSemStateFiniteExact.callEnv a ss (pushEnv (x1, x2) handler
        { decClock st with permute := perm }))
      (WordSemStateFiniteExact.callEnv a ss (pushEnv (y1, y2) h' (decClock cst))) ?_]
  · rw [hP, hL]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19,
    s20, -, -, -⟩ := hS
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
    c20, -, -, -⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c1, s1]; exact efp
  · rw [c2, s2]; exact est
  · rw [c3, s3]
  · rw [c4, s4]; exact eslim
  · rw [c5, s5, ← hsz]; show wordSemOptionMax (wordSemOptionMax cst.stackMax _) _ =
      wordSemOptionMax (wordSemOptionMax st.stackMax _) _; rw [esmax]
  · rw [c6, s6]; exact essz
  · rw [c7, s7]; exact emem
  · rw [c8, s8]; exact emd
  · rw [c9, s9]; exact esmd
  · rw [c10, s10]; exact egc
  · rw [c11, s11]
    rcases handler with _ | _ <;> rcases h' with _ | _
    · exact eh
    · cases hhs
    · cases hhs
    · show cst.stack.length = st.stack.length; rw [estk]
  · rw [c12, s12]; show cst.clock - 1 = st.clock - 1; rw [eclk]
  · rw [c13, s13]; exact ecode
  · rw [c14, s14]; exact effi
  · rw [c15, s15]; exact ebe
  · rw [c16, s16]; exact etd
  · rw [c17, s17]; exact ecomp
  · rw [c18, s18]; exact ecor
  · rw [c19, s19]; exact ecb
  · rw [c20, s20]; exact edb

/-- `map` keeps `Nodup` for a function injective on the list. -/
theorem nodup_map_of_injOn {α β : Type} (g : α → β) :
    ∀ l : List α, (∀ a b, a ∈ l → b ∈ l → g a = g b → a = b) → l.Nodup → (l.map g).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hinj, hnd => by
      rw [List.nodup_cons] at hnd
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, nodup_map_of_injOn g l (fun x y hx hy => hinj x y
        (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)) hnd.2⟩
      obtain ⟨b, hb, hgb⟩ := List.mem_map.mp hm
      have := hinj b a (List.mem_cons_of_mem _ hb) (List.mem_cons_self) hgb
      subst this
      exact hnd.1 hb

/-- Stack size of a pushed frame. -/
theorem stackSize_pushEnv (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (h : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (t : WordSemStateFiniteExact width C F) :
    wordSemStackSize (pushEnv envs h t).stack =
      wordSemOptionAdd (match h with | none => t.localsSize | some _ => t.localsSize.map (3 + ·))
        (wordSemStackSize t.stack) := by
  rcases h with _ | ⟨_, _, _, _⟩ <;> rfl

open Classical in
/-- A returning call whose clock is zero times out with a flushed state. -/
theorem evaluate_call_ret_timeout (s : WordSemStateFiniteExact width C F)
    (n : List Nat) (names : WordLangCutsetsHOL) (rh : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (xv args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (hgv : WordSemStateFiniteExact.getVars args s = some xv)
    (hbad : ¬ wordSemBadDestArgs dest args = true)
    (hfc : wordSemFindCode dest (wordSemAddRetLoc (some (n, names, rh, l1, l2)) xv) s.code
      s.stackSize = some (args1, prog, ss))
    (hg : ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup))
    (hce : wordSemCutEnvs names s.locals = some envs) (hz : s.clock = 0) :
    evaluate (.call (some (n, names, rh, l1, l2)) dest args handler) s =
      (some .timeOut, flushState true { s with
        stackMax := (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler s)).stackMax,
        stack := [] }) := by
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)
    ).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht, hgv]
  dsimp only
  rw [if_neg hbad, hfc]
  dsimp only
  rw [if_neg hg, hce]
  dsimp only
  rw [if_pos hz]

/-- The coloured exception handler of a call. -/
def colourHandler (f : Nat → Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat) :=
  match handler with
  | none => none
  | some (v, prog, l1, l2) => some (f v, applyColour f prog, l1, l2)

/-- `apply_colour` on a returning call (Flapjack infrastructure). -/
theorem applyColour_call_some (f : Nat → Nat) (n : List Nat) (names : WordLangCutsetsHOL)
    (rh : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    applyColour f (.call (some (n, names, rh, l1, l2)) dest args handler) =
      .call (some (n.map f, applyNummapsKey f names, applyColour f rh, l1, l2)) dest
        (args.map f) (colourHandler f handler) := by
  rcases handler with _ | ⟨_, _, _, _⟩ <;> (rw [applyColour.eq_def]; rfl)

/-- Flushing callee results pass through the call (Flapjack infrastructure). -/
theorem callRetTail_flush (n : List Nat) (rh : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (r : WordSemResult width) (t : WordSemStateFiniteExact width C F)
    (hr : r = .timeOut ∨ r = .notEnoughSpace ∨ ∃ e, r = .finalFfi e) :
    callRetTail n rh l1 l2 envs handler (some r, t) = (some r, t) := by
  rcases hr with rfl | rfl | ⟨e, rfl⟩ <;> rfl

/-- Flushing results only require equal locals (Flapjack infrastructure). -/
theorem applyColourLocals_flush (f : Nat → Nat) (live : NumSet) (lt : List (NumSet × NumSet))
    (r : WordSemResult width) (a : Spt (WordLocW width))
    (hr : r = .timeOut ∨ r = .notEnoughSpace ∨ ∃ e, r = .finalFfi e) :
    applyColourLocals f live lt (some r) a a := by
  rcases hr with rfl | rfl | ⟨e, rfl⟩ <;> exact rfl

section RetTail

variable (n : List Nat) (rh : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
  (envs : Spt (WordLocW width) × Spt (WordLocW width))
  (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))

/-- Result with a mismatched label or arity is an error (Flapjack infrastructure). -/
theorem callRetTail_result_err (x : WordLocW width) (ys : List (WordLocW width))
    (t : WordSemStateFiniteExact width C F) (hg : x ≠ .loc l1 l2 ∨ ys.length ≠ n.length) :
    callRetTail n rh l1 l2 envs handler (some (.result x ys), t) = (some .error, t) := by
  classical
  show (if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then _ else _) = _
  rw [if_pos hg]

/-- Result with no frame to pop is an error (Flapjack infrastructure). -/
theorem callRetTail_result_popNone (x : WordLocW width) (ys : List (WordLocW width))
    (t : WordSemStateFiniteExact width C F) (hg : ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ n.length))
    (hp : popEnv t = none) :
    callRetTail n rh l1 l2 envs handler (some (.result x ys), t) = (some .error, t) := by
  classical
  show (if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then _ else _) = _
  rw [if_neg hg]
  show (match popEnv t with | none => _ | some s1 => _) = _
  rw [hp]

/-- Result after popping the caller frame (Flapjack infrastructure). -/
theorem callRetTail_result_pop (x : WordLocW width) (ys : List (WordLocW width))
    (t s1 : WordSemStateFiniteExact width C F) (hg : ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ n.length))
    (hp : popEnv t = some s1) :
    callRetTail n rh l1 l2 envs handler (some (.result x ys), t) =
      if sptDomainEqUnion s1.locals envs.1 envs.2 then
        evaluate rh (WordSemStateFiniteExact.setVars n ys s1)
      else (some .error, s1) := by
  classical
  show (if x ≠ .loc l1 l2 ∨ ys.length ≠ n.length then _ else _) = _
  rw [if_neg hg]
  show (match popEnv t with | none => _ | some s1 => _) = _
  rw [hp]

/-- Exception without a handler passes through (Flapjack infrastructure). -/
theorem callRetTail_exc_none (x y : WordLocW width) (t : WordSemStateFiniteExact width C F) :
    callRetTail n rh l1 l2 envs none (some (.exception x y), t) = (some (.exception x y), t) :=
  rfl

/-- Exception with a handler (Flapjack infrastructure). -/
theorem callRetTail_exc_some (x y : WordLocW width) (t : WordSemStateFiniteExact width C F)
    (v : Nat) (hp : WordLangProgHOL (BitVec width)) (l1' l2' : Nat) :
    callRetTail n rh l1 l2 envs (some (v, hp, l1', l2')) (some (.exception x y), t) =
      if x ≠ .loc l1' l2' then (some .error, t)
      else if sptDomainEqUnion t.locals envs.1 envs.2 then
        evaluate hp (WordSemStateFiniteExact.setVar v y t)
      else (some .error, t) := by
  classical
  rfl

end RetTail

/-- `pop_env` does not touch the oracle (Flapjack infrastructure). -/
theorem popEnv_withPermute (t : WordSemStateFiniteExact width C F) (q : Nat → Nat → Nat) :
    popEnv { t with permute := q } = (popEnv t).map (fun s => { s with permute := q }) := by
  unfold popEnv
  rcases t with ⟨_, _, _, _, stk, _⟩
  rcases stk with _ | ⟨⟨_, _, _, _ | ⟨_, _, _⟩⟩, _⟩ <;> rfl

/-- Local list-pair reassembly infrastructure (not a claimed HOL port). -/
theorem zip_map_fst_snd {α β : Type} (e : List (α × β)) :
    (e.map Prod.fst).zip (e.map Prod.snd) = e := by
  induction e with
  | nil => rfl
  | cons p e ih => simp [ih]

/-- Association-list membership (Flapjack infrastructure). -/
private theorem alistLookupIsSomeC {α : Type} (k : Nat) :
    ∀ l : List (Nat × α), (sptAListLookup k l).isSome = true ↔ k ∈ l.map Prod.fst
  | [] => by simp [sptAListLookup]
  | (a, v) :: l => by
      by_cases h : k = a
      · subst h; simp [sptAListLookup]
      · simp [sptAListLookup, h, alistLookupIsSomeC k l]

/-- Keys of a frame environment `union (fromAList l) (fromAList (toAList t))`. -/
theorem sptDomain_frameLocals {α : Type} (l : List (Nat × α)) (t : Spt α) (k : Nat) :
    sptDomain (sptUnion (sptFromAList l) (sptFromAList (sptToAList t))) k ↔
      k ∈ l.map Prod.fst ∨ sptDomain t k := by
  rw [sptDomain_uni]
  unfold sptDomain
  rw [sptLookup_sptFromAList, sptLookup_sptFromAList_sptToAList, alistLookupIsSomeC]

end CallCase

/-- HOL `evaluate_apply_colour`, `Call` case (`word_allocProofScript.sml:1449-1809`):
the three HOL premises at `Call ret dest args handler` and the HOL existential
conclusion; the only additional hypotheses are the induction hypotheses for the
two sub-programs, the return handler and the exception handler. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "evaluate_apply_colour"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateApplyColour_Call {width : Nat} [NeZero width] {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (ihRet : ∀ n names rh l1 l2, ret = some (n, names, rh, l1, l2) → applyColourGoal C F rh)
    (ihHandler : ∀ v h l1 l2, handler = some (v, h, l1, l2) → applyColourGoal C F h) :
    ∀ (st cst : WordSemStateFiniteExact width C F) (f : Nat → Nat) (live : NumSet)
      (lt : List (NumSet × NumSet)),
      colouringOk f (.call ret dest args handler) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain (getLive (.call ret dest args handler) live lt))
          st.locals cst.locals →
      applyColourPost f (.call ret dest args handler) live lt st cst := by
  classical
  rintro st cst f live lt ⟨hok, hs, hr⟩
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)
    ).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- the arguments are live
  have hargs : ∀ a, a ∈ args → sptDomain (getLive (.call ret dest args handler) live lt) a := by
    intro a ha
    cases ret with
    | none => simp only [getLive]; exact (sptDomain_numsetIns _ _ _).mpr (Or.inr ha)
    | some r =>
        obtain ⟨_, cuts, _⟩ := r
        simp only [getLive]
        exact (sptDomain_uni _ _ _).mpr (Or.inr ((sptDomain_numsetIns _ _ _).mpr (Or.inr ha)))
  cases hgv : WordSemStateFiniteExact.getVars args st with
  | none =>
    apply applyColourPost_self
    intro he
    rw [ht, hgv] at he
    exact absurd rfl he
  | some xv =>
  have hgvC : WordSemStateFiniteExact.getVars (args.map f) cst = some xv :=
    strongLocalsRelGetVars args xv f _ st cst ⟨hr, hargs, hgv⟩
  have hbadC : wordSemBadDestArgs dest (args.map f) = wordSemBadDestArgs dest args := by
    simp [wordSemBadDestArgs]
  by_cases hbad : wordSemBadDestArgs dest args = true
  · apply applyColourPost_self
    intro he
    rw [ht, hgv] at he
    dsimp only at he
    rw [if_pos hbad] at he
    exact absurd rfl he
  have hcode : cst.code = st.code := wsrCode hs
  have hss : cst.stackSize = st.stackSize := by unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.1
  have hclk : cst.clock = st.clock := wsrClock hs
  cases ret with
  | none =>
    cases handler with
    | some hv =>
      apply applyColourPost_self
      intro he
      rw [ht, hgv] at he
      dsimp only at he
      rw [if_neg hbad] at he
      split at he <;> exact absurd rfl he
    | none =>
    cases hfc : wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xv) st.code st.stackSize with
    | none =>
      apply applyColourPost_self
      intro he
      rw [ht, hgv] at he
      dsimp only at he
      rw [if_neg hbad, hfc] at he
      exact absurd rfl he
    | some fc =>
    obtain ⟨args1, prog, ss⟩ := fc
    have hEq : evaluate (applyColour f (.call none dest args none)) cst =
        evaluate (.call none dest args none) { st with permute := cst.permute } := by
      simp only [applyColour]
      rw [ht cst, ht { st with permute := cst.permute }, hgvC, getVars_withPermute, hgv]
      dsimp only
      simp only [hbadC, hbad, Bool.false_eq_true, ↓reduceIte, hcode, hss, hfc, hclk]
      by_cases hz : st.clock = 0
      · simp only [hz, ↓reduceIte]
        congr 1
        conv => lhs; rw [← wsrEq hs]
        simp only [hz]
        try rfl
      · simp only [hz, ↓reduceIte]
        rw [callEnv_decClock_wsr hs]
    refine applyColourPost_intro f _ live lt st cst cst.permute
      (evaluate (.call none dest args none) { st with permute := cst.permute }).1
      (evaluate (.call none dest args none) { st with permute := cst.permute }).1
      (evaluate (.call none dest args none) { st with permute := cst.permute }).2
      (evaluate (.call none dest args none) { st with permute := cst.permute }).2 rfl
      (fun hne => ⟨by rw [hEq], rfl, wsrRefl _, ?_⟩)
    have hshape : ∀ r, (evaluate (.call none dest args none : WordLangProgHOL (BitVec width))
        { st with permute := cst.permute }).1 = r → wordSemBadFunReturn r = true →
        r = some .error := by
      intro r hr0 hb
      rw [ht, getVars_withPermute, hgv] at hr0
      dsimp only at hr0
      rw [if_neg hbad, hfc] at hr0
      dsimp only at hr0
      by_cases hz : st.clock = 0
      · rw [if_pos hz] at hr0; subst hr0; simp [wordSemBadFunReturn] at hb
      · rw [if_neg hz] at hr0
        split at hr0
        · exact hr0.symm
        · rename_i hnb; rw [← hr0] at hb; exact absurd hb hnb
    generalize hE : (evaluate (.call none dest args none : WordLangProgHOL (BitVec width))
      { st with permute := cst.permute }) = E at hne hshape ⊢
    rcases E with ⟨r, rst⟩
    dsimp only at hne hshape ⊢
    rcases r with _ | r
    · exact absurd (hshape none rfl rfl) (by simp)
    · cases r with
      | «break» k => exact absurd (hshape _ rfl rfl) (by simp)
      | «continue» k => exact absurd (hshape _ rfl rfl) (by simp)
      | _ => rfl
  | some rv =>
  obtain ⟨n, names, rh, l1, l2⟩ := rv
  obtain ⟨n1, n2⟩ := names
  have hok' := hok
  unfold colouringOk at hok'
  obtain ⟨hinjA, hinjN, hokRh, hokH⟩ := hok'
  simp only [getLive] at hr
  have hmA : ∀ k, (sptDomain n1 k ∨ sptDomain n2 k) →
      sptDomain (sptUnion (sptUnion n2 n1) (numsetListInsert args .ln)) k := by
    intro k hk
    rw [sptDomain_uni, sptDomain_uni]
    rcases hk with hk | hk
    · exact Or.inl (Or.inr hk)
    · exact Or.inl (Or.inl hk)
  have hmR : ∀ k, (sptDomain n1 k ∨ sptDomain n2 k) →
      sptDomain (sptUnion (sptUnion n1 n2) (numsetListInsert args .ln)) k := by
    intro k hk
    rw [sptDomain_uni, sptDomain_uni]
    exact Or.inl hk
  have inj12 : ∀ a b, (sptDomain n1 a ∨ sptDomain n2 a) → (sptDomain n1 b ∨ sptDomain n2 b) →
      f a = f b → a = b := fun a b ha hb => hinjA a b (hmA a ha) (hmA b hb)
  have inj1 : ∀ a b, sptDomain n1 a → sptDomain n1 b → f a = f b → a = b :=
    fun a b ha hb => inj12 a b (Or.inl ha) (Or.inl hb)
  have inj2 : ∀ a b, sptDomain n2 a → sptDomain n2 b → f a = f b → a = b :=
    fun a b ha hb => inj12 a b (Or.inr ha) (Or.inr hb)
  have rel1 : strongLocalsRel f (sptDomain n1) st.locals cst.locals :=
    fun k v ⟨hk, h⟩ => hr k v ⟨hmR k (Or.inl hk), h⟩
  have rel2 : strongLocalsRel f (sptDomain n2) st.locals cst.locals :=
    fun k v ⟨hk, h⟩ => hr k v ⟨hmR k (Or.inr hk), h⟩
  cases hfc : wordSemFindCode dest (wordSemAddRetLoc (some (n, (n1, n2), rh, l1, l2)) xv)
      st.code st.stackSize with
  | none =>
    apply applyColourPost_self
    intro he
    rw [ht, hgv] at he
    dsimp only at he
    rw [if_neg hbad, hfc] at he
    exact absurd rfl he
  | some fc =>
  obtain ⟨args1, prog, ss⟩ := fc
  by_cases hg : sptDomainEmpty n1 ∨ ¬ n.Nodup
  · apply applyColourPost_self
    intro he
    rw [ht, hgv] at he
    dsimp only at he
    rw [if_neg hbad, hfc] at he
    dsimp only at he
    rw [if_pos hg] at he
    exact absurd rfl he
  have hgC : ¬ (sptDomainEmpty (applyNummapsKey f (n1, n2)).1 ∨ ¬ (n.map f).Nodup) := by
    intro h
    apply hg
    rcases h with h | h
    · left
      intro k hk
      apply h (f k)
      show sptDomain (applyNummapsKey f (n1, n2)).1 (f k)
      rw [(nummapsToNummap f (n1, n2)).1, applyNummapKeyDomain]
      exact ⟨k, hk, rfl⟩
    · right
      intro hnd
      apply h
      refine nodup_map_of_injOn f n (fun a b ha hb hab => hinjN a b ?_ ?_ hab) hnd
      · exact (sptDomain_numsetIns _ _ _).mpr (Or.inr ha)
      · exact (sptDomain_numsetIns _ _ _).mpr (Or.inr hb)
  cases hce : wordSemCutEnvs (n1, n2) st.locals with
  | none =>
    apply applyColourPost_self
    intro he
    rw [ht, hgv] at he
    dsimp only at he
    rw [if_neg hbad, hfc] at he
    dsimp only at he
    rw [if_neg hg] at he
    rw [hce] at he
    exact absurd rfl he
  | some xs =>
  obtain ⟨x1, x2⟩ := xs
  obtain ⟨y1, y2, hceC, hdy1, hdy2, hr1, hr2, hi1, hi2, hdx1, hdx2⟩ :=
    cutEnvsLemma n1 n2 st.locals cst.locals x1 x2 f ⟨inj1, inj2, hce, rel1, rel2⟩
  have hfcC : wordSemFindCode dest (wordSemAddRetLoc (some (n.map f, applyNummapsKey f (n1, n2),
      applyColour f rh, l1, l2)) xv) cst.code cst.stackSize = some (args1, prog, ss) := by
    rw [hcode, hss]; exact hfc
  have hbad' : ¬ wordSemBadDestArgs dest (args.map f) = true := by rw [hbadC]; exact hbad
  -- the coloured handler
  have hstk : cst.stack = st.stack := by unfold wordStateEqRel at hs; exact hs.2.2.2.1
  have hls : cst.localsSize = st.localsSize := by unfold wordStateEqRel at hs; exact hs.2.2.1
  have hhd : cst.handler = st.handler := by
    unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.2.2.2.2.2.1
  by_cases hz : st.clock = 0
  · -- TimeOut before the call
    have hEvC : evaluate (applyColour f (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler))
        cst =
        (some .timeOut, flushState true { cst with
          stackMax := (WordSemStateFiniteExact.callEnv args1 ss
            (pushEnv (y1, y2) (colourHandler f handler) cst)).stackMax,
          stack := [] }) := by
      rw [applyColour_call_some]
      exact evaluate_call_ret_timeout cst (n.map f) (applyNummapsKey f (n1, n2)) (applyColour f rh)
        l1 l2 dest (args.map f) (colourHandler f handler) xv args1 prog ss (y1, y2) hgvC hbad' hfcC
        hgC hceC
        (by rw [hclk]; exact hz)
    have hEvS := evaluate_call_ret_timeout { st with permute := st.permute } n (n1, n2) rh l1 l2
      dest args handler xv args1 prog ss (x1, x2) (by rw [getVars_withPermute]; exact hgv) hbad
      hfc hg hce hz
    refine applyColourPost_intro f _ live lt st cst st.permute _ _ _ _ hEvS
      (fun _ => ⟨hEvC, rfl, ?_, rfl⟩)
    apply wsrFlush
    have hS := callEnv_pushEnv_fields args1 ss (x1, x2) handler { st with permute := st.permute }
    have hC := callEnv_pushEnv_fields args1 ss (y1, y2) (colourHandler f handler) cst
    simp only at hS hC
    have hm : (WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv (y1, y2) (colourHandler f handler) cst)).stackMax =
        (WordSemStateFiniteExact.callEnv args1 ss
          (pushEnv (x1, x2) handler { st with permute := st.permute })).stackMax := by
      rw [hC.2.2.2.2.1, hS.2.2.2.2.1, stackSize_pushEnv, stackSize_pushEnv]
      have hsm : cst.stackMax = st.stackMax := by
        unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.1
      rcases handler with _ | ⟨_, _, _, _⟩ <;>
        simp only [colourHandler, hsm, hls, hstk]
    have hs' := hs
    unfold wordStateEqRel at hs' ⊢
    obtain ⟨e1, e2, e3, -, e5, -, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20,
      e21⟩ := hs'
    exact ⟨e1, e2, e3, rfl, e5, hm, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
      e20, e21⟩
  -- the callee runs on pushed frames
  have hhs : handler.isSome = (colourHandler f handler).isSome := by
    rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
  have hdy2' : sptDomain y2 = fun key => ∃ source, sptDomain x2 source ∧ f source = key := by
    rw [hdx2]; exact hdy2
  have hdy1' : sptDomain y1 = fun key => ∃ source, sptDomain x1 source ∧ f source = key := by
    rw [hdx1]; exact hdy1
  have hr2' : strongLocalsRel f (sptDomain x2) x2 y2 := by rw [hdx2]; exact hr2
  have hr1' : strongLocalsRel f (sptDomain x1) x1 y1 := by rw [hdx1]; exact hr1
  obtain ⟨perm, henv, hsv⟩ := pushEnvSValEq (decClock st) (decClock cst) x2 x1 y2 y1 f handler
    (colourHandler f handler) (wordSemEnvToList y2 cst.permute).2
    ⟨hhd.symm, hstk.symm, hls.symm, hdy2', hi2, hdy1', hi1, hr2',
      by rcases handler with _ | ⟨_, _, _, _⟩ <;> simp [colourHandler]⟩
  rcases hy : wordSemEnvToList y2 cst.permute with ⟨lsC, pmC⟩
  rcases hx : wordSemEnvToList x2 perm with ⟨lsB, pmB⟩
  have henv' := henv
  simp only [decClock] at henv'
  rw [hy, hx] at henv'
  obtain ⟨hpm, hmapB, hinjB⟩ := henv'
  have hperm : (wordSemEnvToList x2 perm).2 = (wordSemEnvToList y2 cst.permute).2 := by
    rw [hx, hy]; exact hpm
  have hSwap := calleeSwap hs x1 x2 y1 y2 handler (colourHandler f handler) hhs perm hperm hsv
    args1 ss
  generalize hS0 : WordSemStateFiniteExact.callEnv args1 ss
    (pushEnv (x1, x2) handler { decClock st with permute := perm }) = S0 at hSwap
  generalize hCc : WordSemStateFiniteExact.callEnv args1 ss
    (pushEnv (y1, y2) (colourHandler f handler) (decClock cst)) = Cc at hSwap
  have hvS : sValEq S0.stack Cc.stack := by rw [← hS0, ← hCc]; exact hsv
  have hEvC : evaluate (applyColour f (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler))
      cst = callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2) (colourHandler f handler)
        (evaluate prog Cc) := by
    rw [applyColour_call_some, ← hCc]
    exact evaluate_call_ret_eq cst (n.map f) (applyNummapsKey f (n1, n2)) (applyColour f rh)
      l1 l2 dest (args.map f) (colourHandler f handler) xv args1 prog ss (y1, y2) hgvC hbad'
      hfcC hgC hceC (by rw [hclk]; exact hz)
  have hEvS : ∀ perm'', evaluate (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler)
      { st with permute := ppPerm perm perm'' } =
        callRetTail n rh l1 l2 (x1, x2) handler (evaluate prog { S0 with permute := perm'' }) := by
    intro perm''
    rw [evaluate_call_ret_eq { st with permute := ppPerm perm perm'' } n (n1, n2) rh l1 l2 dest
      args handler xv args1 prog ss (x1, x2) (by rw [getVars_withPermute]; exact hgv) hbad hfc hg
      hce hz, ← hS0]
    show callRetTail n rh l1 l2 (x1, x2) handler (evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (pushEnv (x1, x2) handler { decClock st with permute := ppPerm perm perm'' }))) = _
    rw [pushEnv_ppPerm]
    rfl
  let Q : Option (WordSemResult width) × WordSemStateFiniteExact width C F → Prop := fun r =>
    (callRetTail n rh l1 l2 (x1, x2) handler r).1 ≠ some .error →
      (callRetTail n rh l1 l2 (x1, x2) handler r).1 =
          (callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2) (colourHandler f handler)
            (evaluate prog Cc)).1 ∧
        wordStateEqRel (callRetTail n rh l1 l2 (x1, x2) handler r).2
          (callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2) (colourHandler f handler)
            (evaluate prog Cc)).2 ∧
        applyColourLocals f live lt (callRetTail n rh l1 l2 (x1, x2) handler r).1
          (callRetTail n rh l1 l2 (x1, x2) handler r).2.locals
          (callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2) (colourHandler f handler)
            (evaluate prog Cc)).2.locals
  have hmain : ∃ pq, Q ((evaluate prog S0).1, { (evaluate prog S0).2 with permute := pq }) := by
    have hSS := (stackSwapPost_iff _ _).mp (evaluateStackSwap prog S0)
    rcases hE : evaluate prog S0 with ⟨r1, st1⟩
    rw [hE] at hSS
    dsimp only
    have hCrun : ∀ q, evaluate prog { S0 with stack := Cc.stack } = q → evaluate prog Cc = q :=
      fun q h => by rw [← hSwap]; exact h
    rcases r1 with _ | r1
    · exact ⟨st1.permute, fun hne => absurd rfl hne⟩
    cases r1 with
    | error => exact ⟨st1.permute, fun hne => absurd rfl hne⟩
    | «break» _ => exact ⟨st1.permute, fun hne => absurd rfl hne⟩
    | «continue» _ => exact ⟨st1.permute, fun hne => absurd rfl hne⟩
    | timeOut =>
        obtain ⟨-, -, hx⟩ := hSS
        have hc := hCrun _ (hx _ hvS)
        refine ⟨st1.permute, fun _ => ?_⟩
        rw [hc, callRetTail_flush _ _ _ _ _ _ _ _ (Or.inl rfl),
          callRetTail_flush _ _ _ _ _ _ _ _ (Or.inl rfl)]
        dsimp only
        exact ⟨rfl, wsrRefl _, applyColourLocals_flush _ _ _ _ _ (Or.inl rfl)⟩
    | notEnoughSpace =>
        obtain ⟨-, -, hx⟩ := hSS
        have hc := hCrun _ (hx _ hvS)
        refine ⟨st1.permute, fun _ => ?_⟩
        rw [hc, callRetTail_flush _ _ _ _ _ _ _ _ (Or.inr (Or.inl rfl)),
          callRetTail_flush _ _ _ _ _ _ _ _ (Or.inr (Or.inl rfl))]
        dsimp only
        exact ⟨rfl, wsrRefl _, applyColourLocals_flush _ _ _ _ _ (Or.inr (Or.inl rfl))⟩
    | finalFfi _ =>
        obtain ⟨-, -, hx⟩ := hSS
        have hc := hCrun _ (hx _ hvS)
        refine ⟨st1.permute, fun _ => ?_⟩
        rw [hc, callRetTail_flush _ _ _ _ _ _ _ _ (Or.inr (Or.inr ⟨_, rfl⟩)),
          callRetTail_flush _ _ _ _ _ _ _ _ (Or.inr (Or.inr ⟨_, rfl⟩))]
        dsimp only
        exact ⟨rfl, wsrRefl _, applyColourLocals_flush _ _ _ _ _ (Or.inr (Or.inr ⟨_, rfl⟩))⟩
    | result x ys =>
        obtain ⟨hk1, hh1, hxS⟩ := hSS
        obtain ⟨st0, hst0, hvst, hkst⟩ := hxS Cc.stack hvS
        have hc := hCrun _ hst0
        by_cases hg2 : x ≠ .loc l1 l2 ∨ ys.length ≠ n.length
        · exact ⟨st1.permute, fun hne => absurd (congrArg Prod.fst
            (callRetTail_result_err n rh l1 l2 (x1, x2) handler x ys _ hg2)) hne⟩
        have hg2' : ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ (n.map f).length) := by simpa using hg2
        have hkS : sKeyEq (pushEnv (x1, x2) handler { decClock st with permute := perm }).stack
            st1.stack := by rw [← hS0] at hk1; exact hk1
        have hkC : sKeyEq (pushEnv (y1, y2) (colourHandler f handler) (decClock cst)).stack
            st0 := by rw [← hCc] at hkst; exact hkst
        obtain ⟨nS, lS, lsS, optS, hst1st, s1, hpop, hloc1, hdom1, hk1s⟩ :=
          pushEnvPopEnvSKeyEq (x1, x2) handler { decClock st with permute := perm } st1 hkS
        cases hpopP : popEnv { st1 with permute := st1.permute } with
        | none => rw [popEnv_withPermute, hpop] at hpopP; cases hpopP
        | some _ => ?_
        obtain ⟨nC, lC, lsC', optC, hst0st, cy, hpopC, hlocC, hdomC, hkCy⟩ :=
          pushEnvPopEnvSKeyEq (y1, y2) (colourHandler f handler) (decClock cst)
            { st1 with stack := st0 } hkC
        have hW : wordStateEqRel s1 cy := popEnvFrame st1 s1 cy st0
          ⟨hvst, sKeyEqTrans _ _ _ ⟨(sKeyEqSym _ _).mp hk1s,
            by show sKeyEq st.stack cy.stack; rw [← hstk]; exact hkCy⟩,
            hpopC, hpop⟩
        by_cases hd : sptDomainEqUnion s1.locals x1 x2
        case neg =>
          refine ⟨st1.permute, fun hne => absurd ?_ hne⟩
          rw [callRetTail_result_pop n rh l1 l2 (x1, x2) handler x ys
            _ { s1 with permute := st1.permute } hg2
            (by rw [popEnv_withPermute, hpop]; rfl), if_neg hd]
        have hdC : sptDomainEqUnion cy.locals y1 y2 := by
          intro k
          have := congrFun hdomC k
          show sptDomain cy.locals k ↔ sptDomain y1 k ∨ sptDomain y2 k
          rw [← this]
          exact Or.comm
        -- keys and values of the popped frames
        have hkeysS := sKeyEqPushEnvImpMapFst { decClock st with permute := perm } x1 x2 handler
          nS (sptToAList x1) lS optS lsS lsB pmB ⟨by rw [← hst1st]; exact hkS, hx⟩
        have hkeysC := sKeyEqPushEnvImpMapFst (decClock cst) y1 y2 (colourHandler f handler)
          nC (sptToAList y1) lC optC lsC' lsC pmC ⟨by rw [← hst0st]; exact hkC, hy⟩
        have hvals : lS.map Prod.snd = lC.map Prod.snd := by
          have hst0st' : st0 = _ := hst0st
          rw [hst1st, hst0st'] at hvst
          exact ((sFrameValEqDef2 _ _ _ _ _ _ _ _).mp hvst.2).1
        have hmapK := keyMapImplies f lsB lsC hmapB
        have hl : lC.map Prod.fst = (lS.map Prod.fst).map f := by
          rw [← hkeysC.1, ← hmapK, hkeysS.1]
        have hkeysB := envToListKeys x2 perm
        rw [hx] at hkeysB
        have hdomL : ∀ a, a ∈ lS.map Prod.fst → sptDomain n2 a := by
          intro a ha
          rw [← hkeysS.1] at ha
          have : sptDomain x2 a := by rw [← hkeysB]; exact ha
          rw [hdx2] at this; exact this
        have hrelAll : ∀ d, strongLocalsRel f d s1.locals cy.locals := by
          intro d
          rw [hloc1, hlocC]
          have hz' : lS = (lS.map Prod.fst).zip (lC.map Prod.snd) := by
            rw [← hvals, zip_map_fst_snd]
          rw [hz']
          refine allocLocalsRel f x1 y1 (lS.map Prod.fst) lC hl ?_ hr1' d
          intro a b ha hb hab
          refine inj12 a b ?_ ?_ hab
          · rcases ha with ha | ha
            · exact Or.inr (hdomL a ha)
            · rw [hdx1] at ha; exact Or.inl ha
          · rcases hb with hb | hb
            · exact Or.inr (hdomL b hb)
            · rw [hdx1] at hb; exact Or.inl hb
        have hX : ∀ k, sptMem k s1.locals →
            sptDomain (numsetListInsert n (sptUnion n2 n1)) k := by
          intro k hk
          have := (congrFun hdom1 k).mpr hk
          rw [sptDomain_numsetIns, sptDomain_uni, hdx2, hdx1] at *
          exact Or.inl this
        have hlenN : n.length = ys.length := by
          have : ¬ ys.length ≠ n.length := fun h => hg2 (Or.inr h)
          exact (Classical.not_not.mp this).symm
        have hIH := ihRet n (n1, n2) rh l1 l2 rfl (WordSemStateFiniteExact.setVars n ys s1)
          (WordSemStateFiniteExact.setVars (n.map f) ys cy) f live lt
          ⟨hokRh, wsrLocals _ _ hW,
            strongLocalsRelSetVarsDom n ys f _ _ s1 cy ⟨hlenN, hinjN, hX,
              fun k hk => (sptDomain_numsetIns _ _ _).mpr (Or.inr hk), hrelAll _⟩⟩
        obtain ⟨pq, hpq⟩ := hIH
        refine ⟨pq, fun hne => ?_⟩
        have hsrc : callRetTail n rh l1 l2 (x1, x2) handler
            (some (.result x ys), { st1 with permute := pq }) =
            evaluate rh { WordSemStateFiniteExact.setVars n ys s1 with permute := pq } := by
          rw [callRetTail_result_pop _ _ _ _ _ _ _ _ _ { s1 with permute := pq } hg2
            (by rw [popEnv_withPermute, hpop]; rfl)]
          exact if_pos hd
        have hcol : callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2)
            (colourHandler f handler) (evaluate prog Cc) =
            evaluate (applyColour f rh) (WordSemStateFiniteExact.setVars (n.map f) ys cy) := by
          rw [hc, callRetTail_result_pop _ _ _ _ _ _ _ _ _ cy hg2' hpopC]
          exact if_pos hdC
        rw [hsrc] at hne ⊢
        rw [hcol]
        rcases hE1 : evaluate rh { WordSemStateFiniteExact.setVars n ys s1 with permute := pq } with
          ⟨res, rst⟩
        rcases hE2 : evaluate (applyColour f rh)
            (WordSemStateFiniteExact.setVars (n.map f) ys cy) with
          ⟨res', rcst⟩
        rw [hE1] at hpq hne
        rw [hE2] at hpq
        dsimp only at hpq hne ⊢
        rw [if_neg hne] at hpq
        exact hpq
    | exception x y =>
        obtain ⟨hlt, e0, e, nn, ls, m, lss, hl, hm, ⟨hfe, hloc⟩, hks, hhn, hxS⟩ := hSS
        have hkeysB := envToListKeys x2 perm
        rw [hx] at hkeysB
        have hkeysC := envToListKeys y2 cst.permute
        rw [hy] at hkeysC
        have hmapK := keyMapImplies f lsB lsC hmapB
        rcases handler with _ | ⟨v, hp, l1', l2'⟩
        · -- no handler: the exception passes through
          have hS0h : S0.handler = st.handler := by rw [← hS0]; rfl
          have hS0st : S0.stack =
              .stackFrame st.localsSize (sptToAList x1) lsB none :: st.stack := by
            rw [← hS0]; show (pushEnv (x1, x2) none { decClock st with permute := perm }).stack = _
            simp only [pushEnv, decClock, hx]
          have hCcst : Cc.stack =
              .stackFrame cst.localsSize (sptToAList y1) lsC none :: cst.stack := by
            rw [← hCc]; show (pushEnv (y1, y2) none (decClock cst)).stack = _
            simp only [pushEnv, decClock, hy]
          have hl0 := hl
          rw [hS0h, hS0st] at hlt hl
          have hle : st.handler + 1 ≤ st.stack.length := by
            rcases Nat.lt_or_ge st.handler st.stack.length with h | h
            · exact h
            · exfalso
              have hlt' : st.handler < st.stack.length + 1 := by simpa using hlt
              have heq : st.handler + 1 = (WordSemStackFrame.stackFrame st.localsSize
                  (sptToAList x1) lsB none :: st.stack).length := by simp; omega
              rw [lastNLengthCond _ _ heq] at hl
              simp at hl
          rw [lastN_cons _ _ _ hle] at hl
          have hlC0 : wordSemLastN (S0.handler + 1) Cc.stack =
              .stackFrame m e0 e (some nn) :: ls := by
            rw [hS0h, hCcst, lastN_cons _ _ _ (by rw [hstk]; exact hle), hstk]; exact hl
          obtain ⟨stt, locs, hstt, ⟨lss', hf', hlocs, hsnd'⟩, hvstt, hkstt⟩ :=
            hxS Cc.stack e0 e ls ⟨hlC0, hvS⟩
          have hc := hCrun _ hstt
          have hlss : lss = lss' := listEq_of_map_fst_snd _ _ (hfe.symm.trans hf') hsnd'
          subst hlss
          have hlocsEq : locs = st1.locals := hlocs.trans hloc.symm
          have hsttEq : stt = st1.stack :=
            (sValAndKeyEq _ _ ⟨hvstt, sKeyEqTrans _ _ _ ⟨hks, hkstt⟩⟩).symm
          refine ⟨st1.permute, fun _ => ?_⟩
          rw [hc, show colourHandler f (none : Option (Nat × WordLangProgHOL (BitVec width) × Nat ×
            Nat)) = none from rfl, callRetTail_exc_none, callRetTail_exc_none, hlocsEq, hsttEq,
            ← hhn]
          exact ⟨rfl, wsrRefl _, rfl⟩
        · -- handler: continue with the handler program
          obtain ⟨hinjH, hokHp⟩ := hokH
          have hS0h : S0.handler = st.stack.length := by rw [← hS0]; rfl
          have hS0st : S0.stack = .stackFrame st.localsSize (sptToAList x1) lsB
              (some (st.handler, l1', l2')) :: st.stack := by
            rw [← hS0]; show (pushEnv (x1, x2) (some (v, hp, l1', l2'))
              { decClock st with permute := perm }).stack = _
            simp only [pushEnv, decClock, hx]
          have hCcst : Cc.stack = .stackFrame cst.localsSize (sptToAList y1) lsC
              (some (cst.handler, l1', l2')) :: cst.stack := by
            rw [← hCc]; show (pushEnv (y1, y2) (some (f v, applyColour f hp, l1', l2'))
              (decClock cst)).stack = _
            simp only [pushEnv, decClock, hy]
          rw [hS0h, hS0st, lastNLengthCond _ _ (by simp)] at hl
          simp only [List.cons.injEq, WordSemStackFrame.stackFrame.injEq, Option.some.injEq] at hl
          obtain ⟨⟨hm0, he0, hee, hnn⟩, hls0⟩ := hl
          subst hm0 he0 hee hnn hls0
          have hlC0 : wordSemLastN (S0.handler + 1) Cc.stack =
              .stackFrame st.localsSize (sptToAList y1) lsC (some (st.handler, l1', l2')) ::
                cst.stack := by
            rw [hS0h, hCcst, lastNLengthCond _ _ (by simp [hstk]), hls, hhd]
          obtain ⟨stt, locs, hstt, ⟨lss', hf', hlocs, hsnd'⟩, hvstt, hkstt⟩ :=
            hxS Cc.stack (sptToAList y1) lsC cst.stack ⟨hlC0, hvS⟩
          have hc := hCrun _ hstt
          have hsttEq : stt = st1.stack :=
            (sValAndKeyEq _ _ ⟨hvstt, sKeyEqTrans _ _ _ ⟨hks, by rw [← hstk]; exact hkstt⟩⟩).symm
          by_cases hxg : x ≠ .loc l1' l2'
          · refine ⟨st1.permute, fun hne => absurd ?_ hne⟩
            rw [callRetTail_exc_some, if_pos hxg]
          by_cases hd : sptDomainEqUnion st1.locals x1 x2
          case neg =>
            refine ⟨st1.permute, fun hne => absurd ?_ hne⟩
            rw [callRetTail_exc_some, if_neg hxg, if_neg hd]
          have hkl : lss'.map Prod.fst = (lss.map Prod.fst).map f := by
            rw [← hf', ← hmapK, hfe]
          have hdomL : ∀ a, a ∈ lss.map Prod.fst → sptDomain n2 a := by
            intro a ha
            rw [← hfe] at ha
            have : sptDomain x2 a := by rw [← hkeysB]; exact ha
            rw [hdx2] at this; exact this
          have hrelAll : ∀ d, strongLocalsRel f d st1.locals locs := by
            intro d
            rw [hloc, hlocs]
            have hz' : lss = (lss.map Prod.fst).zip (lss'.map Prod.snd) := by
              rw [← hsnd', zip_map_fst_snd]
            rw [hz']
            refine allocLocalsRel f x1 y1 (lss.map Prod.fst) lss' hkl ?_ hr1' d
            intro a b ha hb hab
            refine inj12 a b ?_ ?_ hab
            · rcases ha with ha | ha
              · exact Or.inr (hdomL a ha)
              · rw [hdx1] at ha; exact Or.inl ha
            · rcases hb with hb | hb
              · exact Or.inr (hdomL b hb)
              · rw [hdx1] at hb; exact Or.inl hb
          have hX : ∀ k, sptMem k st1.locals → sptDomain (sptInsert v () (sptUnion n2 n1)) k := by
            intro k hk
            have hk' : sptDomain st1.locals k := hk
            rw [hloc, sptDomain_frameLocals] at hk'
            rw [sptDomain_ins, sptDomain_uni]
            rcases hk' with hk' | hk'
            · exact Or.inr (Or.inl (hdomL k hk'))
            · rw [hdx1] at hk'; exact Or.inr (Or.inr hk')
          have hdC : sptDomainEqUnion locs y1 y2 := by
            intro k
            show sptDomain locs k ↔ sptDomain y1 k ∨ sptDomain y2 k
            rw [hlocs, sptDomain_frameLocals, ← hf']
            have : k ∈ lsC.map Prod.fst ↔ sptDomain y2 k := by rw [← hkeysC]
            rw [this]
            exact Or.comm
          have hW : wordStateEqRel st1
              { st1 with stack := stt, handler := st.handler, locals := locs } := by
            have hh1 : st.handler = st1.handler := hhn.symm
            rw [hsttEq, hh1]
            exact wsrLocals st1.locals locs (wsrRefl st1)
          have hIH := ihHandler v hp l1' l2' rfl (WordSemStateFiniteExact.setVar v y st1)
            (WordSemStateFiniteExact.setVar (f v) y
              { st1 with stack := stt, handler := st.handler, locals := locs })
            f live lt ⟨hokHp, wsrLocals _ _ hW,
              strongLocalsRelSetVarDom f _ _ v y st1 _ ⟨hinjH, hX,
                (sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hrelAll _⟩⟩
          obtain ⟨pq, hpq⟩ := hIH
          refine ⟨pq, fun hne => ?_⟩
          have hsrc : callRetTail n rh l1 l2 (x1, x2) (some (v, hp, l1', l2'))
              (some (.exception x y), { st1 with permute := pq }) =
              evaluate hp { WordSemStateFiniteExact.setVar v y st1 with permute := pq } := by
            rw [callRetTail_exc_some, if_neg hxg]
            exact if_pos hd
          have hcol : callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2)
              (colourHandler f (some (v, hp, l1', l2'))) (evaluate prog Cc) =
              evaluate (applyColour f hp) (WordSemStateFiniteExact.setVar (f v) y
                { st1 with stack := stt, handler := st.handler, locals := locs }) := by
            rw [hc]
            show callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2)
              (some (f v, applyColour f hp, l1', l2')) _ = _
            rw [callRetTail_exc_some, if_neg hxg]
            exact if_pos hdC
          rw [hsrc] at hne ⊢
          rw [hcol]
          rcases hE1 : evaluate hp
              { WordSemStateFiniteExact.setVar v y st1 with permute := pq } with
            ⟨res, rst⟩
          rcases hE2 : evaluate (applyColour f hp) (WordSemStateFiniteExact.setVar (f v) y
              { st1 with stack := stt, handler := st.handler, locals := locs }) with
            ⟨res', rcst⟩
          rw [hE1] at hpq hne
          rw [hE2] at hpq
          dsimp only at hpq hne ⊢
          rw [if_neg hne] at hpq
          exact hpq
  obtain ⟨perm'', hQ⟩ := permuteSwapLemma4 prog S0 Q
    ⟨fun st' _ hne => absurd rfl hne, hmain⟩
  refine applyColourPost_intro f _ live lt st cst (ppPerm perm perm'') _
    (callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2) (colourHandler f handler)
      (evaluate prog Cc)).1 _
    (callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2) (colourHandler f handler)
      (evaluate prog Cc)).2 (hEvS perm'') (fun hne => ?_)
  obtain ⟨h1, h2, h3⟩ := hQ hne
  exact ⟨hEvC, h1, h2, h3⟩

end Flapjack.WordAlloc
