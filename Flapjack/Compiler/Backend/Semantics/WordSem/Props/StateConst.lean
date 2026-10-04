import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.WordSem.ShMem
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.InstConstFull

/-!
# `wordProps`: state-constancy lemmas (`*_const`, `*_with_const`)

Counterpart of the `CONST LEMMAS` section of
`cakeml/compiler/backend/semantics/wordPropsScript.sml` (lines 90-1380): which
fields each wordSem state operation leaves unchanged, and how each operation
commutes with an update of a field it does not read. Every conjunct of each
HOL theorem is kept in source order. HOL's record update `s with ffi := f` may
change the FFI type, so an FFI conjunct binds an independent `OtherF` host type;
the shared-memory functions return an independent HOL `'a result`, represented
by independently quantified positive result widths, separate from the state
width and also separate across the permute and clock conjuncts.

Not ported here: `case_eq_thms` is an ML-assembled list of HOL's automatically
generated `case_eq` rewrites for nine datatypes, not a statement about wordSem
(Lean's `split`/`cases` play its role). The `[local]` `evaluate_clock_const` and
`evaluate_clock_with_const` are covered by the untagged
`evaluate_withClock_const` in `EvaluateAddClock`, and `inst_const` lives in
`InstConst`. The other theorems of the section already have tagged ports in
`StateLaws`, `JumpExcConst`, `InstConstFull` and the evaluator property modules.
-/

namespace Flapjack

namespace WordSemStateConstSupport

/-- Same-module canonical finite-support witness for the `fpRegs`/`store`
    fields named by the tagged theorems of this module. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C : Type} {F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
        (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
        WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness

end WordSemStateConstSupport

/-- Exact HOL `PAIR_MAP_EQ_PAIR` (`wordPropsScript.sml:112-116`). -/
theorem prodMap_eq_pair {α β γ δ : Type} (f : α → γ) (g : β → δ) (p : α × β) (a : γ) (b : δ) :
    Prod.map f g p = (a, b) ↔ ∃ x y, p = (x, y) ∧ f x = a ∧ g y = b := by
  obtain ⟨x, y⟩ := p
  constructor
  · intro h
    exact ⟨x, y, rfl, (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
  · rintro ⟨x', y', h, rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rfl

/-- Exact HOL `OPTION_CASE_OPTION_MAP` (`wordPropsScript.sml:122-128`);
    HOL's `option_CASE x e g` is `Option.elim x e g`. -/
theorem optionElim_map {α β γ : Type} (f : α → β) (a : Option α) (e : γ) (g : β → γ) :
    (a.map f).elim e g = a.elim e (fun x => g (f x)) := by
  cases a <;> rfl

/-- Exact HOL `OPTION_CASE_MAP` (`wordPropsScript.sml:130-134`). -/
theorem optionElim_some {α β : Type} (f : α → β) (x : Option α) :
    x.elim none (fun x => some (f x)) = x.map f := by
  cases x <;> rfl

namespace WordSemStateFiniteExact

section Congr

variable {width : Nat} [NeZero width] {C : Type} {F : Type} {C' : Type} {F' : Type}

/-- `word_exp` reads only the locals, store, memory and memory domain
    (Flapjack infrastructure). -/
theorem wordExp_congr (s : WordSemStateFiniteExact width C F) (t : WordSemStateFiniteExact width C' F')
    (hl : t.locals = s.locals) (hs : t.store = s.store) (hm : t.memory = s.memory)
    (hd : t.mdomain = s.mdomain) :
    ∀ e : WordLangExpHOL (BitVec width), wordExp t e = wordExp s e
  | .const w => by rw [wordExp, wordExp]
  | .var v => by rw [wordExp, wordExp]; simp only [getVar, hl]
  | .lookup n => by rw [wordExp, wordExp]; simp only [getStore, hs]
  | .load a => by
      rw [wordExp, wordExp, wordExp_congr s t hl hs hm hd a]
      simp only [memLoad, hm, hd]
  | .op op args => by
      rw [wordExp, wordExp]
      have : (args.attach.map fun (x : { x // x ∈ args }) => wordExp t x.1) =
          (args.attach.map fun (x : { x // x ∈ args }) => wordExp s x.1) := by
        apply List.map_congr_left
        intro ⟨e, he⟩ _
        have := List.sizeOf_lt_of_mem he
        exact wordExp_congr s t hl hs hm hd e
      simp only [] at this ⊢
      rw [this]
  | .shift sh e1 e2 => by
      rw [wordExp, wordExp, wordExp_congr s t hl hs hm hd e1, wordExp_congr s t hl hs hm hd e2]
termination_by e => sizeOf e

/-- `get_vars` reads only the locals (Flapjack infrastructure). -/
theorem getVars_congr (s : WordSemStateFiniteExact width C F) (t : WordSemStateFiniteExact width C' F')
    (hl : t.locals = s.locals) :
    ∀ ns : List Nat, WordSemStateFiniteExact.getVars ns t = WordSemStateFiniteExact.getVars ns s
  | [] => rfl
  | n :: ns => by
      simp only [WordSemStateFiniteExact.getVars, getVars_congr s t hl ns, getVar, hl]

end Congr

section Frame

variable {width : Nat} [NeZero width] {C : Type} {F : Type}

/-- A state map that keeps every field `inst` reads and commutes with the
    updates `inst` makes (Flapjack infrastructure). -/
structure InstFrame (f : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F) : Prop where
  locals : ∀ s, (f s).locals = s.locals
  store : ∀ s, (f s).store = s.store
  memory : ∀ s, (f s).memory = s.memory
  mdomain : ∀ s, (f s).mdomain = s.mdomain
  be : ∀ s, (f s).be = s.be
  fpRegs : ∀ s, (f s).fpRegs = s.fpRegs
  setVar : ∀ x w s, setVar x w (f s) = f (setVar x w s)
  setFpVar : ∀ x w s, setFpVar x w (f s) = f (setFpVar x w s)
  setMemory : ∀ s m, ({ f s with memory := m } : WordSemStateFiniteExact width C F) =
    f { s with memory := m }
  memStore : ∀ a w s, memStore a w (f s) = (memStore a w s).map f

set_option linter.unusedSimpArgs false in
theorem inst_frame {f : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F}
    (hf : InstFrame f) (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F) :
    (inst i s).map f = inst i (f s) := by
  have wE : ∀ e, wordExp (f s) e = wordExp s e :=
    wordExp_congr s (f s) (hf.locals s) (hf.store s) (hf.memory s) (hf.mdomain s)
  have gV : ∀ ns, WordSemStateFiniteExact.getVars ns (f s) = WordSemStateFiniteExact.getVars ns s :=
    getVars_congr s (f s) (hf.locals s)
  have gv : ∀ x, getVar x (f s) = getVar x s := fun x => by simp only [getVar, hf.locals]
  have gf : ∀ x, getFpVar x (f s) = getFpVar x s := fun x => by simp only [getFpVar, hf.fpRegs]
  have sv := hf.setVar
  have sf := hf.setFpVar
  have ms : ∀ a w, memStore a w (f s) = (memStore a w s).map f := fun a w => hf.memStore a w s
  have ml : ∀ a, memLoad a (f s) = memLoad a s := fun a => by
    simp only [memLoad, hf.mdomain, hf.memory]
  have hm := hf.memory s
  have hd := hf.mdomain s
  have hb := hf.be s
  have sm := hf.setMemory s
  symm
  cases i with
  | skip => rfl
  | const r w => simp only [inst, assign, wE]; split <;> simp only [sv, Option.map_some, Option.map_none]
  | arith a =>
    cases a <;> simp only [inst, assign, wE, gV] <;>
      (repeat' split) <;> first | rfl | simp_all
  | mem op r a =>
    cases a
    cases op <;> simp only [inst, wE, gv, ms, ml, hm, hd, hb, sm] <;>
      (repeat' split) <;> first | rfl | simp_all
theorem assign_frame {f : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F}
    (hf : InstFrame f) (x : Nat) (e : WordLangExpHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) :
    (assign x e s).map f = assign x e (f s) := by
  simp only [assign, wordExp_congr s (f s) (hf.locals s) (hf.store s) (hf.memory s) (hf.mdomain s)]
  split <;> simp only [hf.setVar, Option.map_some, Option.map_none]

/-- A state map that keeps every field `alloc` reads and commutes with the
    updates `alloc` makes (Flapjack infrastructure). -/
structure AllocFrame (f : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F) : Prop where
  locals : ∀ s, (f s).locals = s.locals
  store : ∀ s, (f s).store = s.store
  pushStore : ∀ envs w s, pushEnv envs none (setStore .allocSize (.word w) (f s)) =
    f (pushEnv envs none (setStore .allocSize (.word w) s))
  gc : ∀ s, gc (f s) = (gc s).map f
  popEnv : ∀ s, popEnv (f s) = (popEnv s).map f
  flushState : ∀ b s, flushState b (f s) = f (flushState b s)

theorem alloc_frame {f : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F}
    (hf : AllocFrame f) (w : BitVec width) (names : WordLangCutsetsHOL)
    (s : WordSemStateFiniteExact width C F) :
    Prod.map id f (alloc w names s) = alloc w names (f s) := by
  unfold alloc
  rw [hf.locals]
  cases wordSemCutEnvs names s.locals with
  | none => simp only [Prod.map, id, hf.flushState]
  | some envs =>
    simp only []
    rw [hf.pushStore, hf.gc]
    cases gc (pushEnv envs none (setStore .allocSize (.word w) s)) with
    | none => simp only [Option.map_none, Prod.map, id, hf.flushState]
    | some g =>
      simp only [Option.map_some, hf.popEnv]
      cases popEnv g with
      | none => simp only [Option.map_none, Prod.map, id, hf.flushState]
      | some p =>
        simp only [Option.map_some]
        have hs : getStore .allocSize (f p) = getStore .allocSize p := by
          simp only [getStore, hf.store]
        rw [hs]
        cases getStore .allocSize p with
        | none => rfl
        | some a =>
          simp only []
          have hsp : hasSpace a (f p) = hasSpace a p := by
            simp only [hasSpace, getStore, hf.store]
          rw [hsp]
          split <;> simp only [Prod.map, id, hf.flushState]

/-- A state map that keeps every field the shared-memory operations read and
    commutes with the updates they make (Flapjack infrastructure). -/
structure ShMemFrame (f : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F) : Prop where
  locals : ∀ s, (f s).locals = s.locals
  shMdomain : ∀ s, (f s).shMdomain = s.shMdomain
  ffi : ∀ s, (f s).ffi = s.ffi
  setVar : ∀ x w s, setVar x w (f s) = f (setVar x w s)
  setFfi : ∀ s (x : HolFfiState F), ({ f s with ffi := x } : WordSemStateFiniteExact width C F) =
    f { s with ffi := x }
  flushState : ∀ b s, flushState b (f s) = f (flushState b s)

theorem shMemSetVar_frame {rw : Nat} [NeZero rw] {f : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F}
    (hf : ShMemFrame f) (res : Option (HolFfiResult F)) (v : Nat)
    (s : WordSemStateFiniteExact width C F) :
    Prod.map id f (shMemSetVar (rw := rw) res v s) = shMemSetVar (rw := rw) res v (f s) := by
  cases res with
  | none => rfl
  | some r =>
    cases r
    · simp only [shMemSetVar, Prod.map, id, hf.setFfi, hf.setVar]
    · simp only [shMemSetVar, Prod.map, id, hf.flushState]

theorem shMemStore_frame {rw : Nat} [NeZero rw] {f : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F}
    (hf : ShMemFrame f) (a w : BitVec width) (s : WordSemStateFiniteExact width C F) :
    Prod.map id f (shMemStore (rw := rw) a w s) = shMemStore (rw := rw) a w (f s) ∧
    Prod.map id f (shMemStoreByte (rw := rw) a w s) = shMemStoreByte (rw := rw) a w (f s) ∧
    Prod.map id f (shMemStore16 (rw := rw) a w s) = shMemStore16 (rw := rw) a w (f s) ∧
    Prod.map id f (shMemStore32 (rw := rw) a w s) = shMemStore32 (rw := rw) a w (f s) := by
  have hsm : ∀ a, (f s).shMdomain a = s.shMdomain a := fun a => by rw [hf.shMdomain]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [shMemStore, shMemStoreByte, shMemStore16, shMemStore32, hsm, hf.ffi] <;>
    split <;> (try split) <;> simp only [Prod.map, id, hf.flushState, hf.setFfi]

theorem shareInst_frame {rw : Nat} [NeZero rw] {f : WordSemStateFiniteExact width C F → WordSemStateFiniteExact width C F}
    (hf : ShMemFrame f) (op : WordMemOp) (v : Nat) (ad : BitVec width)
    (s : WordSemStateFiniteExact width C F) :
    Prod.map id f (shareInst (rw := rw) op v ad s) = shareInst (rw := rw) op v ad (f s) := by
  have gv : getVar v (f s) = getVar v s := by simp only [getVar, hf.locals]
  have h1 := fun w => (shMemStore_frame (rw := rw) hf ad w s).1
  have h2 := fun w => (shMemStore_frame (rw := rw) hf ad w s).2.1
  have h3 := fun w => (shMemStore_frame (rw := rw) hf ad w s).2.2.1
  have h4 := fun w => (shMemStore_frame (rw := rw) hf ad w s).2.2.2
  have hsm : ∀ a, (f s).shMdomain a = s.shMdomain a := fun a => by rw [hf.shMdomain]
  cases op <;>
    simp only [shareInst, shMemLoad, shMemLoadByte, shMemLoad16, shMemLoad32, hsm,
      hf.ffi, gv, shMemSetVar_frame (rw := rw) hf] <;>
    (try split) <;> first | exact h1 _ | exact h2 _ | exact h3 _ | exact h4 _ | rfl

end Frame

/-- Close one constancy conjunct (Flapjack proof automation). -/
syntax "constConj_tac" : tactic

macro_rules
  | `(tactic| constConj_tac) => `(tactic| first
  | rfl
  | (exact wordExp_congr _ _ (by rfl) (by rfl) (by rfl) (by rfl) _)
  | (exact getVars_congr _ _ (by rfl) _)
  | (cases ‹WordRegImm _› <;> rfl)
  | (cases ‹Bool› <;> rfl)
  | (cases ‹Option (Nat × WordLangProgHOL _ × Nat × Nat)› with
      | none => rfl
      | some h => obtain ⟨_, _, _, _⟩ := h; rfl)
  | (unfold popEnv; dsimp only <;> (try split) <;> rfl)
  | (unfold cutState; dsimp only <;> (try split) <;> rfl)
  | (unfold memStore; dsimp only <;> (try split) <;> rfl)
  | (unfold jumpExc; dsimp only <;> (try split) <;> (try split) <;> rfl)
  | (unfold gc; dsimp only <;> (try split) <;> (try split) <;> rfl)
  | (apply Eq.symm; apply assign_frame; constructor <;> intros <;> constConj_tac)
  | (apply Eq.symm; apply inst_frame; constructor <;> intros <;> constConj_tac)
  | (apply Eq.symm; apply alloc_frame; constructor <;> intros <;> constConj_tac)
  | (apply Eq.symm; apply shMemSetVar_frame; constructor <;> intros <;> constConj_tac)
  | (apply Eq.symm; apply shareInst_frame; constructor <;> intros <;> constConj_tac)
  | (apply Eq.symm; refine (shMemStore_frame ?_ _ _ _).1; constructor <;> intros <;> constConj_tac)
  | (apply Eq.symm; refine (shMemStore_frame ?_ _ _ _).2.1; constructor <;> intros <;> constConj_tac)
  | (apply Eq.symm; refine (shMemStore_frame ?_ _ _ _).2.2.1; constructor <;> intros <;> constConj_tac)
  | (apply Eq.symm; refine (shMemStore_frame ?_ _ _ _).2.2.2; constructor <;> intros <;> constConj_tac)
  | skip)

/-- Exact HOL `get_var_with_const` (`wordPropsScript.sml:137-160`): all 22
    original conjuncts in source order. -/
theorem getVarWithConst {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (ls : Option Nat) (x : Nat) (y : WordSemStateFiniteExact width C F) (fp : HolFiniteMapExact Nat (BitVec 64)) (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (xs : List (WordSemStackFrame width)) (sl : Nat) (sm : Option Nat) (ssize : Spt Nat) (m : BitVec width → WordLocW width) (md : BitVec width → Bool) (smd : BitVec width → Bool) (p : Nat → Nat → Nat) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (cb : WordSemBuffer width 8) (db : WordSemBuffer width width) (g : WordSemGcFun width) (hd : Nat) (clk : Nat) (tdep : Nat) (cd : Spt (Nat × WordLangProgHOL (BitVec width))) (b : Bool) (ffi : HolFfiState OtherF) :
    getVar x { y with localsSize := ls } = getVar x y ∧
    getVar x { y with fpRegs := fp } = getVar x y ∧
    getVar x { y with store := store } = getVar x y ∧
    getVar x { y with stack := xs } = getVar x y ∧
    getVar x { y with stackLimit := sl } = getVar x y ∧
    getVar x { y with stackMax := sm } = getVar x y ∧
    getVar x { y with stackSize := ssize } = getVar x y ∧
    getVar x { y with memory := m } = getVar x y ∧
    getVar x { y with mdomain := md } = getVar x y ∧
    getVar x { y with shMdomain := smd } = getVar x y ∧
    getVar x { y with permute := p } = getVar x y ∧
    getVar x { y with compile := c } = getVar x y ∧
    getVar x { y with compileOracle := co } = getVar x y ∧
    getVar x { y with codeBuffer := cb } = getVar x y ∧
    getVar x { y with dataBuffer := db } = getVar x y ∧
    getVar x { y with gcFun := g } = getVar x y ∧
    getVar x { y with handler := hd } = getVar x y ∧
    getVar x { y with clock := clk } = getVar x y ∧
    getVar x { y with termdep := tdep } = getVar x y ∧
    getVar x { y with code := cd } = getVar x y ∧
    getVar x { y with be := b } = getVar x y ∧
    getVar x ({ y with ffi := ffi } : WordSemStateFiniteExact width C OtherF) = getVar x y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `get_vars_with_const` (`wordPropsScript.sml:164-187`): all 22
    original conjuncts in source order. -/
theorem getVarsWithConst {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (ls : Option Nat) (x : List Nat) (y : WordSemStateFiniteExact width C F) (fp : HolFiniteMapExact Nat (BitVec 64)) (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (xs : List (WordSemStackFrame width)) (sl : Nat) (sm : Option Nat) (ssize : Spt Nat) (m : BitVec width → WordLocW width) (md : BitVec width → Bool) (smd : BitVec width → Bool) (p : Nat → Nat → Nat) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (cb : WordSemBuffer width 8) (db : WordSemBuffer width width) (g : WordSemGcFun width) (hd : Nat) (clk : Nat) (tdep : Nat) (cd : Spt (Nat × WordLangProgHOL (BitVec width))) (b : Bool) (ffi : HolFfiState OtherF) :
    WordSemStateFiniteExact.getVars x { y with localsSize := ls } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with fpRegs := fp } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with store := store } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with stack := xs } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with stackLimit := sl } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with stackMax := sm } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with stackSize := ssize } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with memory := m } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with mdomain := md } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with shMdomain := smd } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with permute := p } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with compile := c } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with compileOracle := co } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with codeBuffer := cb } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with dataBuffer := db } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with gcFun := g } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with handler := hd } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with clock := clk } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with termdep := tdep } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with code := cd } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x { y with be := b } = WordSemStateFiniteExact.getVars x y ∧
    WordSemStateFiniteExact.getVars x ({ y with ffi := ffi } : WordSemStateFiniteExact width C OtherF) = WordSemStateFiniteExact.getVars x y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `unset_var_with_const` (`wordPropsScript.sml:272-295`): all 22
    original conjuncts in source order. -/
theorem unsetVarWithConst {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (ls : Option Nat) (x : Nat) (z : WordSemStateFiniteExact width C F) (fp : HolFiniteMapExact Nat (BitVec 64)) (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (xs : List (WordSemStackFrame width)) (sl : Nat) (sm : Option Nat) (ssize : Spt Nat) (m : BitVec width → WordLocW width) (md : BitVec width → Bool) (smd : BitVec width → Bool) (p : Nat → Nat → Nat) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (cb : WordSemBuffer width 8) (db : WordSemBuffer width width) (g : WordSemGcFun width) (hd : Nat) (clk : Nat) (tdep : Nat) (cd : Spt (Nat × WordLangProgHOL (BitVec width))) (b : Bool) (ffi : HolFfiState OtherF) :
    unsetVar x { z with localsSize := ls } = { unsetVar x z with localsSize := ls } ∧
    unsetVar x { z with fpRegs := fp } = { unsetVar x z with fpRegs := fp } ∧
    unsetVar x { z with store := store } = { unsetVar x z with store := store } ∧
    unsetVar x { z with stack := xs } = { unsetVar x z with stack := xs } ∧
    unsetVar x { z with stackLimit := sl } = { unsetVar x z with stackLimit := sl } ∧
    unsetVar x { z with stackMax := sm } = { unsetVar x z with stackMax := sm } ∧
    unsetVar x { z with stackSize := ssize } = { unsetVar x z with stackSize := ssize } ∧
    unsetVar x { z with memory := m } = { unsetVar x z with memory := m } ∧
    unsetVar x { z with mdomain := md } = { unsetVar x z with mdomain := md } ∧
    unsetVar x { z with shMdomain := smd } = { unsetVar x z with shMdomain := smd } ∧
    unsetVar x { z with permute := p } = { unsetVar x z with permute := p } ∧
    unsetVar x { z with compile := c } = { unsetVar x z with compile := c } ∧
    unsetVar x { z with compileOracle := co } = { unsetVar x z with compileOracle := co } ∧
    unsetVar x { z with codeBuffer := cb } = { unsetVar x z with codeBuffer := cb } ∧
    unsetVar x { z with dataBuffer := db } = { unsetVar x z with dataBuffer := db } ∧
    unsetVar x { z with gcFun := g } = { unsetVar x z with gcFun := g } ∧
    unsetVar x { z with handler := hd } = { unsetVar x z with handler := hd } ∧
    unsetVar x { z with clock := clk } = { unsetVar x z with clock := clk } ∧
    unsetVar x { z with termdep := tdep } = { unsetVar x z with termdep := tdep } ∧
    unsetVar x { z with code := cd } = { unsetVar x z with code := cd } ∧
    unsetVar x { z with be := b } = { unsetVar x z with be := b } ∧
    unsetVar x ({ z with ffi := ffi } : WordSemStateFiniteExact width C OtherF) = { unsetVar x z with ffi := ffi } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `set_vars_with_const` (`wordPropsScript.sml:326-349`): all 22
    original conjuncts in source order. -/
theorem setVarsWithConst {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (ls : Option Nat) (x : List Nat) (y : List (WordLocW width)) (z : WordSemStateFiniteExact width C F) (fp : HolFiniteMapExact Nat (BitVec 64)) (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (xs : List (WordSemStackFrame width)) (sl : Nat) (sm : Option Nat) (ssize : Spt Nat) (m : BitVec width → WordLocW width) (md : BitVec width → Bool) (smd : BitVec width → Bool) (p : Nat → Nat → Nat) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (cb : WordSemBuffer width 8) (db : WordSemBuffer width width) (g : WordSemGcFun width) (hd : Nat) (clk : Nat) (tdep : Nat) (cd : Spt (Nat × WordLangProgHOL (BitVec width))) (b : Bool) (ffi : HolFfiState OtherF) :
    setVars x y { z with localsSize := ls } = { setVars x y z with localsSize := ls } ∧
    setVars x y { z with fpRegs := fp } = { setVars x y z with fpRegs := fp } ∧
    setVars x y { z with store := store } = { setVars x y z with store := store } ∧
    setVars x y { z with stack := xs } = { setVars x y z with stack := xs } ∧
    setVars x y { z with stackLimit := sl } = { setVars x y z with stackLimit := sl } ∧
    setVars x y { z with stackMax := sm } = { setVars x y z with stackMax := sm } ∧
    setVars x y { z with stackSize := ssize } = { setVars x y z with stackSize := ssize } ∧
    setVars x y { z with memory := m } = { setVars x y z with memory := m } ∧
    setVars x y { z with mdomain := md } = { setVars x y z with mdomain := md } ∧
    setVars x y { z with shMdomain := smd } = { setVars x y z with shMdomain := smd } ∧
    setVars x y { z with permute := p } = { setVars x y z with permute := p } ∧
    setVars x y { z with compile := c } = { setVars x y z with compile := c } ∧
    setVars x y { z with compileOracle := co } = { setVars x y z with compileOracle := co } ∧
    setVars x y { z with codeBuffer := cb } = { setVars x y z with codeBuffer := cb } ∧
    setVars x y { z with dataBuffer := db } = { setVars x y z with dataBuffer := db } ∧
    setVars x y { z with gcFun := g } = { setVars x y z with gcFun := g } ∧
    setVars x y { z with handler := hd } = { setVars x y z with handler := hd } ∧
    setVars x y { z with clock := clk } = { setVars x y z with clock := clk } ∧
    setVars x y { z with termdep := tdep } = { setVars x y z with termdep := tdep } ∧
    setVars x y { z with code := cd } = { setVars x y z with code := cd } ∧
    setVars x y { z with be := b } = { setVars x y z with be := b } ∧
    setVars x y ({ z with ffi := ffi } : WordSemStateFiniteExact width C OtherF) = { setVars x y z with ffi := ffi } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `get_store_with_const` (`wordPropsScript.sml:353-376`): all 22
    original conjuncts in source order. -/
theorem getStoreWithConst {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (l : Spt (WordLocW width)) (x : WordStoreHOL) (y : WordSemStateFiniteExact width C F) (ls : Option Nat) (fp : HolFiniteMapExact Nat (BitVec 64)) (xs : List (WordSemStackFrame width)) (sl : Nat) (sm : Option Nat) (ssize : Spt Nat) (m : BitVec width → WordLocW width) (md : BitVec width → Bool) (smd : BitVec width → Bool) (p : Nat → Nat → Nat) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (cb : WordSemBuffer width 8) (db : WordSemBuffer width width) (g : WordSemGcFun width) (hd : Nat) (clk : Nat) (tdep : Nat) (cd : Spt (Nat × WordLangProgHOL (BitVec width))) (b : Bool) (ffi : HolFfiState OtherF) :
    getStore x { y with locals := l } = getStore x y ∧
    getStore x { y with localsSize := ls } = getStore x y ∧
    getStore x { y with fpRegs := fp } = getStore x y ∧
    getStore x { y with stack := xs } = getStore x y ∧
    getStore x { y with stackLimit := sl } = getStore x y ∧
    getStore x { y with stackMax := sm } = getStore x y ∧
    getStore x { y with stackSize := ssize } = getStore x y ∧
    getStore x { y with memory := m } = getStore x y ∧
    getStore x { y with mdomain := md } = getStore x y ∧
    getStore x { y with shMdomain := smd } = getStore x y ∧
    getStore x { y with permute := p } = getStore x y ∧
    getStore x { y with compile := c } = getStore x y ∧
    getStore x { y with compileOracle := co } = getStore x y ∧
    getStore x { y with codeBuffer := cb } = getStore x y ∧
    getStore x { y with dataBuffer := db } = getStore x y ∧
    getStore x { y with gcFun := g } = getStore x y ∧
    getStore x { y with handler := hd } = getStore x y ∧
    getStore x { y with clock := clk } = getStore x y ∧
    getStore x { y with termdep := tdep } = getStore x y ∧
    getStore x { y with code := cd } = getStore x y ∧
    getStore x { y with be := b } = getStore x y ∧
    getStore x ({ y with ffi := ffi } : WordSemStateFiniteExact width C OtherF) = getStore x y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `set_store_with_const` (`wordPropsScript.sml:407-430`): all 22
    original conjuncts in source order. -/
theorem setStoreWithConst {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (l : Spt (WordLocW width)) (x : WordStoreHOL) (y : WordLocW width) (z : WordSemStateFiniteExact width C F) (ls : Option Nat) (fp : HolFiniteMapExact Nat (BitVec 64)) (xs : List (WordSemStackFrame width)) (sl : Nat) (sm : Option Nat) (ssize : Spt Nat) (m : BitVec width → WordLocW width) (md : BitVec width → Bool) (smd : BitVec width → Bool) (p : Nat → Nat → Nat) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (cb : WordSemBuffer width 8) (db : WordSemBuffer width width) (g : WordSemGcFun width) (hd : Nat) (clk : Nat) (tdep : Nat) (cd : Spt (Nat × WordLangProgHOL (BitVec width))) (b : Bool) (ffi : HolFfiState OtherF) :
    setStore x y { z with locals := l } = { setStore x y z with locals := l } ∧
    setStore x y { z with localsSize := ls } = { setStore x y z with localsSize := ls } ∧
    setStore x y { z with fpRegs := fp } = { setStore x y z with fpRegs := fp } ∧
    setStore x y { z with stack := xs } = { setStore x y z with stack := xs } ∧
    setStore x y { z with stackLimit := sl } = { setStore x y z with stackLimit := sl } ∧
    setStore x y { z with stackMax := sm } = { setStore x y z with stackMax := sm } ∧
    setStore x y { z with stackSize := ssize } = { setStore x y z with stackSize := ssize } ∧
    setStore x y { z with memory := m } = { setStore x y z with memory := m } ∧
    setStore x y { z with mdomain := md } = { setStore x y z with mdomain := md } ∧
    setStore x y { z with shMdomain := smd } = { setStore x y z with shMdomain := smd } ∧
    setStore x y { z with permute := p } = { setStore x y z with permute := p } ∧
    setStore x y { z with compile := c } = { setStore x y z with compile := c } ∧
    setStore x y { z with compileOracle := co } = { setStore x y z with compileOracle := co } ∧
    setStore x y { z with codeBuffer := cb } = { setStore x y z with codeBuffer := cb } ∧
    setStore x y { z with dataBuffer := db } = { setStore x y z with dataBuffer := db } ∧
    setStore x y { z with gcFun := g } = { setStore x y z with gcFun := g } ∧
    setStore x y { z with handler := hd } = { setStore x y z with handler := hd } ∧
    setStore x y { z with clock := clk } = { setStore x y z with clock := clk } ∧
    setStore x y { z with termdep := tdep } = { setStore x y z with termdep := tdep } ∧
    setStore x y { z with code := cd } = { setStore x y z with code := cd } ∧
    setStore x y { z with be := b } = { setStore x y z with be := b } ∧
    setStore x y ({ z with ffi := ffi } : WordSemStateFiniteExact width C OtherF) = { setStore x y z with ffi := ffi } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `push_env_with_const` (`wordPropsScript.sml:461-468`): all 6
    original conjuncts in source order. -/
theorem pushEnvWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (x : Spt (WordLocW width) × Spt (WordLocW width)) (y : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) (z : WordSemStateFiniteExact width C F) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (termdep : Nat) (l : Spt (WordLocW width)) :
    pushEnv x y { z with clock := k } = { pushEnv x y z with clock := k } ∧
    pushEnv x y { z with compile := c } = { pushEnv x y z with compile := c } ∧
    pushEnv x y { z with compileOracle := co } = { pushEnv x y z with compileOracle := co } ∧
    pushEnv x y { z with code := code } = { pushEnv x y z with code := code } ∧
    pushEnv x y { z with termdep := termdep } = { pushEnv x y z with termdep := termdep } ∧
    pushEnv x y { z with locals := l } = { pushEnv x y z with locals := l } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `pop_env_with_const` (`wordPropsScript.sml:501-510`): all 8
    original conjuncts in source order. -/
theorem popEnvWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (z : WordSemStateFiniteExact width C F) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (termdep : Nat) (perm : Nat → Nat → Nat) (l : Spt (WordLocW width)) (ls : Option Nat) :
    popEnv { z with clock := k } = (popEnv z).map (fun s => { s with clock := k }) ∧
    popEnv { z with compile := c } = (popEnv z).map (fun s => { s with compile := c }) ∧
    popEnv { z with compileOracle := co } = (popEnv z).map (fun s => { s with compileOracle := co }) ∧
    popEnv { z with code := code } = (popEnv z).map (fun s => { s with code := code }) ∧
    popEnv { z with termdep := termdep } = (popEnv z).map (fun s => { s with termdep := termdep }) ∧
    popEnv { z with permute := perm } = (popEnv z).map (fun s => { s with permute := perm }) ∧
    popEnv { z with locals := l } = popEnv z ∧
    popEnv { z with localsSize := ls } = popEnv z := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `call_env_with_const` (`wordPropsScript.sml:558-567`): all 8
    original conjuncts in source order. -/
theorem callEnvWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (l : Spt (WordLocW width)) (x : List (WordLocW width)) (ss : Option Nat) (y : WordSemStateFiniteExact width C F) (k : Nat) (termdep : Nat) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (perm : Nat → Nat → Nat) :
    WordSemStateFiniteExact.callEnv x ss { y with locals := l } = WordSemStateFiniteExact.callEnv x ss y ∧
    WordSemStateFiniteExact.callEnv x ss { y with clock := k } = { WordSemStateFiniteExact.callEnv x ss y with clock := k } ∧
    WordSemStateFiniteExact.callEnv x ss { y with termdep := termdep } = { WordSemStateFiniteExact.callEnv x ss y with termdep := termdep } ∧
    WordSemStateFiniteExact.callEnv x ss { y with compile := c } = { WordSemStateFiniteExact.callEnv x ss y with compile := c } ∧
    WordSemStateFiniteExact.callEnv x ss { y with compileOracle := co } = { WordSemStateFiniteExact.callEnv x ss y with compileOracle := co } ∧
    WordSemStateFiniteExact.callEnv x ss { y with code := code } = { WordSemStateFiniteExact.callEnv x ss y with code := code } ∧
    WordSemStateFiniteExact.callEnv x ss { y with handler := k } = { WordSemStateFiniteExact.callEnv x ss y with handler := k } ∧
    WordSemStateFiniteExact.callEnv x ss { y with permute := perm } = { WordSemStateFiniteExact.callEnv x ss y with permute := perm } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `flush_state_with_const` (`wordPropsScript.sml:588-595`): all 6
    original conjuncts in source order. -/
theorem flushStateWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (l : Spt (WordLocW width)) (b : Bool) (y : WordSemStateFiniteExact width C F) (ls : Option Nat) (xs : List (WordSemStackFrame width)) (p : Nat → Nat → Nat) (sm : Option Nat) (k : Nat) :
    flushState b { y with locals := l } = flushState b y ∧
    flushState b { y with localsSize := ls } = flushState b y ∧
    flushState true { y with stack := xs } = flushState true y ∧
    flushState b { y with permute := p } = { flushState b y with permute := p } ∧
    flushState b { y with stackMax := sm } = { flushState b y with stackMax := sm } ∧
    flushState b { y with clock := k } = { flushState b y with clock := k } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `has_space_with_const` (`wordPropsScript.sml:599-608`): all 8
    original conjuncts in source order. -/
theorem hasSpaceWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (x : WordLocW width) (y : WordSemStateFiniteExact width C F) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (termdep : Nat) (l : Spt (WordLocW width)) (ls : Option Nat) (xs : List (WordSemStackFrame width)) :
    hasSpace x { y with clock := k } = hasSpace x y ∧
    hasSpace x { y with compile := c } = hasSpace x y ∧
    hasSpace x { y with compileOracle := co } = hasSpace x y ∧
    hasSpace x { y with code := code } = hasSpace x y ∧
    hasSpace x { y with termdep := termdep } = hasSpace x y ∧
    hasSpace x { y with locals := l } = hasSpace x y ∧
    hasSpace x { y with localsSize := ls } = hasSpace x y ∧
    hasSpace x { y with stack := xs } = hasSpace x y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `gc_with_const` (`wordPropsScript.sml:632-641`): all 8
    original conjuncts in source order. -/
theorem gcWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (x : WordSemStateFiniteExact width C F) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (perm : Nat → Nat → Nat) (t : Nat) (l : Spt (WordLocW width)) (ls : Option Nat) :
    gc { x with clock := k } = (gc x).map (fun s => { s with clock := k }) ∧
    gc { x with compile := c } = (gc x).map (fun s => { s with compile := c }) ∧
    gc { x with compileOracle := co } = (gc x).map (fun s => { s with compileOracle := co }) ∧
    gc { x with code := code } = (gc x).map (fun s => { s with code := code }) ∧
    gc { x with permute := perm } = (gc x).map (fun s => { s with permute := perm }) ∧
    gc { x with termdep := t } = (gc x).map (fun s => { s with termdep := t }) ∧
    gc { x with locals := l } = (gc x).map (fun s => { s with locals := l }) ∧
    gc { x with localsSize := ls } = (gc x).map (fun s => { s with localsSize := ls }) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `alloc_with_const` (`wordPropsScript.sml:690-696`): all 5
    original conjuncts in source order. -/
theorem allocWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (c : BitVec width) (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact width C F) (t : Nat) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (compile_oracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (comp : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) :
    alloc c names { s with clock := k } = Prod.map id (fun s => { s with clock := k }) (alloc c names s) ∧
    alloc c names { s with termdep := t } = Prod.map id (fun s => { s with termdep := t }) (alloc c names s) ∧
    alloc c names { s with code := code } = Prod.map id (fun s => { s with code := code }) (alloc c names s) ∧
    alloc c names { s with compileOracle := compile_oracle } = Prod.map id (fun s => { s with compileOracle := compile_oracle }) (alloc c names s) ∧
    alloc c names { s with compile := comp } = Prod.map id (fun s => { s with compile := comp }) (alloc c names s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `get_fp_var_with_const` (`wordPropsScript.sml:700-723`): all 22
    original conjuncts in source order. -/
theorem getFpVarWithConst {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (l : Spt (WordLocW width)) (x : Nat) (y : WordSemStateFiniteExact width C F) (ls : Option Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (xs : List (WordSemStackFrame width)) (sl : Nat) (sm : Option Nat) (ssize : Spt Nat) (m : BitVec width → WordLocW width) (md : BitVec width → Bool) (smd : BitVec width → Bool) (p : Nat → Nat → Nat) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (cb : WordSemBuffer width 8) (db : WordSemBuffer width width) (g : WordSemGcFun width) (hd : Nat) (clk : Nat) (tdep : Nat) (cd : Spt (Nat × WordLangProgHOL (BitVec width))) (b : Bool) (ffi : HolFfiState OtherF) :
    getFpVar x { y with locals := l } = getFpVar x y ∧
    getFpVar x { y with localsSize := ls } = getFpVar x y ∧
    getFpVar x { y with store := store } = getFpVar x y ∧
    getFpVar x { y with stack := xs } = getFpVar x y ∧
    getFpVar x { y with stackLimit := sl } = getFpVar x y ∧
    getFpVar x { y with stackMax := sm } = getFpVar x y ∧
    getFpVar x { y with stackSize := ssize } = getFpVar x y ∧
    getFpVar x { y with memory := m } = getFpVar x y ∧
    getFpVar x { y with mdomain := md } = getFpVar x y ∧
    getFpVar x { y with shMdomain := smd } = getFpVar x y ∧
    getFpVar x { y with permute := p } = getFpVar x y ∧
    getFpVar x { y with compile := c } = getFpVar x y ∧
    getFpVar x { y with compileOracle := co } = getFpVar x y ∧
    getFpVar x { y with codeBuffer := cb } = getFpVar x y ∧
    getFpVar x { y with dataBuffer := db } = getFpVar x y ∧
    getFpVar x { y with gcFun := g } = getFpVar x y ∧
    getFpVar x { y with handler := hd } = getFpVar x y ∧
    getFpVar x { y with clock := clk } = getFpVar x y ∧
    getFpVar x { y with termdep := tdep } = getFpVar x y ∧
    getFpVar x { y with code := cd } = getFpVar x y ∧
    getFpVar x { y with be := b } = getFpVar x y ∧
    getFpVar x ({ y with ffi := ffi } : WordSemStateFiniteExact width C OtherF) = getFpVar x y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `set_fp_var_with_const` (`wordPropsScript.sml:754-777`): all 22
    original conjuncts in source order. -/
theorem setFpVarWithConst {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (l : Spt (WordLocW width)) (x : Nat) (y : BitVec 64) (z : WordSemStateFiniteExact width C F) (ls : Option Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (xs : List (WordSemStackFrame width)) (sl : Nat) (sm : Option Nat) (ssize : Spt Nat) (m : BitVec width → WordLocW width) (md : BitVec width → Bool) (smd : BitVec width → Bool) (p : Nat → Nat → Nat) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (cb : WordSemBuffer width 8) (db : WordSemBuffer width width) (g : WordSemGcFun width) (hd : Nat) (clk : Nat) (tdep : Nat) (cd : Spt (Nat × WordLangProgHOL (BitVec width))) (b : Bool) (ffi : HolFfiState OtherF) :
    setFpVar x y { z with locals := l } = { setFpVar x y z with locals := l } ∧
    setFpVar x y { z with localsSize := ls } = { setFpVar x y z with localsSize := ls } ∧
    setFpVar x y { z with store := store } = { setFpVar x y z with store := store } ∧
    setFpVar x y { z with stack := xs } = { setFpVar x y z with stack := xs } ∧
    setFpVar x y { z with stackLimit := sl } = { setFpVar x y z with stackLimit := sl } ∧
    setFpVar x y { z with stackMax := sm } = { setFpVar x y z with stackMax := sm } ∧
    setFpVar x y { z with stackSize := ssize } = { setFpVar x y z with stackSize := ssize } ∧
    setFpVar x y { z with memory := m } = { setFpVar x y z with memory := m } ∧
    setFpVar x y { z with mdomain := md } = { setFpVar x y z with mdomain := md } ∧
    setFpVar x y { z with shMdomain := smd } = { setFpVar x y z with shMdomain := smd } ∧
    setFpVar x y { z with permute := p } = { setFpVar x y z with permute := p } ∧
    setFpVar x y { z with compile := c } = { setFpVar x y z with compile := c } ∧
    setFpVar x y { z with compileOracle := co } = { setFpVar x y z with compileOracle := co } ∧
    setFpVar x y { z with codeBuffer := cb } = { setFpVar x y z with codeBuffer := cb } ∧
    setFpVar x y { z with dataBuffer := db } = { setFpVar x y z with dataBuffer := db } ∧
    setFpVar x y { z with gcFun := g } = { setFpVar x y z with gcFun := g } ∧
    setFpVar x y { z with handler := hd } = { setFpVar x y z with handler := hd } ∧
    setFpVar x y { z with clock := clk } = { setFpVar x y z with clock := clk } ∧
    setFpVar x y { z with termdep := tdep } = { setFpVar x y z with termdep := tdep } ∧
    setFpVar x y { z with code := cd } = { setFpVar x y z with code := cd } ∧
    setFpVar x y { z with be := b } = { setFpVar x y z with be := b } ∧
    setFpVar x y ({ z with ffi := ffi } : WordSemStateFiniteExact width C OtherF) = { setFpVar x y z with ffi := ffi } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `mem_load_with_const` (`wordPropsScript.sml:781-790`): all 8
    original conjuncts in source order. -/
theorem memLoadWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (l : Spt (WordLocW width)) (x : BitVec width) (y : WordSemStateFiniteExact width C F) (td : Nat) (k : Nat) (xs : List (WordSemStackFrame width)) (perm : Nat → Nat → Nat) (c : Spt (Nat × WordLangProgHOL (BitVec width))) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) :
    memLoad x { y with locals := l } = memLoad x y ∧
    memLoad x { y with termdep := td } = memLoad x y ∧
    memLoad x { y with clock := k } = memLoad x y ∧
    memLoad x { y with stack := xs } = memLoad x y ∧
    memLoad x { y with permute := perm } = memLoad x y ∧
    memLoad x { y with code := c } = memLoad x y ∧
    memLoad x { y with compileOracle := co } = memLoad x y ∧
    memLoad x { y with compile := cc } = memLoad x y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `mem_store_with_const` (`wordPropsScript.sml:819-827`): all 7
    original conjuncts in source order. -/
theorem memStoreWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (l : Spt (WordLocW width)) (x : BitVec width) (z : WordLocW width) (y : WordSemStateFiniteExact width C F) (k : Nat) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (perm : Nat → Nat → Nat) (xs : List (WordSemStackFrame width)) :
    memStore x z { y with locals := l } = (memStore x z y).map (fun s => { s with locals := l }) ∧
    memStore x z { y with clock := k } = (memStore x z y).map (fun s => { s with clock := k }) ∧
    memStore x z { y with code := code } = (memStore x z y).map (fun s => { s with code := code }) ∧
    memStore x z { y with compile := c } = (memStore x z y).map (fun s => { s with compile := c }) ∧
    memStore x z { y with compileOracle := co } = (memStore x z y).map (fun s => { s with compileOracle := co }) ∧
    memStore x z { y with permute := perm } = (memStore x z y).map (fun s => { s with permute := perm }) ∧
    memStore x z { y with stack := xs } = (memStore x z y).map (fun s => { s with stack := xs }) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `word_exp_with_const` (`wordPropsScript.sml:831-840`): all 7
    original conjuncts in source order. -/
theorem wordExpWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (y : WordLangExpHOL (BitVec width)) (x : WordSemStateFiniteExact width C F) (xs : List (WordSemStackFrame width)) (perm : Nat → Nat → Nat) (termdep : Nat) (c : Spt (Nat × WordLangProgHOL (BitVec width))) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) :
    wordExp { x with clock := k } y = wordExp x y ∧
    wordExp { x with stack := xs } y = wordExp x y ∧
    wordExp { x with permute := perm } y = wordExp x y ∧
    wordExp { x with termdep := termdep } y = wordExp x y ∧
    wordExp { x with code := c } y = wordExp x y ∧
    wordExp { x with compileOracle := co } y = wordExp x y ∧
    wordExp { x with compile := cc } y = wordExp x y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `assign_with_const` (`wordPropsScript.sml:877-884`): all 6
    original conjuncts in source order. -/
theorem assignWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (x : Nat) (y : WordLangExpHOL (BitVec width)) (z : WordSemStateFiniteExact width C F) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (perm : Nat → Nat → Nat) (xs : List (WordSemStackFrame width)) :
    assign x y { z with clock := k } = (assign x y z).map (fun s => { s with clock := k }) ∧
    assign x y { z with code := code } = (assign x y z).map (fun s => { s with code := code }) ∧
    assign x y { z with compile := c } = (assign x y z).map (fun s => { s with compile := c }) ∧
    assign x y { z with compileOracle := co } = (assign x y z).map (fun s => { s with compileOracle := co }) ∧
    assign x y { z with permute := perm } = (assign x y z).map (fun s => { s with permute := perm }) ∧
    assign x y { z with stack := xs } = (assign x y z).map (fun s => { s with stack := xs }) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `inst_with_const` (`wordPropsScript.sml:888-895`): all 6
    original conjuncts in source order. -/
theorem instWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (i : WordLangInst (BitVec width)) (s : WordSemStateFiniteExact width C F) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (perm : Nat → Nat → Nat) (xs : List (WordSemStackFrame width)) :
    inst i { s with clock := k } = (inst i s).map (fun s => { s with clock := k }) ∧
    inst i { s with code := code } = (inst i s).map (fun s => { s with code := code }) ∧
    inst i { s with compile := c } = (inst i s).map (fun s => { s with compile := c }) ∧
    inst i { s with compileOracle := co } = (inst i s).map (fun s => { s with compileOracle := co }) ∧
    inst i { s with permute := perm } = (inst i s).map (fun s => { s with permute := perm }) ∧
    inst i { s with stack := xs } = (inst i s).map (fun s => { s with stack := xs }) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `jump_exc_with_const` (`wordPropsScript.sml:963-966`): all 2
    original conjuncts in source order. -/
theorem jumpExcWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (s : WordSemStateFiniteExact width C F) (perm : Nat → Nat → Nat) :
    jumpExc { s with clock := k } = (jumpExc s).map (fun p => ({ p.1 with clock := k }, p.2)) ∧
    jumpExc { s with permute := perm } = (jumpExc s).map (fun p => ({ p.1 with permute := perm }, p.2)) := by
  refine ⟨?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `get_var_imm_with_const` (`wordPropsScript.sml:970-978`): all 7
    original conjuncts in source order. -/
theorem getVarImmWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (x : WordRegImm (BitVec width)) (y : WordSemStateFiniteExact width C F) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (compile : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (compile_oracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (td : Nat) (xs : List (WordSemStackFrame width)) (perm : Nat → Nat → Nat) :
    WordSemStateFiniteExact.getVarImm x { y with clock := k } = WordSemStateFiniteExact.getVarImm x y ∧
    WordSemStateFiniteExact.getVarImm x { y with code := code } = WordSemStateFiniteExact.getVarImm x y ∧
    WordSemStateFiniteExact.getVarImm x { y with compile := compile } = WordSemStateFiniteExact.getVarImm x y ∧
    WordSemStateFiniteExact.getVarImm x { y with compileOracle := compile_oracle } = WordSemStateFiniteExact.getVarImm x y ∧
    WordSemStateFiniteExact.getVarImm x { y with termdep := td } = WordSemStateFiniteExact.getVarImm x y ∧
    WordSemStateFiniteExact.getVarImm x { y with stack := xs } = WordSemStateFiniteExact.getVarImm x y ∧
    WordSemStateFiniteExact.getVarImm x { y with permute := perm } = WordSemStateFiniteExact.getVarImm x y := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `sh_mem_set_var_with_const` (`wordPropsScript.sml:1187-1192`): all 2
    original conjuncts in source order. -/
theorem shMemSetVarWithConst {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {clockRw : Nat} [NeZero clockRw] {C : Type} {F : Type}
    (p : Nat → Nat → Nat) (res : Option (HolFfiResult F)) (v : Nat) (s : WordSemStateFiniteExact width C F) (k : Nat) :
    shMemSetVar (rw := rw) res v { s with permute := p } = Prod.map id (fun s => { s with permute := p }) (shMemSetVar (rw := rw) res v s) ∧
    shMemSetVar (rw := clockRw) res v { s with clock := k } = Prod.map id (fun s => { s with clock := k }) (shMemSetVar (rw := clockRw) res v s) := by
  refine ⟨?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `sh_mem_load_with_const` (`wordPropsScript.sml:1200-1205`): all 4
    original conjuncts in source order. -/
theorem shMemLoadWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (l : Spt (WordLocW width)) (a : BitVec width) (s : WordSemStateFiniteExact width C F) (p : Nat → Nat → Nat) (k : Nat) (xs : List (WordSemStackFrame width)) :
    shMemLoad a { s with locals := l } = shMemLoad a s ∧
    shMemLoad a { s with permute := p } = shMemLoad a s ∧
    shMemLoad a { s with clock := k } = shMemLoad a s ∧
    shMemLoad a { s with stack := xs } = shMemLoad a s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `sh_mem_load_byte_with_const` (`wordPropsScript.sml:1209-1214`): all 4
    original conjuncts in source order. -/
theorem shMemLoadByteWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (l : Spt (WordLocW width)) (a : BitVec width) (s : WordSemStateFiniteExact width C F) (p : Nat → Nat → Nat) (k : Nat) (xs : List (WordSemStackFrame width)) :
    shMemLoadByte a { s with locals := l } = shMemLoadByte a s ∧
    shMemLoadByte a { s with permute := p } = shMemLoadByte a s ∧
    shMemLoadByte a { s with clock := k } = shMemLoadByte a s ∧
    shMemLoadByte a { s with stack := xs } = shMemLoadByte a s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `sh_mem_load16_with_const` (`wordPropsScript.sml:1218-1223`): all 4
    original conjuncts in source order. -/
theorem shMemLoad16WithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (l : Spt (WordLocW width)) (a : BitVec width) (s : WordSemStateFiniteExact width C F) (p : Nat → Nat → Nat) (k : Nat) (xs : List (WordSemStackFrame width)) :
    shMemLoad16 a { s with locals := l } = shMemLoad16 a s ∧
    shMemLoad16 a { s with permute := p } = shMemLoad16 a s ∧
    shMemLoad16 a { s with clock := k } = shMemLoad16 a s ∧
    shMemLoad16 a { s with stack := xs } = shMemLoad16 a s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `sh_mem_load32_with_const` (`wordPropsScript.sml:1227-1232`): all 4
    original conjuncts in source order. -/
theorem shMemLoad32WithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (l : Spt (WordLocW width)) (a : BitVec width) (s : WordSemStateFiniteExact width C F) (p : Nat → Nat → Nat) (k : Nat) (xs : List (WordSemStackFrame width)) :
    shMemLoad32 a { s with locals := l } = shMemLoad32 a s ∧
    shMemLoad32 a { s with permute := p } = shMemLoad32 a s ∧
    shMemLoad32 a { s with clock := k } = shMemLoad32 a s ∧
    shMemLoad32 a { s with stack := xs } = shMemLoad32 a s := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `sh_mem_store_with_const` (`wordPropsScript.sml:1236-1241`): all 2
    original conjuncts in source order. -/
theorem shMemStoreWithConst {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {clockRw : Nat} [NeZero clockRw] {C : Type} {F : Type}
    (p : Nat → Nat → Nat) (a : BitVec width) (w : BitVec width) (s : WordSemStateFiniteExact width C F) (k : Nat) :
    shMemStore (rw := rw) a w { s with permute := p } = Prod.map id (fun s => { s with permute := p }) (shMemStore (rw := rw) a w s) ∧
    shMemStore (rw := clockRw) a w { s with clock := k } = Prod.map id (fun s => { s with clock := k }) (shMemStore (rw := clockRw) a w s) := by
  refine ⟨?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `sh_mem_store_byte_with_const` (`wordPropsScript.sml:1245-1250`): all 2
    original conjuncts in source order. -/
theorem shMemStoreByteWithConst {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {clockRw : Nat} [NeZero clockRw] {C : Type} {F : Type}
    (p : Nat → Nat → Nat) (a : BitVec width) (w : BitVec width) (s : WordSemStateFiniteExact width C F) (k : Nat) :
    shMemStoreByte (rw := rw) a w { s with permute := p } = Prod.map id (fun s => { s with permute := p }) (shMemStoreByte (rw := rw) a w s) ∧
    shMemStoreByte (rw := clockRw) a w { s with clock := k } = Prod.map id (fun s => { s with clock := k }) (shMemStoreByte (rw := clockRw) a w s) := by
  refine ⟨?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `sh_mem_store16_with_const` (`wordPropsScript.sml:1254-1259`): all 2
    original conjuncts in source order. -/
theorem shMemStore16WithConst {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {clockRw : Nat} [NeZero clockRw] {C : Type} {F : Type}
    (p : Nat → Nat → Nat) (a : BitVec width) (w : BitVec width) (s : WordSemStateFiniteExact width C F) (k : Nat) :
    shMemStore16 (rw := rw) a w { s with permute := p } = Prod.map id (fun s => { s with permute := p }) (shMemStore16 (rw := rw) a w s) ∧
    shMemStore16 (rw := clockRw) a w { s with clock := k } = Prod.map id (fun s => { s with clock := k }) (shMemStore16 (rw := clockRw) a w s) := by
  refine ⟨?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `sh_mem_store32_with_const` (`wordPropsScript.sml:1263-1268`): all 2
    original conjuncts in source order. -/
theorem shMemStore32WithConst {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {clockRw : Nat} [NeZero clockRw] {C : Type} {F : Type}
    (p : Nat → Nat → Nat) (a : BitVec width) (w : BitVec width) (s : WordSemStateFiniteExact width C F) (k : Nat) :
    shMemStore32 (rw := rw) a w { s with permute := p } = Prod.map id (fun s => { s with permute := p }) (shMemStore32 (rw := rw) a w s) ∧
    shMemStore32 (rw := clockRw) a w { s with clock := k } = Prod.map id (fun s => { s with clock := k }) (shMemStore32 (rw := clockRw) a w s) := by
  refine ⟨?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `share_inst_with_const` (`wordPropsScript.sml:1272-1277`): all 2
    original conjuncts in source order. -/
theorem shareInstWithConst {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {clockRw : Nat} [NeZero clockRw] {C : Type} {F : Type}
    (p : Nat → Nat → Nat) (op : WordMemOp) (v : Nat) (c : BitVec width) (s : WordSemStateFiniteExact width C F) (k : Nat) :
    shareInst (rw := rw) op v c { s with permute := p } = Prod.map id (fun s => { s with permute := p }) (shareInst (rw := rw) op v c s) ∧
    shareInst (rw := clockRw) op v c { s with clock := k } = Prod.map id (fun s => { s with clock := k }) (shareInst (rw := clockRw) op v c s) := by
  refine ⟨?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `cut_state_with_const` (`wordPropsScript.sml:1281-1288`): all 6
    original conjuncts in source order. -/
theorem cutStateWithConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (k : Nat) (x : WordLangCutsetsHOL) (z : WordSemStateFiniteExact width C F) (code : Spt (Nat × WordLangProgHOL (BitVec width))) (c : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) → Option (List (BitVec 8) × List (BitVec width) × C)) (co : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width))) (perm : Nat → Nat → Nat) (xs : List (WordSemStackFrame width)) :
    cutState x { z with clock := k } = (cutState x z).map (fun s => { s with clock := k }) ∧
    cutState x { z with code := code } = (cutState x z).map (fun s => { s with code := code }) ∧
    cutState x { z with compile := c } = (cutState x z).map (fun s => { s with compile := c }) ∧
    cutState x { z with compileOracle := co } = (cutState x z).map (fun s => { s with compileOracle := co }) ∧
    cutState x { z with permute := perm } = (cutState x z).map (fun s => { s with permute := perm }) ∧
    cutState x { z with stack := xs } = (cutState x z).map (fun s => { s with stack := xs }) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `unset_var_const` (`wordPropsScript.sml:245-268`): all 22
    original conjuncts in source order. -/
theorem unsetVarConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (z : WordSemStateFiniteExact width C F) :
    (unsetVar x z).localsSize = z.localsSize ∧
    (unsetVar x z).fpRegs = z.fpRegs ∧
    (unsetVar x z).store = z.store ∧
    (unsetVar x z).stack = z.stack ∧
    (unsetVar x z).stackLimit = z.stackLimit ∧
    (unsetVar x z).stackMax = z.stackMax ∧
    (unsetVar x z).stackSize = z.stackSize ∧
    (unsetVar x z).memory = z.memory ∧
    (unsetVar x z).mdomain = z.mdomain ∧
    (unsetVar x z).shMdomain = z.shMdomain ∧
    (unsetVar x z).permute = z.permute ∧
    (unsetVar x z).compile = z.compile ∧
    (unsetVar x z).compileOracle = z.compileOracle ∧
    (unsetVar x z).codeBuffer = z.codeBuffer ∧
    (unsetVar x z).dataBuffer = z.dataBuffer ∧
    (unsetVar x z).gcFun = z.gcFun ∧
    (unsetVar x z).handler = z.handler ∧
    (unsetVar x z).clock = z.clock ∧
    (unsetVar x z).termdep = z.termdep ∧
    (unsetVar x z).code = z.code ∧
    (unsetVar x z).be = z.be ∧
    (unsetVar x z).ffi = z.ffi := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `set_vars_const` (`wordPropsScript.sml:299-322`): all 22
    original conjuncts in source order. -/
theorem setVarsConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : List Nat) (y : List (WordLocW width)) (z : WordSemStateFiniteExact width C F) :
    (setVars x y z).localsSize = z.localsSize ∧
    (setVars x y z).fpRegs = z.fpRegs ∧
    (setVars x y z).store = z.store ∧
    (setVars x y z).stack = z.stack ∧
    (setVars x y z).stackLimit = z.stackLimit ∧
    (setVars x y z).stackMax = z.stackMax ∧
    (setVars x y z).stackSize = z.stackSize ∧
    (setVars x y z).memory = z.memory ∧
    (setVars x y z).mdomain = z.mdomain ∧
    (setVars x y z).shMdomain = z.shMdomain ∧
    (setVars x y z).permute = z.permute ∧
    (setVars x y z).compile = z.compile ∧
    (setVars x y z).compileOracle = z.compileOracle ∧
    (setVars x y z).codeBuffer = z.codeBuffer ∧
    (setVars x y z).dataBuffer = z.dataBuffer ∧
    (setVars x y z).gcFun = z.gcFun ∧
    (setVars x y z).handler = z.handler ∧
    (setVars x y z).clock = z.clock ∧
    (setVars x y z).termdep = z.termdep ∧
    (setVars x y z).code = z.code ∧
    (setVars x y z).be = z.be ∧
    (setVars x y z).ffi = z.ffi := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `push_env_const` (`wordPropsScript.sml:435-454`): all 18
    original conjuncts in source order. -/
theorem pushEnvConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Spt (WordLocW width) × Spt (WordLocW width)) (y : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) (z : WordSemStateFiniteExact width C F) :
    (pushEnv x y z).clock = z.clock ∧
    (pushEnv x y z).memory = z.memory ∧
    (pushEnv x y z).store = z.store ∧
    (pushEnv x none z).handler = z.handler ∧
    (pushEnv x y z).ffi = z.ffi ∧
    (pushEnv x y z).termdep = z.termdep ∧
    (pushEnv x y z).dataBuffer = z.dataBuffer ∧
    (pushEnv x y z).codeBuffer = z.codeBuffer ∧
    (pushEnv x y z).compile = z.compile ∧
    (pushEnv x y z).compileOracle = z.compileOracle ∧
    (pushEnv x y z).mdomain = z.mdomain ∧
    (pushEnv x y z).shMdomain = z.shMdomain ∧
    (pushEnv x y z).gcFun = z.gcFun ∧
    (pushEnv x y z).be = z.be ∧
    (pushEnv x y z).fpRegs = z.fpRegs ∧
    (pushEnv x y z).code = z.code ∧
    (pushEnv x y z).stackLimit = z.stackLimit ∧
    (pushEnv x y z).stackSize = z.stackSize := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `call_env_const` (`wordPropsScript.sml:535-554`): all 18
    original conjuncts in source order. -/
theorem callEnvConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : List (WordLocW width)) (ss : Option Nat) (y : WordSemStateFiniteExact width C F) :
    (WordSemStateFiniteExact.callEnv x ss y).store = y.store ∧
    (WordSemStateFiniteExact.callEnv x ss y).termdep = y.termdep ∧
    (WordSemStateFiniteExact.callEnv x ss y).clock = y.clock ∧
    (WordSemStateFiniteExact.callEnv x ss y).handler = y.handler ∧
    (WordSemStateFiniteExact.callEnv x ss y).stack = y.stack ∧
    (WordSemStateFiniteExact.callEnv x ss y).compileOracle = y.compileOracle ∧
    (WordSemStateFiniteExact.callEnv x ss y).compile = y.compile ∧
    (WordSemStateFiniteExact.callEnv x ss y).be = y.be ∧
    (WordSemStateFiniteExact.callEnv x ss y).memory = y.memory ∧
    (WordSemStateFiniteExact.callEnv x ss y).mdomain = y.mdomain ∧
    (WordSemStateFiniteExact.callEnv x ss y).shMdomain = y.shMdomain ∧
    (WordSemStateFiniteExact.callEnv x ss y).gcFun = y.gcFun ∧
    (WordSemStateFiniteExact.callEnv x ss y).ffi = y.ffi ∧
    (WordSemStateFiniteExact.callEnv x ss y).code = y.code ∧
    (WordSemStateFiniteExact.callEnv x ss y).codeBuffer = y.codeBuffer ∧
    (WordSemStateFiniteExact.callEnv x ss y).dataBuffer = y.dataBuffer ∧
    (WordSemStateFiniteExact.callEnv x ss y).stackLimit = y.stackLimit ∧
    (WordSemStateFiniteExact.callEnv x ss y).stackSize = y.stackSize := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `flush_state_const` (`wordPropsScript.sml:571-584`): all 12
    original conjuncts in source order. -/
theorem flushStateConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (b : Bool) (y : WordSemStateFiniteExact width C F) :
    (flushState b y).clock = y.clock ∧
    (flushState b y).compileOracle = y.compileOracle ∧
    (flushState b y).compile = y.compile ∧
    (flushState b y).be = y.be ∧
    (flushState b y).gcFun = y.gcFun ∧
    (flushState b y).ffi = y.ffi ∧
    (flushState b y).code = y.code ∧
    (flushState b y).codeBuffer = y.codeBuffer ∧
    (flushState b y).dataBuffer = y.dataBuffer ∧
    (flushState b y).stackLimit = y.stackLimit ∧
    (flushState b y).stackSize = y.stackSize ∧
    (flushState false y).stack = y.stack := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `set_fp_var_const` (`wordPropsScript.sml:727-750`): all 22
    original conjuncts in source order. -/
theorem setFpVarConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : BitVec 64) (z : WordSemStateFiniteExact width C F) :
    (setFpVar x y z).locals = z.locals ∧
    (setFpVar x y z).localsSize = z.localsSize ∧
    (setFpVar x y z).store = z.store ∧
    (setFpVar x y z).stack = z.stack ∧
    (setFpVar x y z).stackLimit = z.stackLimit ∧
    (setFpVar x y z).stackMax = z.stackMax ∧
    (setFpVar x y z).stackSize = z.stackSize ∧
    (setFpVar x y z).memory = z.memory ∧
    (setFpVar x y z).mdomain = z.mdomain ∧
    (setFpVar x y z).shMdomain = z.shMdomain ∧
    (setFpVar x y z).permute = z.permute ∧
    (setFpVar x y z).compile = z.compile ∧
    (setFpVar x y z).compileOracle = z.compileOracle ∧
    (setFpVar x y z).codeBuffer = z.codeBuffer ∧
    (setFpVar x y z).dataBuffer = z.dataBuffer ∧
    (setFpVar x y z).gcFun = z.gcFun ∧
    (setFpVar x y z).handler = z.handler ∧
    (setFpVar x y z).clock = z.clock ∧
    (setFpVar x y z).termdep = z.termdep ∧
    (setFpVar x y z).code = z.code ∧
    (setFpVar x y z).be = z.be ∧
    (setFpVar x y z).ffi = z.ffi := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals constConj_tac

/-- Exact HOL `state_const` (`wordPropsScript.sml:103-110`). -/
theorem stateConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) (l l' : Spt (WordLocW width)) (p p' : Nat → Nat → Nat)
    (clk clk' : Nat) (xs xs' : List (WordSemStackFrame width)) :
    (({ s with locals := l } : WordSemStateFiniteExact width C F) = { s with locals := l' } ↔ l = l') ∧
    (({ s with permute := p } : WordSemStateFiniteExact width C F) = { s with permute := p' } ↔ p = p') ∧
    (({ s with clock := clk } : WordSemStateFiniteExact width C F) = { s with clock := clk' } ↔
      clk = clk') ∧
    (({ s with stack := xs } : WordSemStateFiniteExact width C F) = { s with stack := xs' } ↔
      xs = xs') := by
  refine ⟨⟨fun h => congrArg (·.locals) h, fun h => h ▸ rfl⟩,
    ⟨fun h => congrArg (·.permute) h, fun h => h ▸ rfl⟩,
    ⟨fun h => congrArg (·.clock) h, fun h => h ▸ rfl⟩,
    ⟨fun h => congrArg (·.stack) h, fun h => h ▸ rfl⟩⟩

/-- Exact HOL `dec_clock_const` (`wordPropsScript.sml:982-1009`): all 24
    original conjuncts in source order. -/
theorem decClockConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (s : WordSemStateFiniteExact width C F) (locs : Spt (WordLocW width)) (p : Nat → Nat → Nat) :
    (decClock s).locals = s.locals ∧
    (decClock s).localsSize = s.localsSize ∧
    (decClock s).fpRegs = s.fpRegs ∧
    (decClock s).store = s.store ∧
    (decClock s).stack = s.stack ∧
    (decClock s).stackLimit = s.stackLimit ∧
    (decClock s).stackMax = s.stackMax ∧
    (decClock s).stackSize = s.stackSize ∧
    (decClock s).memory = s.memory ∧
    (decClock s).mdomain = s.mdomain ∧
    (decClock s).shMdomain = s.shMdomain ∧
    (decClock s).permute = s.permute ∧
    (decClock s).compile = s.compile ∧
    (decClock s).compileOracle = s.compileOracle ∧
    (decClock s).codeBuffer = s.codeBuffer ∧
    (decClock s).dataBuffer = s.dataBuffer ∧
    (decClock s).gcFun = s.gcFun ∧
    (decClock s).handler = s.handler ∧
    (decClock s).termdep = s.termdep ∧
    (decClock s).code = s.code ∧
    (decClock s).be = s.be ∧
    (decClock s).ffi = s.ffi ∧
    (decClock { s with locals := locs }).clock = (decClock s).clock ∧
    (decClock { s with permute := p }).clock = (decClock s).clock :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

/-- Exact HOL `assign_const_full` (`wordPropsScript.sml:850-867`). -/
theorem assignConstFull {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : WordLangExpHOL (BitVec width)) (z a : WordSemStateFiniteExact width C F)
    (h : assign x y z = some a) :
    a.code = z.code ∧
    a.codeBuffer = z.codeBuffer ∧
    a.dataBuffer = z.dataBuffer ∧
    a.compile = z.compile ∧
    a.compileOracle = z.compileOracle ∧
    a.clock = z.clock ∧
    a.ffi = z.ffi ∧
    a.handler = z.handler ∧
    a.stack = z.stack ∧
    a.localsSize = z.localsSize ∧
    a.stackLimit = z.stackLimit ∧
    a.stackMax = z.stackMax ∧
    a.stackSize = z.stackSize := by
  unfold assign at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL `assign_const` (`wordPropsScript.sml:869-875`). -/
theorem assignConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (x : Nat) (y : WordLangExpHOL (BitVec width)) (z a : WordSemStateFiniteExact width C F)
    (h : assign x y z = some a) :
    a.clock = z.clock ∧
    a.ffi = z.ffi :=
  have h' := assignConstFull x y z a h
  ⟨h'.2.2.2.2.2.1, h'.2.2.2.2.2.2.1⟩

/-- Exact HOL `sh_mem_set_var_const` (`wordPropsScript.sml:1011-1043`): all
    22 original conjuncts in source order. -/
theorem shMemSetVarConst {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type}
    (r : Option (HolFfiResult F)) (v : Nat) (s s' : WordSemStateFiniteExact width C F)
    (x : Option (WordSemResult rw)) (outcome : HolFinalEvent) (f : HolFfiState F)
    (l : List (BitVec 8)) (h : shMemSetVar (rw := rw) r v s = (x, s')) :
    s'.clock = s.clock ∧
    s'.compileOracle = s.compileOracle ∧
    s'.compile = s.compile ∧
    s'.be = s.be ∧
    s'.gcFun = s.gcFun ∧
    s'.mdomain = s.mdomain ∧
    s'.shMdomain = s.shMdomain ∧
    s'.code = s.code ∧
    s'.codeBuffer = s.codeBuffer ∧
    s'.dataBuffer = s.dataBuffer ∧
    s'.permute = s.permute ∧
    s'.handler = s.handler ∧
    s'.stackLimit = s.stackLimit ∧
    s'.stackMax = s.stackMax ∧
    (r = none → s'.ffi = s.ffi) ∧
    (r = some (.final outcome) → s'.ffi = s.ffi) ∧
    (r = none → s'.localsSize = s.localsSize) ∧
    (r = some (.ret f l) → s'.localsSize = s.localsSize) ∧
    (r = none → s'.stackMax = s.stackMax) ∧
    (r = some (.ret f l) → s'.stackMax = s.stackMax) ∧
    (r = none → s'.stackSize = s.stackSize) ∧
    (r = some (.ret f l) → s'.stackSize = s.stackSize) := by
  rcases r with _ | ⟨_, _⟩ | ⟨_⟩ <;> simp only [shMemSetVar] at h <;>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | rfl | (intro _; rfl) | (intro hr; cases hr)

/-- Exact HOL `sh_mem_store_const` (`wordPropsScript.sml:1045-1072`): all 20 original
    conjuncts in source order. -/
theorem shMemStoreConst {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type}
    (ad v : BitVec width) (s s' : WordSemStateFiniteExact width C F) (res : Option (WordSemResult rw))
    (h : shMemStore (rw := rw) ad v s = (res, s')) :
    s'.clock = s.clock ∧
    s'.compileOracle = s.compileOracle ∧
    s'.compile = s.compile ∧
    s'.be = s.be ∧
    s'.gcFun = s.gcFun ∧
    s'.mdomain = s.mdomain ∧
    s'.shMdomain = s.shMdomain ∧
    s'.code = s.code ∧
    s'.codeBuffer = s.codeBuffer ∧
    s'.dataBuffer = s.dataBuffer ∧
    s'.permute = s.permute ∧
    s'.handler = s.handler ∧
    s'.stackLimit = s.stackLimit ∧
    s'.stackMax = s.stackMax ∧
    (res = some .error → s'.localsSize = s.localsSize) ∧
    (res = none → s'.localsSize = s.localsSize) ∧
    (res = none → s'.stackMax = s.stackMax) ∧
    (res = some .error → s'.stackMax = s.stackMax) ∧
    (res = none → s'.stackSize = s.stackSize) ∧
    (res = some .error → s'.stackSize = s.stackSize) := by
  unfold shMemStore at h
  split at h
  · split at h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | rfl | (intro _; rfl) | (intro hr; cases hr)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | rfl | (intro _; rfl) | (intro hr; cases hr)

/-- Exact HOL `sh_mem_store_byte_const` (`wordPropsScript.sml:1074-1101`): all 20 original
    conjuncts in source order. -/
theorem shMemStoreByteConst {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type}
    (ad v : BitVec width) (s s' : WordSemStateFiniteExact width C F) (res : Option (WordSemResult rw))
    (h : shMemStoreByte (rw := rw) ad v s = (res, s')) :
    s'.clock = s.clock ∧
    s'.compileOracle = s.compileOracle ∧
    s'.compile = s.compile ∧
    s'.be = s.be ∧
    s'.gcFun = s.gcFun ∧
    s'.mdomain = s.mdomain ∧
    s'.shMdomain = s.shMdomain ∧
    s'.code = s.code ∧
    s'.codeBuffer = s.codeBuffer ∧
    s'.dataBuffer = s.dataBuffer ∧
    s'.permute = s.permute ∧
    s'.handler = s.handler ∧
    s'.stackLimit = s.stackLimit ∧
    s'.stackMax = s.stackMax ∧
    (res = some .error → s'.localsSize = s.localsSize) ∧
    (res = none → s'.localsSize = s.localsSize) ∧
    (res = none → s'.stackMax = s.stackMax) ∧
    (res = some .error → s'.stackMax = s.stackMax) ∧
    (res = none → s'.stackSize = s.stackSize) ∧
    (res = some .error → s'.stackSize = s.stackSize) := by
  unfold shMemStoreByte at h
  split at h
  · split at h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | rfl | (intro _; rfl) | (intro hr; cases hr)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | rfl | (intro _; rfl) | (intro hr; cases hr)

/-- Exact HOL `sh_mem_store16_const` (`wordPropsScript.sml:1103-1130`): all 20 original
    conjuncts in source order. -/
theorem shMemStore16Const {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type}
    (ad v : BitVec width) (s s' : WordSemStateFiniteExact width C F) (res : Option (WordSemResult rw))
    (h : shMemStore16 (rw := rw) ad v s = (res, s')) :
    s'.clock = s.clock ∧
    s'.compileOracle = s.compileOracle ∧
    s'.compile = s.compile ∧
    s'.be = s.be ∧
    s'.gcFun = s.gcFun ∧
    s'.mdomain = s.mdomain ∧
    s'.shMdomain = s.shMdomain ∧
    s'.code = s.code ∧
    s'.codeBuffer = s.codeBuffer ∧
    s'.dataBuffer = s.dataBuffer ∧
    s'.permute = s.permute ∧
    s'.handler = s.handler ∧
    s'.stackLimit = s.stackLimit ∧
    s'.stackMax = s.stackMax ∧
    (res = some .error → s'.localsSize = s.localsSize) ∧
    (res = none → s'.localsSize = s.localsSize) ∧
    (res = none → s'.stackMax = s.stackMax) ∧
    (res = some .error → s'.stackMax = s.stackMax) ∧
    (res = none → s'.stackSize = s.stackSize) ∧
    (res = some .error → s'.stackSize = s.stackSize) := by
  unfold shMemStore16 at h
  split at h
  · split at h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | rfl | (intro _; rfl) | (intro hr; cases hr)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | rfl | (intro _; rfl) | (intro hr; cases hr)

/-- Exact HOL `sh_mem_store32_const` (`wordPropsScript.sml:1132-1159`): all 20 original
    conjuncts in source order. -/
theorem shMemStore32Const {width : Nat} [NeZero width] {rw : Nat} [NeZero rw] {C : Type} {F : Type}
    (ad v : BitVec width) (s s' : WordSemStateFiniteExact width C F) (res : Option (WordSemResult rw))
    (h : shMemStore32 (rw := rw) ad v s = (res, s')) :
    s'.clock = s.clock ∧
    s'.compileOracle = s.compileOracle ∧
    s'.compile = s.compile ∧
    s'.be = s.be ∧
    s'.gcFun = s.gcFun ∧
    s'.mdomain = s.mdomain ∧
    s'.shMdomain = s.shMdomain ∧
    s'.code = s.code ∧
    s'.codeBuffer = s.codeBuffer ∧
    s'.dataBuffer = s.dataBuffer ∧
    s'.permute = s.permute ∧
    s'.handler = s.handler ∧
    s'.stackLimit = s.stackLimit ∧
    s'.stackMax = s.stackMax ∧
    (res = some .error → s'.localsSize = s.localsSize) ∧
    (res = none → s'.localsSize = s.localsSize) ∧
    (res = none → s'.stackMax = s.stackMax) ∧
    (res = some .error → s'.stackMax = s.stackMax) ∧
    (res = none → s'.stackSize = s.stackSize) ∧
    (res = some .error → s'.stackSize = s.stackSize) := by
  unfold shMemStore32 at h
  split at h
  · split at h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj h <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | rfl | (intro _; rfl) | (intro hr; cases hr)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | rfl | (intro _; rfl) | (intro hr; cases hr)

/-- Exact HOL `get_var_set_store` (`wordPropsScript.sml:1350-1354`). -/
theorem getVarSetStore {width : Nat} [NeZero width] {C : Type} {F : Type}
    (v1 : Nat) (v2 : WordStoreHOL) (x : WordLocW width) (s : WordSemStateFiniteExact width C F) :
    getVar v1 (setStore v2 x s) = getVar v1 s := rfl

/-- Exact HOL `get_var_set_fp_var` (`wordPropsScript.sml:1356-1360`). -/
theorem getVarSetFpVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (v1 v2 : Nat) (x : BitVec 64) (s : WordSemStateFiniteExact width C F) :
    getVar v1 (setFpVar v2 x s) = getVar v1 s := rfl

/-- Exact HOL `get_store_set_store` (`wordPropsScript.sml:1368-1373`). -/
theorem getStoreSetStore {width : Nat} [NeZero width] {C : Type} {F : Type}
    (v1 v2 : WordStoreHOL) (x : WordLocW width) (s : WordSemStateFiniteExact width C F) :
    getStore v1 (setStore v2 x s) = if v1 = v2 then some x else getStore v1 s := rfl

/-- Exact HOL `get_fp_var_set_fp_var` (`wordPropsScript.sml:1375-1380`). -/
theorem getFpVarSetFpVar {width : Nat} [NeZero width] {C : Type} {F : Type}
    (v1 v2 : Nat) (x : BitVec 64) (s : WordSemStateFiniteExact width C F) :
    getFpVar v1 (setFpVar v2 x s) = if v1 = v2 then some x else getFpVar v1 s := rfl

end WordSemStateFiniteExact

end Flapjack
