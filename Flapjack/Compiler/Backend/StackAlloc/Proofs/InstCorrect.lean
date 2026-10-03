import Flapjack.Compiler.Backend.StackAlloc.Proofs.ProgComp
import Flapjack.Compiler.Backend.Semantics.StackSem.Inst

/-!
# `stack_allocProof` `inst_correct`

`inst_correct` of `cakeml/compiler/backend/proofs/stack_allocProofScript.sml`
(5223-5276): a primitive instruction run from a state whose registers extend
the source registers, and whose compiler/code/GC/mode fields are those of the
`stack_alloc` output, produces the corresponding output state.
-/

namespace Flapjack.Compiler.Backend.StackAlloc

open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemExpressions Flapjack.StackSemIntegerInstructions
open Flapjack.StackSemFpInstructions Flapjack.StackSemFpRegisterInstructions
open Flapjack.StackSemInst Flapjack.Compiler.Encoders.Asm

namespace InstCorrectSupport

/-- Canonical codec for the imported owning StackSem state carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- The fields a primitive instruction reads, other than the registers, agree,
and the registers of `u` extend those of `s`. Flapjack infrastructure for the
HOL proof's `FLOOKUP_SUBMAP` steps. -/
structure InstRel {width : Nat} [NeZero width] {C F : Type}
    (s u : StackSemStateFiniteExact width C F) : Prop where
  regs : s.regs.submap u.regs
  fpRegs : u.fpRegs = s.fpRegs
  store : u.store = s.store
  memory : u.memory = s.memory
  mdomain : u.mdomain = s.mdomain
  be : u.be = s.be

theorem wordExp_rel {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) :
    ∀ (e : WordLangExpHOL (BitVec width)) (w : BitVec width),
      wordExp s e = some w → wordExp u e = some w
  | .const w', w, h => by simpa [wordExp] using h
  | .var v, w, h => by
      simp only [wordExp] at h ⊢
      split at h
      · rename_i w' hv
        rw [hr.regs _ _ hv]
        exact h
      · simp at h
  | .lookup name, w, h => by
      simp only [wordExp, hr.store] at h ⊢
      exact h
  | .load addr, w, h => by
      simp only [wordExp] at h ⊢
      split at h
      · rename_i a ha
        rw [wordExp_rel hr addr a ha]
        simpa [StackSemStateOps.memLoad, hr.memory, hr.mdomain] using h
      · simp at h
  | .op operator args, w, h => by
      simp only [wordExp] at h ⊢
      have hmap : (args.attach.map fun ⟨e, _⟩ => wordExp u e) =
          (args.attach.map fun ⟨e, _⟩ => wordExp s e) ∨
          ¬ (args.attach.map fun ⟨e, _⟩ => wordExp s e).all Option.isSome := by
        by_cases hall : (args.attach.map fun ⟨e, _⟩ => wordExp s e).all Option.isSome
        · left
          apply List.map_congr_left
          intro ⟨e, he⟩ hmem
          have hs : (wordExp s e).isSome := by
            rw [List.all_eq_true] at hall
            exact hall _ (List.mem_map.2 ⟨⟨e, he⟩, hmem, rfl⟩)
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
          have : sizeOf e < sizeOf (WordLangExpHOL.op operator args) := by
            have := List.sizeOf_lt_of_mem he
            simp only [WordLangExpHOL.op.sizeOf_spec]
            omega
          simp only [hv, wordExp_rel hr e v hv]
        · exact Or.inr hall
      rcases hmap with hmap | hmap
      · rw [hmap]; exact h
      · split at h
        · exact absurd ‹_› hmap
        · simp at h
  | .shift sh e e1, w, h => by
      simp only [wordExp] at h ⊢
      split at h
      · rename_i a b ha hb
        rw [wordExp_rel hr e a ha, wordExp_rel hr e1 b hb]
        exact h
      · simp at h
termination_by e => sizeOf e

/-- `u` with the registers `rg` and the FP registers and memory of `t`: the
shape of the target state after an instruction. -/
def liftState {width : Nat} [NeZero width] {C F : Type}
    (u t : StackSemStateFiniteExact width C F) (rg : HolFiniteMapExact Nat (WordLocW width)) :
    StackSemStateFiniteExact width C F :=
  { u with regs := rg, fpRegs := t.fpRegs, memory := t.memory }

theorem InstRel.setVar {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) (r : Nat) (v : WordLocW width) :
    InstRel (StackSemStateOps.setVar r v s) (StackSemStateOps.setVar r v u) :=
  ⟨submap_fupdate_both hr.regs, hr.fpRegs, hr.store, hr.memory, hr.mdomain, hr.be⟩

theorem InstRel.setFpVar {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) (r : Nat) (v : BitVec 64) :
    InstRel (StackSemStateOps.setFpVar r v s) (StackSemStateOps.setFpVar r v u) :=
  ⟨hr.regs, by simp [StackSemStateOps.setFpVar, hr.fpRegs], hr.store, hr.memory,
    hr.mdomain, hr.be⟩

theorem InstRel.lift {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) :
    u = liftState u s u.regs := by
  cases u; simp [liftState, ← hr.fpRegs, ← hr.memory]

theorem liftState_setVar {width : Nat} [NeZero width] {C F : Type}
    (u t : StackSemStateFiniteExact width C F) (rg : HolFiniteMapExact Nat (WordLocW width))
    (r : Nat) (v : WordLocW width) :
    StackSemStateOps.setVar r v (liftState u t rg) =
      liftState u (StackSemStateOps.setVar r v t) (rg.updateEq (r, v)) := rfl

theorem liftState_setFpVar {width : Nat} [NeZero width] {C F : Type}
    (u t : StackSemStateFiniteExact width C F) (rg : HolFiniteMapExact Nat (WordLocW width))
    (r : Nat) (v : BitVec 64) :
    StackSemStateOps.setFpVar r v (liftState u t rg) =
      liftState u (StackSemStateOps.setFpVar r v t) rg := rfl

theorem getVar_rel {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) {r : Nat} {v : WordLocW width}
    (h : StackSemStateOps.getVar r s = some v) : StackSemStateOps.getVar r u = some v :=
  hr.regs _ _ h

theorem getVars_rel {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) :
    ∀ {rs : List Nat} {vs : List (WordLocW width)},
      StackSemStateOps.getVars rs s = some vs → StackSemStateOps.getVars rs u = some vs
  | [], vs, h => h
  | r :: rs, vs, h => by
      simp only [StackSemStateOps.getVars] at h ⊢
      split at h
      · simp at h
      · rename_i v hv
        rw [getVar_rel hr hv]
        split at h
        · simp at h
        · rename_i vs' hvs
          rw [getVars_rel hr hvs]
          exact h

theorem getFpVar_rel {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) (r : Nat) :
    StackSemStateOps.getFpVar r u = StackSemStateOps.getFpVar r s := by
  simp [StackSemStateOps.getFpVar, hr.fpRegs]

theorem memLoad_rel {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) (a : BitVec width) :
    StackSemStateOps.memLoad a u = StackSemStateOps.memLoad a s := by
  simp [StackSemStateOps.memLoad, hr.memory, hr.mdomain]


theorem InstRel.withRegs {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u)
    (rg : HolFiniteMapExact Nat (WordLocW width)) :
    { u with regs := rg } = liftState u s rg := by
  cases u; simp [liftState, ← hr.fpRegs, ← hr.memory]

theorem InstRel.withMemory {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u)
    (m : BitVec width → WordLocW width) :
    { u with memory := m } = liftState u { s with memory := m } u.regs := by
  cases u; simp [liftState, ← hr.fpRegs]

theorem InstRel.setVar1 {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) (a : Nat) (x : WordLocW width) :
    StackSemStateOps.setVar a x u =
      liftState u (StackSemStateOps.setVar a x s) (u.regs.updateEq (a, x)) := by
  cases u; simp [StackSemStateOps.setVar, liftState, ← hr.fpRegs, ← hr.memory]

theorem InstRel.setVar2 {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) (a b : Nat)
    (x y : WordLocW width) :
    StackSemStateOps.setVar a x (StackSemStateOps.setVar b y u) =
      liftState u (StackSemStateOps.setVar a x (StackSemStateOps.setVar b y s))
        ((u.regs.updateEq (b, y)).updateEq (a, x)) := by
  cases u; simp [StackSemStateOps.setVar, liftState, ← hr.fpRegs, ← hr.memory]

theorem memStore_rel {width : Nat} [NeZero width] {C F : Type}
    {s u s1 : StackSemStateFiniteExact width C F} (hr : InstRel s u) {a : BitVec width}
    {v : WordLocW width} (h : StackSemStateOps.memStore a v s = some s1) :
    StackSemStateOps.memStore a v u = some (liftState u s1 u.regs) ∧ s1.regs = s.regs := by
  simp only [StackSemStateOps.memStore] at h ⊢
  split at h
  · rename_i hd
    simp only [Option.some.injEq] at h
    subst h
    rw [if_pos (by rw [hr.mdomain]; exact hd), ← hr.memory, hr.withMemory]
    exact ⟨by simp [hr.memory], rfl⟩
  · simp at h

theorem instInteger_rel {width : Nat} [NeZero width] {C F : Type}
    {s u t : StackSemStateFiniteExact width C F} (hr : InstRel s u) {i : HolInst width}
    (h : instInteger i s = some (some t)) :
    ∃ rg1, instInteger i u = some (some (liftState u t rg1)) ∧ t.regs.submap rg1 := by
  cases i with
  | skip =>
      simp only [instInteger, Option.some.injEq] at h ⊢
      subst h
      exact ⟨u.regs, by rw [← hr.withRegs], hr.regs⟩
  | const reg w =>
      simp only [instInteger, assign, wordExp, Option.some.injEq] at h ⊢
      subst h
      exact ⟨_, by rw [StackSemStateOps.setVar, hr.withRegs]; rfl, submap_fupdate_both hr.regs⟩
  | arith a =>
      cases a with
      | binop bop r1 r2 ri =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split_ifs at h ⊢ with hg
          · split at h
            · simp at h
            · rename_i v hv
              rw [hr.regs _ _ hv]
              simp only [Option.some.injEq] at h ⊢
              subst h
              exact ⟨_, hr.setVar1 _ _, submap_fupdate_both hr.regs⟩
          · simp only [assign] at h ⊢
            split at h
            · simp at h
            · rename_i v hv
              rw [wordExp_rel hr _ _ hv]
              simp only [Option.some.injEq] at h ⊢
              subst h
              exact ⟨_, hr.setVar1 _ _, submap_fupdate_both hr.regs⟩
      | shift sh r1 r2 ri =>
          simp only [instInteger, assign, Option.some.injEq] at h ⊢
          split at h
          · simp at h
          · rename_i v hv
            rw [wordExp_rel hr _ _ hv]
            simp only [Option.some.injEq] at h ⊢
            subst h
            exact ⟨_, hr.setVar1 _ _, submap_fupdate_both hr.regs⟩
      | div r1 r2 r3 =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i q w2 hv
            rw [getVars_rel hr hv]
            split at h
            · rename_i hq
              simp only [if_pos hq, Option.some.injEq] at h ⊢
              subst h
              exact ⟨_, hr.setVar1 _ _, submap_fupdate_both hr.regs⟩
            · simp at h
          · simp at h
      | longMul r1 r2 r3 r4 =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i hv
            rw [getVars_rel hr hv]
            simp only [Option.some.injEq] at h ⊢
            subst h
            exact ⟨_, hr.setVar2 _ _ _ _, submap_fupdate_both (submap_fupdate_both hr.regs)⟩
          · simp at h
      | longDiv r1 r2 r3 r4 r5 =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i hv
            rw [getVars_rel hr hv]
            split at h
            · rename_i hq
              simp only [if_pos hq, Option.some.injEq] at h ⊢
              subst h
              exact ⟨_, hr.setVar2 _ _ _ _, submap_fupdate_both (submap_fupdate_both hr.regs)⟩
            · simp at h
          · simp at h
      | addCarry r1 r2 r3 r4 =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i hv
            rw [getVars_rel hr hv]
            simp only [Option.some.injEq] at h ⊢
            subst h
            exact ⟨_, hr.setVar2 _ _ _ _, submap_fupdate_both (submap_fupdate_both hr.regs)⟩
          · simp at h
      | addOverflow r1 r2 r3 r4 =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i hv
            rw [getVars_rel hr hv]
            simp only [Option.some.injEq] at h ⊢
            subst h
            exact ⟨_, hr.setVar2 _ _ _ _, submap_fupdate_both (submap_fupdate_both hr.regs)⟩
          · simp at h
      | subOverflow r1 r2 r3 r4 =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i hv
            rw [getVars_rel hr hv]
            simp only [Option.some.injEq] at h ⊢
            subst h
            exact ⟨_, hr.setVar2 _ _ _ _, submap_fupdate_both (submap_fupdate_both hr.regs)⟩
          · simp at h
  | mem op r addr =>
      obtain ⟨a, w⟩ := addr
      cases op with
      | load =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i v hv
            rw [wordExp_rel hr _ _ hv]
            dsimp only
            rw [memLoad_rel hr]
            split at h
            · simp at h
            · rename_i b hb
              simp only [Option.some.injEq] at h ⊢
              subst h
              exact ⟨_, hr.setVar1 _ _, submap_fupdate_both hr.regs⟩
          · simp at h
      | load8 =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i v hv
            rw [wordExp_rel hr _ _ hv]
            dsimp only
            split at h
            · simp at h
            · rename_i b hb
              rw [← hr.memory, ← hr.mdomain, ← hr.be] at hb
              rw [hb]
              simp only [Option.some.injEq] at h ⊢
              subst h
              exact ⟨_, hr.setVar1 _ _, submap_fupdate_both hr.regs⟩
          · simp at h
      | load32 =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i v hv
            rw [wordExp_rel hr _ _ hv]
            dsimp only
            split at h
            · simp at h
            · rename_i b hb
              rw [← hr.memory, ← hr.mdomain, ← hr.be] at hb
              rw [hb]
              simp only [Option.some.injEq] at h ⊢
              subst h
              exact ⟨_, hr.setVar1 _ _, submap_fupdate_both hr.regs⟩
          · simp at h
      | load16 => simp [instInteger] at h
      | store16 => simp [instInteger] at h
      | store =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i ad v hv hg
            rw [wordExp_rel hr _ _ hv, getVar_rel hr hg]
            dsimp only
            split at h
            · rename_i s1 hs1
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨hm, hreg⟩ := memStore_rel hr hs1
              rw [hm]
              exact ⟨u.regs, rfl, hreg ▸ hr.regs⟩
            · simp at h
          · simp at h
      | store8 =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i ad v hv hg
            rw [wordExp_rel hr _ _ hv, getVar_rel hr hg]
            dsimp only
            split at h
            · rename_i m hm
              simp only [Option.some.injEq] at h
              subst h
              rw [← hr.memory, ← hr.mdomain, ← hr.be] at hm
              rw [hm]
              dsimp only
              rw [hr.withMemory]
              exact ⟨u.regs, rfl, hr.regs⟩
            · simp at h
          · simp at h
      | store32 =>
          simp only [instInteger, Option.some.injEq] at h ⊢
          split at h
          · rename_i ad v hv hg
            rw [wordExp_rel hr _ _ hv, getVar_rel hr hg]
            dsimp only
            split at h
            · rename_i m hm
              simp only [Option.some.injEq] at h
              subst h
              rw [← hr.memory, ← hr.mdomain, ← hr.be] at hm
              rw [hm]
              dsimp only
              rw [hr.withMemory]
              exact ⟨u.regs, rfl, hr.regs⟩
            · simp at h
          · simp at h
  | fp f => simp [instInteger] at h

theorem InstRel.setFpVar1 {width : Nat} [NeZero width] {C F : Type}
    {s u : StackSemStateFiniteExact width C F} (hr : InstRel s u) (a : Nat) (x : BitVec 64) :
    StackSemStateOps.setFpVar a x u =
      liftState u (StackSemStateOps.setFpVar a x s) u.regs := by
  cases u; simp [StackSemStateOps.setFpVar, liftState, ← hr.fpRegs, ← hr.memory]

theorem instFp_rel {width : Nat} [NeZero width] {C F : Type}
    {s u t : StackSemStateFiniteExact width C F} (hr : InstRel s u) {op : HolFp}
    (h : instFp op s = some t) :
    ∃ rg1, instFp op u = some (liftState u t rg1) ∧ t.regs.submap rg1 := by
  cases op
  case fpMovFromReg d r1 r2 =>
    simp only [instFp, instFpRegister, Option.join_some] at h ⊢
    split_ifs at h ⊢
    · split at h
      · rename_i w hw
        rw [getVar_rel hr hw]
        simp only [Option.some.injEq] at h ⊢
        subst h
        exact ⟨_, hr.setFpVar1 _ _, hr.regs⟩
      · simp at h
    · split at h
      · rename_i lo hi hlo hhi
        rw [getVar_rel hr hlo, getVar_rel hr hhi]
        simp only [Option.some.injEq] at h ⊢
        subst h
        exact ⟨_, hr.setFpVar1 _ _, hr.regs⟩
      · simp at h
  all_goals
    simp only [instFp, instFpRegister, instFpSqrt, instFpToInt, instFpFromInt,
      getFpVar_rel hr, Option.join_some] at h ⊢
  all_goals try split_ifs at h ⊢
  all_goals repeat' split at h
  all_goals try simp only [Option.some.injEq, reduceCtorEq] at h
  all_goals try subst h
  all_goals try simp only [ite_true, *]
  all_goals try simp only [Option.some.injEq]
  all_goals first
    | exact ⟨_, hr.setFpVar1 _ _, hr.regs⟩
    | exact ⟨_, hr.setVar1 _ _, submap_fupdate_both hr.regs⟩
    | exact ⟨_, hr.setVar2 _ _ _ _, submap_fupdate_both (submap_fupdate_both hr.regs)⟩

theorem InstRel.refl {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : InstRel s s :=
  ⟨fun _ _ h => h, rfl, rfl, rfl, rfl, rfl⟩

theorem instHOL_rel_integer {width : Nat} [NeZero width] {C F : Type}
    {s u t : StackSemStateFiniteExact width C F} (hr : InstRel s u) {i : HolInst width}
    (hs : instHOL i s = (instInteger i s).join) (hu : instHOL i u = (instInteger i u).join)
    (hsome : (instInteger i s).isSome) (h : instHOL i s = some t) :
    ∃ rg1, instHOL i u = some (liftState u t rg1) ∧ t.regs.submap rg1 := by
  rw [hs] at h
  rw [hu]
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hsome
  rw [ho, Option.join_some] at h
  subst h
  obtain ⟨rg1, h1, h2⟩ := instInteger_rel hr ho
  exact ⟨rg1, by rw [h1]; rfl, h2⟩

theorem instHOL_rel {width : Nat} [NeZero width] {C F : Type}
    {s u t : StackSemStateFiniteExact width C F} (hr : InstRel s u) {i : HolInst width}
    (h : instHOL i s = some t) :
    ∃ rg1, instHOL i u = some (liftState u t rg1) ∧ t.regs.submap rg1 := by
  cases i with
  | fp op => exact instFp_rel hr h
  | skip => exact instHOL_rel_integer hr rfl rfl rfl h
  | const _ _ => exact instHOL_rel_integer hr rfl rfl rfl h
  | arith _ => exact instHOL_rel_integer hr rfl rfl rfl h
  | mem _ _ _ => exact instHOL_rel_integer hr rfl rfl rfl h

/-- A primitive instruction changes only the registers, FP registers and memory. -/
theorem instHOL_frame {width : Nat} [NeZero width] {C F : Type}
    {s t : StackSemStateFiniteExact width C F} {i : HolInst width}
    (h : instHOL i s = some t) : ∃ rg, t = liftState s t rg := by
  obtain ⟨rg, h1, -⟩ := instHOL_rel (InstRel.refl s) h
  exact ⟨rg, Option.some.inj (h.symm.trans h1)⟩

end InstCorrectSupport

open InstCorrectSupport

/-- Exact HOL `inst_correct` (`stack_allocProofScript.sml:5223-5276`). HOL's
free `i s t regs compile_rest anything c` are implicit; `(I ## MAP prog_comp ## I)
o oracle` is `Prod.map id (Prod.map (List.map progComp) id) ∘ oracle`,
`dimword (:'a)` is `2 ^ width` and `dimindex (:'a) DIV 8` is `width / 8`. The
proof follows HOL's case split over the instruction: every register read of the
source succeeds in the extended registers (`FLOOKUP_SUBMAP`) and every register
write preserves `SUBMAP` (`SUBMAP_FUPDATE_both`). The total instruction semantics
inherits the `reals_as_rational_cuts` limit through its FP clauses. -/
@[hol "cakeml/compiler/backend/proofs/stack_allocProofScript.sml" "inst_correct"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem inst_correct {width : Nat} [NeZero width] {C F : Type}
    {i : HolInst width} {s t : StackSemStateFiniteExact width C F}
    {regs : HolFiniteMapExact Nat (WordLocW width)}
    {compile_rest : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)}
    {anything : WordSemGcFun width} {c : DataToWord.Config} :
    instHOL i s = some t ∧
      s.stack.length * (width / 8) < 2 ^ width ∧
      s.dataBuffer.buffer.length + (s.bitmaps.length + s.dataBuffer.spaceLeft) < 2 ^ width - 1 ∧
      s.regs.submap regs →
    ∃ regs1,
      instHOL i { s with
          regs := regs
          compile := compile_rest
          compileOracle := Prod.map id (Prod.map (List.map progComp) id) ∘ s.compileOracle
          gcFun := anything, useStack := true, useStore := true, useAlloc := false
          code := sptFromAList (compile c (sptToAList s.code)) } =
        some { t with
          regs := regs1
          compile := compile_rest
          compileOracle := Prod.map id (Prod.map (List.map progComp) id) ∘ t.compileOracle
          gcFun := anything, useStack := true, useStore := true, useAlloc := false
          code := sptFromAList (compile c (sptToAList t.code)) } ∧
      t.regs.submap regs1 ∧
      t.stack.length * (width / 8) < 2 ^ width ∧
      t.dataBuffer.buffer.length + (t.bitmaps.length + t.dataBuffer.spaceLeft) < 2 ^ width - 1 := by
  rintro ⟨h, hst, hbuf, hsub⟩
  obtain ⟨rg, ht⟩ := instHOL_frame h
  obtain ⟨rg1, h1, h2⟩ := instHOL_rel (u := { s with
      regs := regs
      compile := compile_rest
      compileOracle := Prod.map id (Prod.map (List.map progComp) id) ∘ s.compileOracle
      gcFun := anything, useStack := true, useStore := true, useAlloc := false
      code := sptFromAList (compile c (sptToAList s.code)) })
    ⟨hsub, rfl, rfl, rfl, rfl, rfl⟩ h
  refine ⟨rg1, ?_, h2, ?_, ?_⟩
  · rw [h1, ht]
    rfl
  · rw [ht]; exact hst
  · rw [ht]; exact hbuf

end Flapjack.Compiler.Backend.StackAlloc
