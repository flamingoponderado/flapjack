import Mathlib.Logic.Function.Defs
import Flapjack.Compiler.Backend.StackNames.ProgramNames
import Flapjack.Compiler.Backend.Semantics.StackSem.Evaluate
import Flapjack.FiniteMap.MapKeys

/-!
# stack_namesProof: `rename_state` and its state-operation lemmas

Ports of the `rename_state` group of `cakeml/compiler/backend/proofs/stack_namesProofScript.sml`
(lines 15-69): the renamed state and its interaction with the clock, memory and register
lookups. HOL `find_name` is `tlookup` (`findNameSpt`), `MAP_KEYS` is the choice rendering
`HolFiniteMapExact.mapKeys`, `fromAList`/`toAList` are `sptFromAList`/`sptToAList`, `##` is
`Prod.map`, `IMAGE` over the Boolean `ffi_save_regs` set is the decided existential, and HOL
`BIJ (find_name f) UNIV UNIV` is `Function.Bijective (findNameSpt f)`.
-/

namespace Flapjack.Compiler.Backend.StackNames

open Flapjack Flapjack.Compiler.Backend.StackLang StackSemStateOps

namespace StackNamesRenameWitnesses

/-- Canonical imported StackSem carrier roundtrip for the state-field ports. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

end StackNamesRenameWitnesses

/-- Exact HOL `rename_state_def` (`stack_namesProofScript.sml:15-24`). -/
noncomputable def renameState {width : Nat} [NeZero width] {C F : Type}
    (compileRest : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C))
    (f : Spt Nat) (s : StackSemStateFiniteExact width C F) : StackSemStateFiniteExact width C F :=
  open Classical in
  { s with
    regs := HolFiniteMapExact.mapKeys (findNameSpt f) s.regs
    code := sptFromAList (compileHOL f (sptToAList s.code))
    compile := compileRest
    compileOracle := Prod.map id (Prod.map (compileHOL f) id) ∘ s.compileOracle
    ffiSaveRegs := fun y => decide (∃ x, s.ffiSaveRegs x = true ∧ y = findNameSpt f x) }

/-- Exact HOL `rename_state_with_clock` (`stack_namesProofScript.sml:26-30`). -/
theorem renameState_withClock {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F} {k : Nat} :
    renameState c f { s with clock := k } = { renameState c f s with clock := k } := rfl

/-- Exact HOL `rename_state_const` (`stack_namesProofScript.sml:32-44`): the nine unchanged
fields. -/
theorem renameState_const {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F} :
    (renameState c f s).memory = s.memory ∧ (renameState c f s).be = s.be ∧
    (renameState c f s).mdomain = s.mdomain ∧ (renameState c f s).shMdomain = s.shMdomain ∧
    (renameState c f s).codeBuffer = s.codeBuffer ∧ (renameState c f s).clock = s.clock ∧
    (renameState c f s).compile = c ∧ (renameState c f s).useStack = s.useStack ∧
    (renameState c f s).fpRegs = s.fpRegs :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact HOL `rename_state_with_memory` (`stack_namesProofScript.sml:46-50`). -/
theorem renameState_withMemory {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F} {k : BitVec width → WordLocW width} :
    renameState c f { s with memory := k } = { renameState c f s with memory := k } := rfl

/-- Exact HOL `dec_clock_rename_state` (`stack_namesProofScript.sml:52-56`). -/
theorem decClock_renameState {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {x : Spt Nat}
    {y : StackSemStateFiniteExact width C F} :
    decClock (renameState c x y) = renameState c x (decClock y) := rfl

/-- Exact HOL `mem_load_rename_state` (`stack_namesProofScript.sml:58-62`). -/
theorem memLoad_renameState {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F} {x : BitVec width} :
    memLoad x (renameState c f s) = memLoad x s := rfl

/-- Exact HOL `mem_store_rename_state` (`stack_namesProofScript.sml:64-68`). -/
theorem memStore_renameState {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F} {x : BitVec width} {y : WordLocW width} :
    memStore x y (renameState c f s) = (memStore x y s).map (renameState c f) := by
  by_cases h : s.mdomain x = true
  · simp only [memStore, show (renameState c f s).mdomain x = true from h, h, if_true,
      Option.map_some]
    rfl
  · have h'' : s.mdomain x = false := by simpa using h
    have h' : (renameState c f s).mdomain x = false := h''
    simp [memStore, h', h'']

/-- Exact HOL `get_var_find_name` (`stack_namesProofScript.sml:70-79`). -/
theorem getVar_findName {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F} {v : Nat} :
    Function.Bijective (findNameSpt f) →
      getVar (findNameSpt f v) (renameState c f s) = getVar v s :=
  fun h => HolFiniteMapExact.lookup_mapKeys_of_injective h.1 s.regs v

/-- Exact HOL `get_var_imm_find_name` (`stack_namesProofScript.sml:81-92`). The `reg_imm`
operand is the stack_names `HolRegImm` carrier, read by StackSem through the same
`HolRegImm.toWordRegImm` codec as its `If` clause. -/
theorem getVarImm_findName {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F} {ri : Flapjack.Compiler.Encoders.Asm.HolRegImm width} :
    Function.Bijective (findNameSpt f) →
      StackSemStateOps.getVarImm (riFindNameHOL f ri).toWordRegImm (renameState c f s) =
        StackSemStateOps.getVarImm ri.toWordRegImm s := by
  intro h
  cases ri with
  | reg n => exact getVar_findName h
  | imm w => rfl

/-- Exact HOL `FLOOKUP_rename_state_find_name` (`stack_namesProofScript.sml:94-101`). -/
theorem lookup_renameState_findName {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F} {k : Nat} :
    Function.Bijective (findNameSpt f) →
      (renameState c f s).regs.lookup (findNameSpt f k) = s.regs.lookup k :=
  fun h => HolFiniteMapExact.lookup_mapKeys_of_injective h.1 s.regs k

section ShMem
open StackSemShMem


@[simp] private theorem renameState_shMdomain {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).shMdomain = s.shMdomain := rfl
@[simp] private theorem renameState_ffi {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).ffi = s.ffi := rfl

/-- Renaming commutes with a register update and an FFI-state replacement (Flapjack
infrastructure, from `MAP_KEYS_FUPDATE`). -/
theorem renameState_updateRegsFfi {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (hf : Function.Injective (findNameSpt f))
    (s : StackSemStateFiniteExact width C F) (x : Nat) (v : WordLocW width) (ffi' : HolFfiState F) :
    renameState c f { s with regs := s.regs.updateEq (x, v), ffi := ffi' } =
      { renameState c f s with
          regs := (renameState c f s).regs.updateEq (findNameSpt f x, v), ffi := ffi' } := by
  simp only [renameState, HolFiniteMapExact.mapKeys_updateEq hf]

theorem renameState_updateFfi {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (s : StackSemStateFiniteExact width C F) (ffi' : HolFfiState F) :
    renameState c f { s with ffi := ffi' } = { renameState c f s with ffi := ffi' } := rfl

local macro "shload_tac" : tactic =>
  `(tactic| (
    intro hf
    split
    · rename_i hd
      have hd' := hd
      simp only [renameState_shMdomain] at hd'
      simp only [hd', ↓reduceIte]
      split
      · rename_i heq
        have heq' := heq
        simp only [renameState_ffi] at heq'
        simp only [heq']
      · rename_i heq
        have heq' := heq
        simp only [renameState_ffi] at heq'
        simp only [heq']
        rw [renameState_updateRegsFfi hf.1]
        try rfl
    · rename_i hd
      have hd' := hd
      simp only [renameState_shMdomain] at hd'
      simp only [hd', Bool.false_eq_true, ↓reduceIte]))

local macro "shstore_tac" : tactic =>
  `(tactic| (
    intro hf
    simp only [getVar_findName hf]
    split
    · rename_i heq
      try simp only [heq]
      split
      · rename_i hd
        have hd' := hd
        try simp only [renameState_shMdomain] at hd'
        simp only [hd', ↓reduceIte]
        split
        · rename_i heq2
          have heq2' := heq2
          try simp only [renameState_ffi] at heq2'
          try simp only [heq2']
        · rename_i heq2
          have heq2' := heq2
          try simp only [renameState_ffi] at heq2'
          try simp only [heq2']
          rfl
      · rename_i hd
        have hd' := hd
        try simp only [renameState_shMdomain] at hd'
        simp only [hd', Bool.false_eq_true, ↓reduceIte]
    · rename_i hne
      first
      | rfl
      | (split
         · rename_i heq; exact absurd heq (hne _)
         · rfl)))

/-- Exact HOL `sh_mem_load_rename_state` (`stack_namesProofScript.sml:103-112`). -/
theorem shMemLoad_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {x : Nat} {y : BitVec width} :
    Function.Bijective (findNameSpt f) →
      shMemLoad (findNameSpt f x) y (renameState c f s) =
        ((shMemLoad x y s).1, renameState c f (shMemLoad x y s).2) := by
  unfold shMemLoad; shload_tac

/-- Exact HOL `sh_mem_store_rename_state` (`stack_namesProofScript.sml:114-122`). -/
theorem shMemStore_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {x : Nat} {y : BitVec width} :
    Function.Bijective (findNameSpt f) →
      shMemStore (findNameSpt f x) y (renameState c f s) =
        ((shMemStore x y s).1, renameState c f (shMemStore x y s).2) := by
  unfold shMemStore; shstore_tac

/-- Exact HOL `sh_mem_load_byte_rename_state` (`stack_namesProofScript.sml:124-133`). -/
theorem shMemLoadByte_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {x : Nat}
    {y : BitVec width} :
    Function.Bijective (findNameSpt f) →
      shMemLoadByte (findNameSpt f x) y (renameState c f s) =
        ((shMemLoadByte x y s).1, renameState c f (shMemLoadByte x y s).2) := by
  unfold shMemLoadByte; shload_tac

/-- Exact HOL `sh_mem_store_byte_rename_state` (`stack_namesProofScript.sml:135-142`). -/
theorem shMemStoreByte_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {x : Nat}
    {y : BitVec width} :
    Function.Bijective (findNameSpt f) →
      shMemStoreByte (findNameSpt f x) y (renameState c f s) =
        ((shMemStoreByte x y s).1, renameState c f (shMemStoreByte x y s).2) := by
  unfold shMemStoreByte; shstore_tac

/-- Exact HOL `sh_mem_load16_rename_state` (`stack_namesProofScript.sml:144-153`). -/
theorem shMemLoad16_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {x : Nat}
    {y : BitVec width} :
    Function.Bijective (findNameSpt f) →
      shMemLoad16 (findNameSpt f x) y (renameState c f s) =
        ((shMemLoad16 x y s).1, renameState c f (shMemLoad16 x y s).2) := by
  unfold shMemLoad16; shload_tac

/-- Exact HOL `sh_mem_store16_rename_state` (`stack_namesProofScript.sml:155-162`). -/
theorem shMemStore16_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {x : Nat}
    {y : BitVec width} :
    Function.Bijective (findNameSpt f) →
      shMemStore16 (findNameSpt f x) y (renameState c f s) =
        ((shMemStore16 x y s).1, renameState c f (shMemStore16 x y s).2) := by
  unfold shMemStore16; shstore_tac

/-- Exact HOL `sh_mem_load32_rename_state` (`stack_namesProofScript.sml:164-173`). -/
theorem shMemLoad32_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {x : Nat}
    {y : BitVec width} :
    Function.Bijective (findNameSpt f) →
      shMemLoad32 (findNameSpt f x) y (renameState c f s) =
        ((shMemLoad32 x y s).1, renameState c f (shMemLoad32 x y s).2) := by
  unfold shMemLoad32; shload_tac

/-- Exact HOL `sh_mem_store32_rename_state` (`stack_namesProofScript.sml:175-182`). -/
theorem shMemStore32_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {x : Nat}
    {y : BitVec width} :
    Function.Bijective (findNameSpt f) →
      shMemStore32 (findNameSpt f x) y (renameState c f s) =
        ((shMemStore32 x y s).1, renameState c f (shMemStore32 x y s).2) := by
  unfold shMemStore32; shstore_tac

/-- Exact HOL `sh_mem_op_rename_store` (`stack_namesProofScript.sml:184-190`). -/
theorem shMemOp_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {op : WordMemOp} {r : Nat}
    {a : BitVec width} :
    Function.Bijective (findNameSpt f) →
      shMemOp op (findNameSpt f r) a (renameState c f s) =
        ((shMemOp op r a s).1, renameState c f (shMemOp op r a s).2) := by
  intro hf
  cases op
  · exact shMemLoad_renameState hf
  · exact shMemLoadByte_renameState hf
  · exact shMemLoad16_renameState hf
  · exact shMemLoad32_renameState hf
  · exact shMemStore_renameState hf
  · exact shMemStoreByte_renameState hf
  · exact shMemStore16_renameState hf
  · exact shMemStore32_renameState hf

end ShMem

section Code


/-- Exact HOL `prog_comp_eta` (`stack_namesProofScript.sml:192-196`, `[local]`). -/
theorem progComp_eta {width : Nat} [NeZero width] {f : Spt Nat} :
    (progCompEntryHOL f : Nat × HolProg width → Nat × HolProg width) =
      fun p => (p.1, progCompHOL f p.2) := by
  funext p; rfl

/-- `ALOOKUP` through `compile` (Flapjack infrastructure, `ALOOKUP_MAP`). -/
theorem sptAListLookup_compileHOL {width : Nat} [NeZero width] {f : Spt Nat} (k : Nat) (l : List (Nat × HolProg width)) :
    sptAListLookup k (compileHOL f l) = (sptAListLookup k l).map (progCompHOL f) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
      obtain ⟨k', q⟩ := p
      simp only [compileHOL, List.map_cons, progCompEntryHOL, sptAListLookup] at ih ⊢
      split
      · rfl
      · exact ih

/-- The renamed code looks up compiled programs (Flapjack infrastructure, from
`lookup_fromAList`, `ALOOKUP_MAP` and `ALOOKUP_toAList`). -/
theorem sptLookup_renameState_code {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (s : StackSemStateFiniteExact width C F) (k : Nat) :
    sptLookup k (renameState c f s).code = (sptLookup k s.code).map (progCompHOL f) := by
  show sptLookup k (sptFromAList (compileHOL f (sptToAList s.code))) = _
  rw [sptLookup_sptFromAList, sptAListLookup_compileHOL, ← sptLookup_sptFromAList,
    sptLookup_sptFromAList_sptToAList]

/-- Exact HOL `find_code_rename_state` (`stack_namesProofScript.sml:198-219`). -/
theorem findCode_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {dest : Sum Nat Nat} :
    Function.Bijective (findNameSpt f) →
      StackSemControl.findCode (destFindNameHOL f dest) (renameState c f s).regs (renameState c f s).code =
        (StackSemControl.findCode dest s.regs s.code).map (progCompHOL f) := by
  intro hf
  cases dest with
  | inl l => exact sptLookup_renameState_code s l
  | inr r =>
      simp only [StackSemControl.findCode, destFindNameHOL]
      rw [lookup_renameState_findName hf]
      cases hlk : s.regs.lookup r with
      | none => rfl
      | some v =>
        cases v with
        | word w => rfl
        | loc label off =>
          cases off with
          | zero => exact sptLookup_renameState_code s label
          | succ n => rfl

/-- Exact HOL `set_var_find_name` (`stack_namesProofScript.sml:221-229`). -/
theorem setVar_findName {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {x : Nat} {y : WordLocW width} {z : StackSemStateFiniteExact width C F} :
    Function.Bijective (findNameSpt f) →
      renameState c f (setVar x y z) = setVar (findNameSpt f x) y (renameState c f z) := by
  intro hf
  simp only [setVar, renameState, HolFiniteMapExact.mapKeys_updateEq hf.1]
  rfl

/-- Exact HOL `set_fp_var_find_name` (`stack_namesProofScript.sml:231-236`). -/
theorem setFpVar_findName {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {x : Nat} {y : BitVec 64} {z : StackSemStateFiniteExact width C F} :
    renameState c f (setFpVar x y z) = setFpVar x y (renameState c f z) := rfl

/-- Exact HOL `domain_rename_state_code` (`stack_namesProofScript.sml:274-278`). -/
theorem domain_renameState_code {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} :
    sptDomain (renameState c f s).code = sptDomain s.code := by
  funext k
  simp only [sptDomain, sptLookup_renameState_code, Option.isSome_map]

/-- Exact HOL `comp_STOP_Loop` (`stack_namesProofScript.sml:280-285`, `[local]`); HOL `STOP` is
the identity (`stackSemScript.sml:663-664`), which the Lean program carrier does not render. -/
theorem comp_STOP_Loop {width : Nat} [NeZero width] {f : Spt Nat} {c1 : HolProg width} :
    progCompHOL f (.loop c1) = .loop (progCompHOL f c1) := rfl

/-- Exact HOL `get_labels_comp` (`stack_namesProofScript.sml:287-293`, `[local]`). -/
theorem getLabels_comp {width : Nat} [NeZero width] : ∀ (f : Spt Nat) (p : HolProg width),
    StackSem.getLabelsExact (progCompHOL f p) = StackSem.getLabelsExact p
  | f, .seq a b => by
      show StackSem.getLabelsExact (.seq (progCompHOL f a) (progCompHOL f b)) = _
      rw [StackSem.getLabelsExact, StackSem.getLabelsExact, getLabels_comp f a, getLabels_comp f b]
  | f, .ite op r ri a b => by
      show StackSem.getLabelsExact (.ite op (findNameSpt f r) (riFindNameHOL f ri)
        (progCompHOL f a) (progCompHOL f b)) = _
      rw [StackSem.getLabelsExact, StackSem.getLabelsExact, getLabels_comp f a, getLabels_comp f b]
  | f, .loop b => by
      show StackSem.getLabelsExact (.loop (progCompHOL f b)) = _
      rw [StackSem.getLabelsExact, StackSem.getLabelsExact, getLabels_comp f b]
  | f, .call none t none => by
      simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .call none t (some (hb, h1, h2)) => by
      simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .call (some (body, link, l1, l2)) t none => by
      show StackSem.getLabelsExact (.call (some (progCompHOL f body, findNameSpt f link, l1, l2))
        (destFindNameHOL f t) none) = _
      rw [StackSem.getLabelsExact, StackSem.getLabelsExact, getLabels_comp f body]
  | f, .call (some (body, link, l1, l2)) t (some (hb, h1, h2)) => by
      show StackSem.getLabelsExact (.call (some (progCompHOL f body, findNameSpt f link, l1, l2))
        (destFindNameHOL f t) (some (progCompHOL f hb, h1, h2))) = _
      rw [StackSem.getLabelsExact, StackSem.getLabelsExact, getLabels_comp f body]
      dsimp only
      rw [getLabels_comp f hb]
  | f, .skip => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .inst _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .get _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .set _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .opCurrHeap _ _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .jumpLower _ _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .alloc _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .storeConsts _ _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .raise _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .ret _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .break _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .continue _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .ffi _ _ _ _ _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .tick => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .locValue _ _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .install _ _ _ _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .shMemOp _ _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .codeBufferWrite _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .dataBufferWrite _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .rawCall _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .stackAlloc _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .stackFree _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .stackStore _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .stackStoreAny _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .stackLoad _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .stackLoadAny _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .stackGetSize _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .stackSetSize _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .bitmapLoad _ _ => by simp only [progCompHOL, StackSem.getLabelsExact]
  | f, .halt _ => by simp only [progCompHOL, StackSem.getLabelsExact]

/-- Exact HOL `loc_check_rename_state` (`stack_namesProofScript.sml:295-302`, `[local]`). -/
theorem locCheck_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {l1 l2 : Nat} :
    StackSem.locCheckExact (renameState c f s).code (l1, l2) =
      StackSem.locCheckExact s.code (l1, l2) := by
  apply propext
  simp only [StackSem.locCheckExact, sptMem, sptDomain, sptLookup_renameState_code,
    Option.isSome_map]
  constructor
  · rintro (h | ⟨k, p, hp, hl⟩)
    · exact Or.inl h
    · cases hq : sptLookup k s.code with
      | none => rw [hq] at hp; cases hp
      | some q =>
          rw [hq] at hp; simp only [Option.map_some, Option.some.injEq] at hp; subst hp
          exact Or.inr ⟨k, q, hq, by rw [getLabels_comp] at hl; exact hl⟩
  · rintro (h | ⟨k, p, hp, hl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨k, progCompHOL f p, by rw [hp]; rfl, by rw [getLabels_comp]; exact hl⟩

end Code

section InstHelpers
open StackSemExpressions


theorem wordExp_var_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (hf : Function.Bijective (findNameSpt f))
    (s : StackSemStateFiniteExact width C F) (v : Nat) :
    wordExp (renameState c f s) (.var (findNameSpt f v)) = wordExp s (.var v) := by
  simp only [wordExp]
  rw [lookup_renameState_findName hf]

theorem wordExp_op_congr {width : Nat} [NeZero width] {C F : Type} {t t' : StackSemStateFiniteExact width C F} {o : BinOp}
    {args args' : List (WordLangExpHOL (BitVec width))}
    (h : args'.map (wordExp t') = args.map (wordExp t)) :
    wordExp t' (.op o args') = wordExp t (.op o args) := by
  simp only [wordExp]
  have e : ∀ (u : StackSemStateFiniteExact width C F) (l : List (WordLangExpHOL (BitVec width))),
      (l.attach.map fun ⟨e, _⟩ => wordExp u e) = l.map (wordExp u) := by
    intro u l; simp
  rw [e, e, h]

theorem wordExp_shift_congr {width : Nat} [NeZero width] {C F : Type} {t t' : StackSemStateFiniteExact width C F} {sh : Shift}
    {a a' b b' : WordLangExpHOL (BitVec width)}
    (ha : wordExp t' a' = wordExp t a) (hb : wordExp t' b' = wordExp t b) :
    wordExp t' (.shift sh a' b') = wordExp t (.shift sh a b) := by
  simp only [wordExp, ha, hb]

theorem wordExp_ri_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (hf : Function.Bijective (findNameSpt f))
    (s : StackSemStateFiniteExact width C F) (ri : Flapjack.Compiler.Encoders.Asm.HolRegImm width) :
    wordExp (renameState c f s)
        (match riFindNameHOL f ri with | .reg r3 => .var r3 | .imm w => .const w) =
      wordExp s (match ri with | .reg r3 => .var r3 | .imm w => .const w) := by
  cases ri with
  | reg r => exact wordExp_var_renameState hf s r
  | imm w => simp only [riFindNameHOL, wordExp]

theorem wordExp_addr_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (hf : Function.Bijective (findNameSpt f))
    (s : StackSemStateFiniteExact width C F) (a : Nat) (w : BitVec width) :
    wordExp (renameState c f s) (.op .add [.var (findNameSpt f a), .const w]) =
      wordExp s (.op .add [.var a, .const w]) := by
  apply wordExp_op_congr
  simp only [List.map_cons, List.map_nil, wordExp_var_renameState hf, wordExp]

theorem getVars_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (hf : Function.Bijective (findNameSpt f))
    (s : StackSemStateFiniteExact width C F) :
    ∀ l : List Nat, StackSemStateOps.getVars (l.map (findNameSpt f)) (renameState c f s) =
      StackSemStateOps.getVars l s
  | [] => rfl
  | v :: l => by
      simp only [List.map_cons, StackSemStateOps.getVars, getVar_findName hf, getVars_renameState hf s l]

theorem renameState_withMemory' {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (s : StackSemStateFiniteExact width C F)
    (m : BitVec width → WordLocW width) :
    renameState c f { s with memory := m } = { renameState c f s with memory := m } := rfl

end InstHelpers

section InstRename
open StackSemExpressions StackSemInst StackSemIntegerInstructions
open Flapjack.Compiler.Encoders.Asm


theorem assign_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (hf : Function.Bijective (findNameSpt f))
    (s : StackSemStateFiniteExact width C F) (r : Nat) {e e' : WordLangExpHOL (BitVec width)}
    (h : wordExp (renameState c f s) e' = wordExp s e) :
    assign (findNameSpt f r) e' (renameState c f s) = (assign r e s).map (renameState c f) := by
  unfold assign
  rw [h]
  cases wordExp s e with
  | none => rfl
  | some w => simp only [Option.map_some, setVar_findName hf]

@[simp] private theorem getFpVar_renameState {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (s : StackSemStateFiniteExact width C F) (d : Nat) :
    getFpVar d (renameState c f s) = getFpVar d s := rfl
@[simp] private theorem renameState_memory {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).memory = s.memory := rfl
@[simp] private theorem renameState_mdomain {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).mdomain = s.mdomain := rfl
@[simp] private theorem renameState_be {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} (s : StackSemStateFiniteExact width C F) :
    (renameState c f s).be = s.be := rfl

local macro "ir_tac" : tactic =>
  `(tactic| (
    repeat' (first
      | (split <;> try (simp only [Option.map_some, Option.map_none]))
      | rfl)
    all_goals try simp only [Option.map_some, Option.map_none,
      setVar_findName ‹Function.Bijective (findNameSpt _)›,
      setFpVar_findName, renameState_withMemory']))

/-- Exact HOL `inst_rename` (`stack_namesProofScript.sml:238-266`). -/
theorem instRename {width : Nat} [NeZero width] {C F : Type} {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat} {s : StackSemStateFiniteExact width C F} {i : HolInst width} :
    Function.Bijective (findNameSpt f) →
      instHOL (instFindNameHOL f i) (renameState c f s) = (instHOL i s).map (renameState c f) := by
  intro hf
  rcases i with _ | ⟨r, w⟩ | ⟨a⟩ | ⟨m, r, ⟨a, w⟩⟩
  · rfl
  · simp only [instHOL, instInteger, instFindNameHOL, Option.join_some]
    exact assign_renameState hf s r (by simp only [wordExp])
  · cases a with
    | binop bop r1 r2 ri =>
        cases ri with
        | imm w =>
            simp only [instHOL, instInteger, instFindNameHOL, riFindNameHOL, Option.join_some,
              Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact assign_renameState hf s r1 (wordExp_op_congr (by
              simp only [List.map_cons, List.map_nil, wordExp_var_renameState hf, wordExp]))
        | reg r3 =>
            simp only [instHOL, instInteger, instFindNameHOL, riFindNameHOL, Option.join_some]
            have hb : (findNameSpt f r3 == findNameSpt f r2) = (r3 == r2) := by
              apply Bool.eq_iff_iff.mpr
              rw [Nat.beq_eq_true_eq, Nat.beq_eq_true_eq]
              exact hf.1.eq_iff
            rw [hb]
            split
            · rw [lookup_renameState_findName hf]
              cases s.regs.lookup r2 with
              | none => rfl
              | some v => simp only [Option.map_some, setVar_findName hf]
            · exact assign_renameState hf s r1 (wordExp_op_congr (by
                simp only [List.map_cons, List.map_nil, wordExp_var_renameState hf]))
    | shift sh r1 r2 ri =>
        simp only [instHOL, instInteger, instFindNameHOL, Option.join_some]
        exact assign_renameState hf s r1
          (wordExp_shift_congr (wordExp_var_renameState hf s r2) (wordExp_ri_renameState hf s ri))
    | div r1 r2 r3 =>
        simp only [instHOL, instInteger, instFindNameHOL, Option.join_some]
        rw [show [findNameSpt f r3, findNameSpt f r2] = [r3, r2].map (findNameSpt f) from rfl,
          getVars_renameState hf]
        ir_tac
    | addCarry r1 r2 r3 r4 =>
        simp only [instHOL, instInteger, instFindNameHOL, Option.join_some]
        rw [show [findNameSpt f r2, findNameSpt f r3, findNameSpt f r4] =
          [r2, r3, r4].map (findNameSpt f) from rfl, getVars_renameState hf]
        ir_tac
    | addOverflow r1 r2 r3 r4 =>
        simp only [instHOL, instInteger, instFindNameHOL, Option.join_some]
        rw [show [findNameSpt f r2, findNameSpt f r3] = [r2, r3].map (findNameSpt f) from rfl,
          getVars_renameState hf]
        ir_tac
    | subOverflow r1 r2 r3 r4 =>
        simp only [instHOL, instInteger, instFindNameHOL, Option.join_some]
        rw [show [findNameSpt f r2, findNameSpt f r3] = [r2, r3].map (findNameSpt f) from rfl,
          getVars_renameState hf]
        ir_tac
    | longMul r1 r2 r3 r4 =>
        simp only [instHOL, instInteger, instFindNameHOL, Option.join_some]
        rw [show [findNameSpt f r3, findNameSpt f r4] = [r3, r4].map (findNameSpt f) from rfl,
          getVars_renameState hf]
        ir_tac
    | longDiv r1 r2 r3 r4 r5 =>
        simp only [instHOL, instInteger, instFindNameHOL, Option.join_some]
        rw [show [findNameSpt f r3, findNameSpt f r4, findNameSpt f r5] =
          [r3, r4, r5].map (findNameSpt f) from rfl, getVars_renameState hf]
        ir_tac
  · cases m <;> simp only [instHOL, instInteger, instFindNameHOL, Option.join_some,
      wordExp_addr_renameState hf, getVar_findName hf, memLoad_renameState,
      renameState_memory, renameState_mdomain, renameState_be] <;> ir_tac
    all_goals try simp_all [memStore_renameState]

end InstRename

end Flapjack.Compiler.Backend.StackNames
