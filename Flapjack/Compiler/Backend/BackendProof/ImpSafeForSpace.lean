module

public import Flapjack.Compiler.Backend.BackendProof.SafeForSpace
public import Flapjack.Compiler.Backend.BackendProof.WordConf
public import Flapjack.Compiler.Backend.BackendProof.WordToStackSfs
public import Flapjack.Compiler.Backend.BackendProof.PerfCalls
public import Flapjack.Compiler.Backend.BackendProof.ConfigOk
public import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
public import Flapjack.Misc.Sptree.MapiWf
public import Flapjack.Misc.Sptree.MapiLookup
public import Flapjack.Misc.Sptree.FromAList.Lookup
public import Flapjack.Misc.Sptree.ToAList
public import Flapjack.Misc.Sorting

@[expose] public section

set_option autoImplicit false

/-! backendProofScript.sml 2813-2869: `IMP_is_safe_for_space`, the space-safety
of the data program under the stack frame sizes of a successful compilation
implies `is_safe_for_space`. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.Backend Flapjack.Compiler.Backend.BackendDefs
open Flapjack.Compiler.Backend.WordToStack.Native

/-- `holALookup` of a value-mapped association list (Flapjack infrastructure
for the theorem below). -/
theorem holALookup_map_snd {α β : Type} (g : α → β) (l : List (Nat × α)) (key : Nat) :
    holALookup (l.map fun kv => (kv.1, g kv.2)) key = (holALookup l key).map g := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨k, v⟩ := hd
      by_cases h : key = k <;> simp [holALookup, h, ih]

/-- With distinct keys, `holALookup` finds exactly the listed pairs (Flapjack
infrastructure). -/
theorem holALookup_eq_some_iff_mem {α : Type} :
    ∀ (p : List (Nat × α)), (p.map Prod.fst).Nodup →
      ∀ (k : Nat) (v : α), holALookup p k = some v ↔ (k, v) ∈ p
  | [], _, k, v => by simp [holALookup]
  | (k', v') :: tl, hnd, k, v => by
      rw [List.map_cons, List.nodup_cons] at hnd
      have ih := holALookup_eq_some_iff_mem tl hnd.2 k v
      by_cases h : k = k'
      · subst h
        simp only [holALookup, if_true, Option.some.injEq, List.mem_cons, Prod.mk.injEq,
          true_and]
        constructor
        · intro e; exact .inl e.symm
        · rintro (e | hm)
          · exact e.symm
          · exact absurd (List.mem_map_of_mem (f := Prod.fst) hm) hnd.1
      · simp [holALookup, h, ih]

/-- Exact HOL `PERM_toAList_fromAList` (`backendProofScript.sml:2773-2786`).
HOL `PERM` is the reviewed `holPerm`, `ALL_DISTINCT` is `List.Nodup`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "PERM_toAList_fromAList"]
theorem permToAListFromAList {α : Type} :
    ∀ (p : List (Nat × α)), (p.map Prod.fst).Nodup → holPerm (sptToAList (sptFromAList p)) p := by
  intro p hnd
  rw [holPerm_iff]
  refine (List.perm_ext_iff_of_nodup
    (List.Nodup.of_map _ (sptAllDistinctMapFstToAList _)) (List.Nodup.of_map _ hnd)).2 ?_
  rintro ⟨k, v⟩
  rw [sptMemToAList, sptLookupFromAList, holALookup_eq_some_iff_mem p hnd]

/-- Mapping the values of `fromAList` is `fromAList` of the mapped list
(Flapjack infrastructure; HOL's proof uses `mapi_Alist` and permutations). -/
theorem sptMapi_sptFromAList {α β : Type} (g : α → β) (l : List (Nat × α)) :
    sptMapi (fun _ v => g v) (sptFromAList l) = sptFromAList (l.map fun kv => (kv.1, g kv.2)) := by
  rw [sptEqThm _ _ ⟨sptWfMapi _ _, sptWfFromAList _⟩]
  intro n
  rw [sptLookupMapi, sptLookupFromAList, sptLookupFromAList, holALookup_map_snd]

/-- Exact HOL `IMP_is_safe_for_space` (`backendProofScript.sml:2813-2869`).
HOL's free variables are explicit parameters: `ffi : 'b ffi_state` is
`HolFfiState F`. The semantics inherit SOUNDNESS item 8 through
`is_safe_for_space`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "IMP_is_safe_for_space"
  (words_as_type_indexed_bitvec)]
theorem impIsSafeForSpace {width : Nat} [NeZero width] {F : Type}
    (asmConf : AsmConfigExact width) (c : Flapjack.Compiler.Backend.Backend.Config)
    (prog : List AstHOL.Dec) (code : List (BitVec 8)) (data : List (BitVec width))
    (conf bviConf : Flapjack.Compiler.Backend.Backend.Config)
    (dataProg : List (Nat × Nat × DataLang.Prog)) (names : Spt MlString)
    (ffi : HolFfiState F) (stackHeapLimit : Nat × Nat) :
    backendConfigOk asmConf c →
    BackendDefs.compile asmConf c prog = some (code, data, conf) →
    toData c prog = (bviConf, dataProg, names) →
    c.dataConf.gcKind ≠ .none →
    DataSem.dataLangSafeForSpace ffi (sptFromAList dataProg)
      (DataSem.computeLimits c.dataConf.lenSize (is64Bits width) c.dataConf.hasFpOps
        c.dataConf.hasFpTern stackHeapLimit)
      conf.wordConf.stackFrameSize BvlToBvi.initGlobalsLocation →
    isSafeForSpace ffi asmConf c prog stackHeapLimit := by
  intro hok hcomp hdata hgc hsafe
  have hperf : c.stackConf.perfCalls = false := hok.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, hgc⟩
  rw [hdata]
  convert hsafe using 1
  rcases hs : toStack asmConf c prog with ⟨bm, wConf, stackProg, stackNames⟩
  rw [compileWordConf_eq asmConf bm c prog code data conf wConf stackProg stackNames
    ⟨hcomp, hs⟩]
  rcases hw : toWord asmConf c prog with ⟨c1, p, n1⟩
  have hperf1 : c1.stackConf.perfCalls = false := by
    rw [← toWord_perfCalls asmConf c c1 prog p n1 hw, hperf]
  simp only [toStack, hw, hperf1] at hs
  rw [← (Prod.mk.inj (Prod.mk.inj hs).2).1]
  simp only [compileNative, computeStackFrameSizesThm]
  rcases hc : compileWordToStackNative asmConf false (asmConf.regCount - (5 + asmConf.avoidRegs.length))
      p (.list [4], 1) with ⟨bodies, frames, bms⟩
  have hk : asmConf.regCount - asmConf.avoidRegs.length - 5 =
      asmConf.regCount - (5 + asmConf.avoidRegs.length) := by omega
  have aux := compileWordToStackSfsAux asmConf false _ p _ bodies frames bms ⟨hc, rfl⟩
  simp only [Bool.false_eq_true, if_false]
  rw [hk]
  refine (sptMapi_sptFromAList (fun x =>
    (compileProgNative asmConf false x.2 x.1 (asmConf.regCount - (5 + asmConf.avoidRegs.length))
      (.nil, 0)).2.1) p).trans ?_
  rw [hc]
  exact aux

end Flapjack.Compiler.Backend.BackendProof
