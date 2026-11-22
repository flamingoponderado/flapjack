module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.Induction
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FfiFinal
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Control
public import Flapjack.Compiler.Backend.Semantics.DataProps.InitialStateLaws
public import Flapjack.Compiler.Backend.Semantics.DataProps.ResourceCall

@[expose] public section

/-! Draft of the `Assign` case of `data_compile_correct`
(`data_to_wordProofScript.sml` lines 367-389) taking the statement of the
not-yet-ported `assign_thm` (`data_to_word_assignProofScript.sml`
`assign_thm_goal`, lines 1765-1778) as a hypothesis. Flapjack proof
infrastructure, not a HOL port: once `assign_thm` lands, instantiating
`AssignThmStmt` gives the tagged `Assign` case. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- The statement of HOL `assign_thm` for one pair of carrier types. -/
def AssignThmStmt (width : Nat) [NeZero width] (C F : Type) : Prop :=
  ∀ (c : Flapjack.Compiler.Backend.DataToWord.Config) (l1 l2 : Nat)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (op : ClosLang.Op) (namesOpt : Option NumSet)
    (x : Flapjack.Compiler.Backend.DataSem.State C F) (args : List Nat)
    (vals : List Flapjack.Compiler.Backend.DataSem.Value) (v : Flapjack.Compiler.Backend.DataSem.Value)
    (s2 : Flapjack.Compiler.Backend.DataSem.State C F) (n l dest : Nat),
    stateRel c l1 l2 s t none locs ∧ DataLang.opRequiresNames op ≠ namesOpt.isNone ∧
      DataSem.cutStateOpt namesOpt s = some x ∧ DataSem.getVars args s.locals = some vals ∧
      t.termdep > 1 ∧ DataSem.doApp op vals x = .val (v, s2) →
    ∃ q r,
      WordSemStateFiniteExact.evaluate (compileAssign c n l dest op args namesOpt).1 t = (q, r) ∧
      (q = some .notEnoughSpace →
        r.ffi = t.ffi ∧ optionLe r.stackMax s2.stackMax ∧
        (c.gcKind ≠ .none → s2.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace → stateRel c l1 l2 (DataSem.setVar dest v s2) r none locs ∧ q = none)

/-- `data_compile_correct`'s `Assign` case from the statement of `assign_thm`. -/
theorem dataCompileCorrect_assign_of_assignThm {width : Nat} [NeZero width] {C F : Type}
    (assignThm : AssignThmStmt width C F)
    (dest : Nat) (op : ClosLang.Op) (names : List Nat) (live : Option NumSet)
    (s : Flapjack.Compiler.Backend.DataSem.State C F) :
    dataCompileCorrectInduction (width := width) (.assign dest op names live) s := by
  intro conf n l l1 l2 res s1 t locs run notType related depth
  have compiled : compileControl (width := width) conf n l (.assign dest op names live) =
      compileAssign conf n l dest op names live := by
    have h := compileControl_option (width := width) conf n l (.assign dest op names live)
    simpa [compileControl?] using h.symm
  rw [compiled]
  have typeErr : ∀ {r : Option (Result (List DataSem.Value) DataSem.Value)},
      r = some (.err (.abort .typeError)) → res = r → False := fun h e => notType (e.trans h)
  simp only [DataSem.evaluate] at run
  by_cases req : (DataLang.opRequiresNames op == live.isNone) = true
  · rw [if_pos req] at run
    exact (typeErr rfl (congrArg Prod.fst run).symm).elim
  rw [if_neg req] at run
  have validNames : DataLang.opRequiresNames op ≠ live.isNone := by simpa using req
  cases read : DataSem.getVars names s.locals with
  | none =>
    rw [read] at run
    exact (typeErr rfl (congrArg Prod.fst run).symm).elim
  | some vals =>
  rw [read] at run
  cases cut : DataSem.cutStateOpt live s with
  | none =>
    simp only [cut] at run
    exact (typeErr rfl (congrArg Prod.fst run).symm).elim
  | some x =>
  simp only [cut] at run
  have cutMax : x.stackMax = s.stackMax := by
    cases live with
    | none => simp [DataSem.cutStateOpt] at cut; rw [cut]
    | some live =>
      simp only [DataSem.cutStateOpt, DataSem.cutState, Option.map_eq_some_iff] at cut
      obtain ⟨_, _, rfl⟩ := cut
      rfl
  have cutFfi := cutStateOpt_ffi live s x cut
  have tffi : t.ffi = s.ffi := related.1
  cases app : DataSem.doApp op vals x with
  | err e =>
    rw [app] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    rcases DataSem.doApp_Rerr op vals x e app with rfl | ⟨name, f, rfl, rfl⟩
    · exact (typeErr rfl rfl).elim
    obtain ⟨q, r, eval, le, notNes, rffi, rfl⟩ :=
      Assign.assignFfi_final conf n l l1 l2 dest s x t locs name names live vals f related
        validNames cut read depth app
    refine ⟨r, _, eval, ?_, fun h => (notNes h).elim, fun _ => ⟨rfl, ?_⟩⟩
    · show optionLe r.stackMax (DataSem.flushState true (DataSem.installSfs _ x)).stackMax
      simpa [DataSem.flushState, DataSem.installSfs, cutMax] using le
    · show r.ffi = (DataSem.flushState true (DataSem.installSfs _ x)).ffi
      simp [DataSem.flushState, DataSem.installSfs, cutFfi, rffi, tffi]
  | val p =>
    obtain ⟨v, s2⟩ := p
    rw [app] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
    obtain ⟨q, r, eval, nes, notNes⟩ :=
      assignThm conf l1 l2 s t locs op live x names vals v s2 n l dest
        ⟨related, validNames, cut, read, depth, app⟩
    refine ⟨r, q, eval, ?_, fun h => ⟨?_, fun gc => ?_⟩, fun h => ?_⟩
    · by_cases h : q = some .notEnoughSpace
      · exact (nes h).2.1
      · rcases (notNes h).1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bound, _⟩
        exact bound
    · show r.ffi.ioEvents <+: s2.ffi.ioEvents
      rw [(nes h).1, tffi, ← cutFfi]
      exact DataSem.doApp_events_of_result op vals x v s2 app
    · show (DataSem.installSfs op s2).safeForSpace = false
      have hs := (nes h).2.2 gc
      cases op <;> simp [DataSem.installSfs, hs]
    · exact ⟨(notNes h).1, (notNes h).2⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs
