import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsExact
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsInitCall
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsCons
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsAlignment
import Flapjack.Pancake.Proofs.PanGlobals.FpermSemantics
import Flapjack.Pancake.Proofs.PanGlobals.SemanticsEmptyLocals
import Flapjack.Pancake.Proofs.PanGlobals.StateRelImpSemantics
import Flapjack.Pancake.Semantics.PanProps.HasMain

namespace Flapjack

open Flapjack.Pancake.PanLang

namespace PanGlobalsCompileTopSemanticsDecls

open PanGlobalsCompileDecsStructural
open PanGlobalsDeclListExact
open PanSemStateFiniteExact

/-- Same-module canonical witness for the exact state finite-map carrier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width]
    : (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
      (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-! Flapjack association-list and finite-map infrastructure for the assembly
below; these are HOL library facts (`ALOOKUP`/`FUPDATE_LIST`), not separate
CakeML declarations. -/

private theorem lookupAppend {α β : Type} [BEq α] [LawfulBEq α]
    (l₁ l₂ : List (α × β)) (k : α) :
    List.lookup k (l₁ ++ l₂) =
      match List.lookup k l₁ with
      | some v => some v
      | none => List.lookup k l₂ := by
  induction l₁ with
  | nil => rfl
  | cons e l ih =>
      obtain ⟨a, b⟩ := e
      by_cases hk : k = a
      · subst hk; simp
      · have : (k == a) = false := by simp [hk]
        simp only [List.cons_append, List.lookup_cons, this, ih]

theorem fupdateListLookup {α β : Type} [BEq α] [LawfulBEq α]
    (m : α → Option β) (l : List (α × β)) (k : α) :
    FUPDATE_LIST m l k =
      match List.lookup k l.reverse with
      | some v => some v
      | none => m k := by
  induction l generalizing m with
  | nil => rfl
  | cons e l ih =>
      obtain ⟨a, b⟩ := e
      rw [FUPDATE_LIST_cons, ih, List.reverse_cons, lookupAppend]
      cases List.lookup k l.reverse with
      | some v => rfl
      | none =>
          by_cases hk : k = a
          · subst hk; simp [FUPDATE]
          · have h1 : (k == a) = false := by simp [hk]
            have h2 : (a == k) = false := by simp [Ne.symm hk]
            simp [FUPDATE, h1, h2, List.lookup_cons]

theorem lookupOfMemNodup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (v : β) (hmem : (k, v) ∈ l) (hnd : (l.map Prod.fst).Nodup) :
    List.lookup k l = some v := by
  induction l with
  | nil => simp at hmem
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with h | h
    · cases h; simp
    · have hka : k ≠ a := by
        intro hk; subst hk; exact hnd.1 (List.mem_map.mpr ⟨(k, v), h, rfl⟩)
      have : (k == a) = false := by simp [hka]
      simp [List.lookup_cons, this, ih h hnd.2]

theorem lookupMem {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (v : β) (h : List.lookup k l = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    by_cases hk : k = a
    · subst hk; simp at h; subst h; simp
    · have : (k == a) = false := by simp [hk]
      simp only [List.lookup_cons, this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookupNoneOfNotMem {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (h : k ∉ l.map Prod.fst) : List.lookup k l = none := by
  cases hl : List.lookup k l with
  | none => rfl
  | some v => exact absurd (List.mem_map.mpr ⟨(k, v), lookupMem l k v hl, rfl⟩) h

theorem lookupReverseOfNodup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (hnd : (l.map Prod.fst).Nodup) :
    List.lookup k l.reverse = List.lookup k l := by
  have hnd' : (l.reverse.map Prod.fst).Nodup := by
    rw [List.map_reverse, List.Nodup, List.pairwise_reverse]; exact hnd.imp (fun h => Ne.symm h)
  cases h : List.lookup k l with
  | none =>
    cases h' : List.lookup k l.reverse with
    | none => rfl
    | some v =>
      have hm := lookupMem _ _ _ h'
      have := lookupOfMemNodup l k v (List.mem_reverse.mp hm) hnd
      rw [h] at this; cases this
  | some v =>
    exact lookupOfMemNodup _ k v (List.mem_reverse.mpr (lookupMem _ _ _ h)) hnd'

/-- `FUPDATE_LIST FEMPTY` over distinct keys is `ALOOKUP`. -/
theorem emptyUpdateListLookup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (hnd : (l.map Prod.fst).Nodup) :
    (HolFiniteMapExact.empty.updateList l).lookup k = List.lookup k l := by
  rw [HolFiniteMapExact.lookup_updateList, fupdateListLookup, lookupReverseOfNodup l k hnd]
  cases List.lookup k l <;> rfl

private theorem updateListCons' {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) (entry : α × β)
    (entries : List (α × β)) :
    (map.update entry).updateList entries = map.updateList (entry :: entries) := by
  apply HolFiniteMapExact.ext
  funext key
  simp only [HolFiniteMapExact.lookup_updateList, FUPDATE_LIST_cons]
  rfl

/-- Flapjack evaluator infrastructure: a successful run of exception
declarations only extends the exception map. -/
theorem evalExnsForm {width : Nat} {σ : Type} [NeZero width] :
    ∀ (program : List (DeclHOL width)) (state : PanSemStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (result : PanSemStateFiniteExact width σ),
      (∀ d ∈ program, isExnDeclHOL d = true) →
      evaluateDeclsHOLFinite state program = some result →
      result = { state with eshapes := state.eshapes.updateList (exceptionsHOL program) } := by
  intro program
  induction program with
  | nil =>
      intro state _ result _ h
      simp only [evaluateDeclsHOLFinite, Option.some.injEq] at h
      subst h; rfl
  | cons d ds ih =>
      intro state _ result hall h
      have htail : ∀ e ∈ ds, isExnDeclHOL e = true := fun e he => hall e (by simp [he])
      cases d with
      | exnDecl name shape =>
          simp only [evaluateDeclsHOLFinite] at h
          split at h
          · rw [ih _ result htail h]
            simp only [exceptionsHOL, updateListCons']
          · cases h
      | function f => simp [isExnDeclHOL] at hall
      | decl sh n e => simp [isExnDeclHOL] at hall
      | name n fs => simp [isExnDeclHOL] at hall

/-- Flapjack evaluator infrastructure: a successful run of function
declarations only extends the code map. -/
theorem evalFunsForm {width : Nat} {σ : Type} [NeZero width] :
    ∀ (program : List (DeclHOL width)) (state : PanSemStateFiniteExact width σ)
      [DecidablePred state.memaddrs] (result : PanSemStateFiniteExact width σ),
      (∀ d ∈ program, isFunctionHOL d = true) →
      evaluateDeclsHOLFinite state program = some result →
      result = { state with code := state.code.updateList (functionsHOL program) } := by
  intro program
  induction program with
  | nil =>
      intro state _ result _ h
      simp only [evaluateDeclsHOLFinite, Option.some.injEq] at h
      subst h; rfl
  | cons d ds ih =>
      intro state _ result hall h
      have htail : ∀ e ∈ ds, isFunctionHOL e = true := fun e he => hall e (by simp [he])
      cases d with
      | function f =>
          simp only [evaluateDeclsHOLFinite] at h
          split at h
          · rw [ih _ result htail h]
            simp only [functionsHOL, updateListCons']
          · cases h
      | exnDecl name shape => simp [isFunctionHOL] at hall
      | decl sh n e => simp [isFunctionHOL] at hall
      | name n fs => simp [isFunctionHOL] at hall

/-- HOL word-library `byte_aligned_add` at the two `good_dimindex` widths,
stated over the reviewed `panGlobalsByteAlignedHOL` rendering. -/
theorem alignedAdd {width : Nat} [NeZero width] (hwidth : goodDimindex width)
    (a b : BitVec width) (ha : panGlobalsByteAlignedHOL a)
    (hb : panGlobalsByteAlignedHOL b) : panGlobalsByteAlignedHOL (a + b) := by
  rcases hwidth with rfl | rfl
  · have ha' := congrArg BitVec.toNat ha
    have hb' := congrArg BitVec.toNat hb
    change BitVec.ofNat 32 ((a.toNat / 4) * 4) = a at ha
    change BitVec.ofNat 32 ((b.toNat / 4) * 4) = b at hb
    change BitVec.ofNat 32 (((a + b).toNat / 4) * 4) = a + b
    have ha2 := congrArg BitVec.toNat ha
    have hb2 := congrArg BitVec.toNat hb
    simp only [BitVec.toNat_ofNat] at ha2 hb2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
    omega
  · change BitVec.ofNat 64 ((a.toNat / 8) * 8) = a at ha
    change BitVec.ofNat 64 ((b.toNat / 8) * 8) = b at hb
    change BitVec.ofNat 64 (((a + b).toNat / 8) * 8) = a + b
    have ha2 := congrArg BitVec.toNat ha
    have hb2 := congrArg BitVec.toNat hb
    simp only [BitVec.toNat_ofNat] at ha2 hb2
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
    omega

theorem alignedZero {width : Nat} [NeZero width] :
    panGlobalsByteAlignedHOL (0 : BitVec width) := by
  unfold panGlobalsByteAlignedHOL panByteAlignHOL
  simp

/-- The first address past a block of `n` words is not in the block, given
HOL's no-wrap bound (`intLib.COOPER_TAC` step of the source proof). -/
theorem topNotInAddresses {width : Nat} [NeZero width] (hwidth : goodDimindex width)
    (a : BitVec width) (n : Nat) (hbound : (panBytesInWord width).toNat * n < 2 ^ width) :
    ¬ Flapjack.Compiler.Backend.StackRemove.addresses a n
      (a + panBytesInWord width * BitVec.ofNat width n) := by
  rw [Flapjack.Compiler.Backend.StackRemove.mem_addresses]
  rintro ⟨i, hi, heq⟩
  have h3 := congrArg BitVec.toNat heq
  have ha := a.isLt
  rcases hwidth with rfl | rfl
  · change (a + BitVec.ofNat 32 4 * BitVec.ofNat 32 n).toNat =
      (a + BitVec.ofNat 32 i * BitVec.ofNat 32 4).toNat at h3
    change (BitVec.ofNat 32 4).toNat * n < 2 ^ 32 at hbound
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at h3 hbound
    omega
  · change (a + BitVec.ofNat 64 8 * BitVec.ofNat 64 n).toNat =
      (a + BitVec.ofNat 64 i * BitVec.ofNat 64 8).toNat at h3
    change (BitVec.ofNat 64 8).toNat * n < 2 ^ 64 at hbound
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat] at h3 hbound
    omega

private theorem bvSubZero {width : Nat} (x : BitVec width) : x - 0 = x := by
  apply BitVec.eq_of_toNat_eq
  simp

theorem filterDeclFperm {width : Nat} [NeZero width] (f g : MlS) (xs : List (DeclHOL width)) :
    (fpermDecsHOL f g xs).filter isDeclHOL = xs.filter isDeclHOL := by
  induction xs with
  | nil => simp [fpermDecsHOL]
  | cons d ds ih => cases d <;> simp [fpermDecsHOL, isDeclHOL, List.filter_cons, ih]

theorem filterDeclResort {width : Nat} [NeZero width] (xs : List (DeclHOL width)) :
    (resortDeclsHOL xs).filter isDeclHOL = xs.filter isDeclHOL := by
  have hnil : ∀ (p : DeclHOL width → Bool), (∀ d, isDeclHOL d = true → p d = false) →
      (xs.filter p).filter isDeclHOL = [] := by
    intro p hp
    apply List.filter_eq_nil_iff.mpr
    intro d hd hdecl
    have := (List.mem_filter.mp hd).2
    rw [hp d hdecl] at this
    cases this
  have hdecl : (xs.filter isDeclHOL).filter isDeclHOL = xs.filter isDeclHOL :=
    List.filter_eq_self.mpr (fun d hd => (List.mem_filter.mp hd).2)
  simp only [resortDeclsHOL, List.filter_append, hdecl]
  rw [hnil isNameHOL (by intro d h; cases d <;> simp_all [isDeclHOL, isNameHOL]),
    hnil isExnDeclHOL (by intro d h; cases d <;> simp_all [isDeclHOL, isExnDeclHOL]),
    hnil isFunctionHOL (by intro d h; cases d <;> simp_all [isDeclHOL, isFunctionHOL])]
  simp

theorem exceptionsFilterExn {width : Nat} [NeZero width] (xs : List (DeclHOL width)) :
    exceptionsHOL (xs.filter isExnDeclHOL) = exceptionsHOL xs := by
  induction xs with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [exceptionsHOL, isExnDeclHOL, List.filter_cons, ih]

/-- Flapjack assembly lemma: the compiled top-level declarations contain only
functions and exception declarations, so they evaluate successfully from any
state sharing the struct context and exception map of a state from which the
source declarations evaluate. This generalises the private target-state lemma
of `CompileTopSemanticsExact`; no separate HOL declaration. -/
theorem evaluateCompileTopOfSource {width : Nat} {σ : Type} [NeZero width]
    (state result u : PanSemStateFiniteExact width σ)
    (declarations : List (DeclHOL width)) (start : MlS)
    (entry : List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)
    (heval : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
      (fun address => Classical.propDecidable (state.memaddrs address)) declarations =
        some result)
    (hstart : (functionsHOL declarations).lookup start = some entry)
    (hkinds : ∀ declaration ∈ declarations,
      isFunctionHOL declaration = true ∨ isDeclHOL declaration = true ∨
        isExnDeclHOL declaration = true)
    (hstructs : u.structs = state.structs) (heshapes : u.eshapes = state.eshapes) :
    @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ u
      (fun address => Classical.propDecidable (u.memaddrs address))
      (compileTopExactHOL declarations start) =
        some { u with
          code := u.code.updateList (functionsHOL (compileTopExactHOL declarations start))
          eshapes := u.eshapes.updateList
            (exceptionsHOL (compileTopExactHOL declarations start)) } := by
  classical
  have hcanonical : PanPropsEvalStateFiniteExact.evaluateDeclsPanPropsCanonical
      (PanPropsEvalStateFiniteExact.ofPanSemFinite state) declarations =
        some (PanPropsEvalStateFiniteExact.ofPanSemFinite result) := by
    simpa [PanPropsEvalStateFiniteExact.evaluateDeclsPanPropsCanonical] using
      congrArg (Option.map PanPropsEvalStateFiniteExact.ofPanSemFinite) heval
  have hex := PanPropsEvalStateFiniteExact.evaluateDeclsExnsWfHOLFinite
    (PanPropsEvalStateFiniteExact.ofPanSemFinite state) declarations
    (PanPropsEvalStateFiniteExact.ofPanSemFinite result) hcanonical
  have hexceptions := exceptions_compile_topHOL declarations start entry hstart
  apply PanGlobalsCompileTopSemanticsExact.evaluateDeclsOnlyFunctionsAndExnsSOMEHOLFinite
  · exact compile_top_only_functions_or_exnsHOL declarations start
  · intro declaration hmem function heq
    have hwf := PanGlobalsCompileTopShapeWf.compile_top_shape_wfHOL
      state result declarations start ⟨heval, hkinds⟩ declaration hmem function heq
    rw [hstructs]
    exact ⟨List.all_eq_true.mpr hwf.1, hwf.2⟩
  · simpa only [hexceptions] using hex.1
  · intro current hmem
    rw [hexceptions] at hmem
    rw [heshapes]
    exact List.all_eq_true.mp hex.2.1 current hmem
  · intro current hmem
    rw [hexceptions] at hmem
    rw [hstructs]
    exact List.all_eq_true.mp hex.2.2 current hmem

/-- Exact HOL `compile_top_semantics_decls` (`pan_globalsProofScript.sml:3010-3194`).

The fourteen hypotheses are HOL's conjuncts in order: distinct function
names; `t = s with <| top_addr := s.top_addr + mgs; memaddrs := s.memaddrs ∪
free_addrs; memory := tmem; locals := tlocals |>` (set union as the pointwise
disjunction of the `Prop` domains); empty source code and globals;
`byte_aligned s.top_addr`; `good_dimindex(:'a)`; the definitions of `mgs` and
`free_addrs`; `DISJOINT s.memaddrs free_addrs`; memory agreement on the source
domain; the fresh top address; HOL's `w2n bytes_in_word * SUM … < dimword(:'a)`
bound (`dimword` is `2 ^ width`); the declaration-kind restriction; and source
`semantics_decls ≠ Fail`. The conclusion is the exact equality of the complete
source and compiled declaration semantics. No target run, successful
evaluation, or post-state fact is assumed: the source run is split along HOL's
`resort_decls` order, the target run and code table are derived from
`evaluate_decls_compile_top`, and the behaviour chain is HOL's
`semantics_init_call'`, `evaluate_decls_init_globals_lemma`,
`semantics_fperm`, `semantics_empty_locals` and `state_rel_imp_semantics`.
The source proof's `addresses_thm` rewrite is replaced by the tagged
`mem_addresses` characterisation; the `byte_aligned_add` step is proved at the
two `good_dimindex` widths over the reviewed alignment rendering. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "compile_top_semantics_decls"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem compileTopSemanticsDeclsHOL {width : Nat} {σ : Type} [NeZero width]
    (s t : PanSemStateFiniteExact width σ) (code : List (DeclHOL width)) (start : MlS)
    (mgs : BitVec width) (freeAddrs : BitVec width → Prop)
    (tmem : BitVec width → HolWordLab width)
    (tlocals : HolFiniteMapExact MlS (ValueHOL width))
    (h : ((functionsHOL code).map Prod.fst).Nodup ∧
      t = { s with
        topAddr := s.topAddr + mgs
        memaddrs := fun address => s.memaddrs address ∨ freeAddrs address
        memory := tmem
        locals := tlocals } ∧
      s.code = HolFiniteMapExact.empty ∧
      s.globals = HolFiniteMapExact.empty ∧
      panGlobalsByteAlignedHOL s.topAddr ∧
      goodDimindex width ∧
      mgs = panBytesInWord width *
        BitVec.ofNat width ((decShapesHOL code).map sizeOfShapeHOL).sum ∧
      freeAddrs = Flapjack.Compiler.Backend.StackRemove.addresses s.topAddr
        ((decShapesHOL code).map sizeOfShapeHOL).sum ∧
      (∀ address, s.memaddrs address → ¬ freeAddrs address) ∧
      (∀ address, s.memaddrs address → s.memory address = tmem address) ∧
      ¬ s.memaddrs (s.topAddr + mgs) ∧
      (panBytesInWord width).toNat * ((decShapesHOL code).map sizeOfShapeHOL).sum <
        2 ^ width ∧
      (∀ d ∈ code, isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) ∧
      semanticsDecls s start code ≠ .fail) :
    semanticsDecls s start code =
      semanticsDecls t start (compileTopExactHOL code start) := by
  classical
  obtain ⟨hdistinct, ht, hcode, hglobals, halign, hgood, rfl, rfl, hdisj, hmem,
    htopNot, hbound, hkinds, hnf⟩ := h
  obtain ⟨body, rshape, hmain⟩ := PanPropsHasMain.semanticsDeclsHasMainPrime s start code hnf
  have hkindsB : code.all (fun d => isFunctionHOL d || isDeclHOL d || isExnDeclHOL d) =
      true := by
    apply List.all_eq_true.mpr
    intro d hd
    rcases hkinds d hd with h | h | h <;> simp [h]
  have hstc := decsStcnamesHOLExact_of_functions_or_decls_or_exnDecls [] code hkindsB
  have hstcT : decsStcnamesHOLExact (width := width) [] (compileTopExactHOL code start) =
      some [] := by
    apply decsStcnamesHOLExact_of_functions_or_decls_or_exnDecls
    apply List.all_eq_true.mpr
    intro d hd
    rcases compile_top_only_functions_or_exnsHOL code start d hd with h | h <;> simp [h]
  unfold semanticsDecls at hnf ⊢
  simp only [hstc, hstcT] at hnf ⊢
  have hstartLookup : (functionsHOL code).lookup start = some ([], body, rshape) := by
    rw [hcode, emptyUpdateListLookup _ _ hdistinct] at hmain; exact hmain
  cases hs1 : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := [] } (fun a => Classical.propDecidable (s.memaddrs a)) code with
  | none => simp only [hs1] at hnf; exact absurd rfl hnf
  | some s1 =>
  simp only [hs1] at hnf ⊢
  rw [evaluateCompileTopOfSource _ s1 { t with structs := [] } code start _ hs1 hstartLookup
    hkinds rfl (by rw [ht])]
  simp only
  -- Source evaluation in HOL's resorted order: exceptions, declarations, functions.
  have hpart : resortDeclsHOL code = code.filter isExnDeclHOL ++ code.filter isDeclHOL ++
      code.filter isFunctionHOL := by
    have hnames : code.filter isNameHOL = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro d hd
      rcases hkinds d hd with h | h | h <;> cases d <;>
        simp_all [isNameHOL, isFunctionHOL, isDeclHOL, isExnDeclHOL]
    simp [resortDeclsHOL, hnames]
  have hs1orig := hs1
  have hres := Flapjack.resortDeclsEvaluate { s with structs := [] } code hkindsB
  rw [← hres, hpart, Flapjack.evaluateDeclsHOLFinite_append,
    Flapjack.evaluateDeclsHOLFinite_append] at hs1
  cases hsE : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := [] } (fun a => Classical.propDecidable (s.memaddrs a))
      (code.filter isExnDeclHOL) with
  | none => simp [hsE] at hs1
  | some sE =>
  cases hsD : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      sE (fun a => Classical.propDecidable (sE.memaddrs a)) (code.filter isDeclHOL) with
  | none => simp [hsE, hsD] at hs1
  | some sD =>
  simp only [hsE, hsD, Option.bind_some] at hs1
  have hsEform := evalExnsForm _ _ sE (fun d hd => (List.mem_filter.mp hd).2) hsE
  have hs1form := evalFunsForm _ _ s1 (fun d hd => (List.mem_filter.mp hd).2) hs1
  have hsDcode : sD.code = sE.code := by
    have := evaluateDeclsHOLFinite_functions sE _ sD hsD
    rw [this, functionsHOL_filter_isDecl]
    rfl
  -- The compiler's declaration-list result and the explicit target code table.
  rcases hc : compileDecsExactHOL
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width
           ((decShapesHOL code).map sizeOfShapeHOL).sum } : PanGlobalsContextExact width)
      (fpermDecsHOL start (newMainNameHOL code) (resortDeclsHOL code)) with
    ⟨inits, funsC, exnsC, ctx⟩
  have hexplicit := PanGlobalsCompileTopSemanticsExact.evaluateDeclsCompileTopHOLFinite
    _ s1 code start [] body rshape inits funsC exnsC ctx ⟨hs1orig, hstartLookup, hkinds, hc⟩
  have hgeneric := evaluateCompileTopOfSource _ s1 { s with structs := [] } code start _ hs1orig
    hstartLookup hkinds rfl rfl
  rw [hgeneric] at hexplicit
  have htable := congrArg PanSemStateFiniteExact.code (Option.some.inj hexplicit)
  simp only at htable
  clear hexplicit hgeneric hres
  subst hsEform
  clear hsE hs1orig hpart hstc hstcT hmain
  simp only at hsD hsDcode
  obtain ⟨N, hNdef⟩ : ∃ N, N = ((decShapesHOL code).map sizeOfShapeHOL).sum := ⟨_, rfl⟩
  obtain ⟨nm, hnm⟩ : ∃ nm, nm = newMainNameHOL code := ⟨_, rfl⟩
  rw [← hNdef] at ht hdisj htopNot hbound hc
  rw [← hnm] at hc htable
  obtain ⟨T, hT⟩ : ∃ T : PanSemStateFiniteExact width σ, T = { t with
    structs := []
    code := t.code.updateList (functionsHOL (compileTopExactHOL code start))
    eshapes := t.eshapes.updateList (exceptionsHOL (compileTopExactHOL code start)) } :=
    ⟨_, rfl⟩
  rw [← hT]
  have hTcode : T.code = (HolFiniteMapExact.empty.update
      (start, [], .seq (nestedSeqHOL inits) (.call none nm []), rshape)).updateList
      ((functionsHOL (fpermDecsHOL start nm code)).map (fun entry =>
        (entry.1, entry.2.1, compileProgExactHOL ctx entry.2.2.1, entry.2.2.2))) := by
    rw [hT]; simp only; rw [ht]; simp only; rw [htable, hcode]; rfl
  -- Initial-globals simulation of the declaration initialisers.
  have hcD : compileDecsExactHOL
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width N } :
         PanGlobalsContextExact width) (code.filter isDeclHOL) = (inits, [], [], ctx) := by
    have := compile_decs_FILTER_declsHOL _ _ _ _ _ _ hc
    rwa [filterDeclFperm, filterDeclResort] at this
  have hND : ((decShapesHOL (code.filter isDeclHOL)).map sizeOfShapeHOL).sum = N := by
    rw [(dec_shapes_FILTERHOL code).2.2.1]; exact hNdef.symm
  obtain ⟨t', hrun, hrel', hclk, hffi, hloc, -⟩ := PanGlobalsInitGlobalsAssembly.initGlobalsAll _ (code.filter isDeclHOL) _ sD
    inits [] [] ctx { T with locals := HolFiniteMapExact.empty } _
    ⟨hsD, fun d hd => (List.mem_filter.mp hd).2, hcD, by
      unfold panGlobalsStateRelHOLExact
      subst hT ht
      refine ⟨?_, fun h => absurd h (by decide), rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_,
        fun a h => Or.inl h, rfl, hmem, rfl, ?_, ?_, ?_, ?_, hgood⟩
      · change s.topAddr = s.topAddr + panBytesInWord width * BitVec.ofNat width N -
          panBytesInWord width * BitVec.ofNat width N
        rw [BitVec.add_sub_cancel]
      · rw [exceptionsFilterExn, exceptions_compile_topHOL code start _ hstartLookup]
      · intro name value h
        rw [hglobals] at h
        cases h
      · intro name shape address h
        cases h
      · intro f ps p rs h
        rw [hcode] at h
        cases h
      · intro _ _ _ _ _ _ _ h
        exact absurd (by rw [hglobals]; rfl) h
      · rintro (h | h)
        · exact htopNot h
        · exact topNotInAddresses hgood _ _ hbound h
      · exact alignedAdd hgood _ _ halign
          (PanGlobalsInitGlobalsAlignment.byteAlignedBytesInWordMulHOL _ hgood), rfl, by
      intro a h
      rw [hND]
      subst hT ht
      change ¬ Flapjack.Compiler.Backend.StackRemove.addresses
        (s.topAddr + panBytesInWord width * BitVec.ofNat width N -
          panBytesInWord width * BitVec.ofNat width N - 0) N a
      rw [bvSubZero, BitVec.add_sub_cancel]
      exact hdisj a h, by
      intro a h
      rw [hND] at h
      subst hT ht
      change Flapjack.Compiler.Backend.StackRemove.addresses
        (s.topAddr + panBytesInWord width * BitVec.ofNat width N -
          panBytesInWord width * BitVec.ofNat width N - 0) N a at h
      rw [bvSubZero, BitVec.add_sub_cancel] at h
      exact Or.inr h,
      alignedZero, hcode, by
      rintro v sh addr ⟨h1, -⟩
      change (s.globals.lookup v).isSome = true at h1
      rw [hglobals] at h1
      (cases h1), by rw [hND]; exact hbound⟩
  -- Function-table facts for the renamed and compiled code.
  have hnmFresh : nm ∉ (functionsHOL code).map Prod.fst := by
    rw [hnm]; exact new_main_name_correctHOL code
  have hstartMem : start ∈ (functionsHOL code).map Prod.fst :=
    List.mem_map.mpr ⟨_, lookupMem _ _ _ hstartLookup, rfl⟩
  have hnmStart : nm ≠ start := fun h => hnmFresh (h ▸ hstartMem)
  have hfpNodup := ALL_DISTINCT_fperm_decsHOL start nm code hdistinct
  have hLkeys : ((functionsHOL (fpermDecsHOL start nm code)).map (fun entry =>
      (entry.1, entry.2.1, compileProgExactHOL ctx entry.2.2.1, entry.2.2.2))).map Prod.fst =
      (functionsHOL (fpermDecsHOL start nm code)).map Prod.fst := by
    rw [List.map_map]; rfl
  have hLNodup := hLkeys ▸ hfpNodup
  have hTlookup : ∀ f entry, (f, entry) ∈ functionsHOL (fpermDecsHOL start nm code) →
      T.code.lookup f = some (entry.1, compileProgExactHOL ctx entry.2.1, entry.2.2) := by
    intro f entry hmem
    rw [hTcode, HolFiniteMapExact.lookup_updateList, fupdateListLookup,
      lookupReverseOfNodup _ _ hLNodup,
      lookupOfMemNodup _ f (entry.1, compileProgExactHOL ctx entry.2.1, entry.2.2)
        (List.mem_map.mpr ⟨(f, entry), hmem, rfl⟩) hLNodup]
  have hstartNotRenamed : start ∉ (functionsHOL (fpermDecsHOL start nm code)).map Prod.fst := by
    rw [functionsFpermDecsHOL, List.map_map]
    intro hmem
    obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem
    simp only [Function.comp, fpermName] at heq
    by_cases h1 : start = entry.1
    · rw [if_pos h1] at heq; exact hnmStart heq
    · rw [if_neg h1] at heq
      by_cases h2 : nm = entry.1
      · exact hnmFresh (List.mem_map.mpr ⟨entry, hentry, h2.symm⟩)
      · rw [if_neg h2] at heq; exact h1 heq.symm
  -- Target: the initialiser call reduces to the renamed original entry.
  have hL1 : T.code.lookup start =
      some ([], .seq (nestedSeqHOL inits) (.call none nm []), rshape) := by
    rw [hTcode, HolFiniteMapExact.lookup_updateList, fupdateListLookup,
      lookupNoneOfNotMem _ _ (by
        rw [List.map_reverse, List.mem_reverse, hLkeys]; exact hstartNotRenamed)]
    simp [HolFiniteMapExact.update, FUPDATE]
  have hbodyMem : (nm, ([] : List (MlS × ShapeHOL)), fpermHOL start nm body, rshape) ∈
      functionsHOL (fpermDecsHOL start nm code) := by
    rw [functionsFpermDecsHOL]
    refine List.mem_map.mpr ⟨(start, [], body, rshape), lookupMem _ _ _ hstartLookup, ?_⟩
    simp [fpermName]
  have hL2 := hTlookup nm _ hbodyMem
  have hinitCall := semanticsInitCall' T start (nestedSeqHOL inits) nm rshape []
    (compileProgExactHOL ctx (fpermHOL start nm body)) t'
    ⟨hL1, hL2, hrun, hclk, by rw [hffi]⟩
  -- Source: rename the entry, empty the locals, and relate to the target.
  have hsDempty : sD.code = HolFiniteMapExact.empty := hsDcode.trans hcode
  have hupd : ∀ (m : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
      (l : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)),
      m.updateList l = m.updateListEq l := by
    intro m l
    apply HolFiniteMapExact.ext
    funext k
    simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_updateListEq]
    rw [FUPDATE_LIST_HOL_eq_FUPDATE_LIST]
  have hC2 : fpermCodeHOL start nm s1.code =
      HolFiniteMapExact.empty.updateList (functionsHOL (fpermDecsHOL start nm code)) := by
    rw [hs1form]
    simp only
    rw [hsDempty, functionsHOL_filter_isFunction, hupd, hupd,
      fpermCodeHOL_updateList_functions, fpermCodeHOL_empty]
  have hfperm := semanticsFpermHOL start nm s1 start
  have hname : fpermName start nm start = nm := by simp [fpermName]
  rw [hname, hC2] at hfperm
  have hempty := PanGlobalsSemanticsEmptyLocals.semanticsEmptyLocals
    { s1 with code := (HolFiniteMapExact.empty.updateList
      (functionsHOL (fpermDecsHOL start nm code))) } nm
  have hinv := Flapjack.evaluateInvariantsHOLFinite (nestedSeqHOL inits)
    (PanPropsEvalStateFiniteExact.ofPanSemFinite { T with locals := HolFiniteMapExact.empty })
    none (PanPropsEvalStateFiniteExact.ofPanSemFinite t') (by
      simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite, hrun])
  have htcode : t'.code = T.code := hinv.2.2.2.2.2.2.1
  have hrelT : panGlobalsStateRelHOLExact true ctx
      (emptyLocalsHOLFinite { s1 with code := (HolFiniteMapExact.empty.updateList
        (functionsHOL (fpermDecsHOL start nm code))) }) t' := by
    subst hs1form
    obtain ⟨h1, -, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, h16, h17, h18,
      h19⟩ := hrel'
    refine ⟨h1, fun _ => ?_, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ?_, h16,
      h17, h18, h19⟩
    · rw [hloc]; rfl
    · intro f ps p rs hlk
      change (HolFiniteMapExact.empty.updateList
        (functionsHOL (fpermDecsHOL start nm code))).lookup f = _ at hlk
      rw [emptyUpdateListLookup _ _ hfpNodup] at hlk
      rw [htcode]
      exact hTlookup f (ps, p, rs) (lookupMem _ _ _ hlk)
  have hsem := PanGlobalsStateRelImpSemantics.stateRelImpSemanticsHOL ctx _ t' nm
    ⟨hrelT, by rw [← hempty, hfperm]; exact hnf⟩
  rw [← hfperm, hempty, ← hsem, hinitCall]

end PanGlobalsCompileTopSemanticsDecls

end Flapjack
