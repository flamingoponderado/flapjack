import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsSimulation
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsState
import Flapjack.Pancake.Proofs.PanGlobals.InitGlobalsRecursiveDisjoint

namespace Flapjack.PanGlobalsInitGlobalsAssembly
open Flapjack.PanGlobalsInitGlobalsSimulation
open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact
open Flapjack.Compiler.Backend.StackRemove (addresses)

/-- Canonical state roundtrips for the relation representation. -/
theorem holFmapAsFiniteSupportRelationWitness_PanSemStateFiniteExact
    {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

/-- Canonical context roundtrip for the relation representation. -/
theorem holFmapAsFiniteSupportRelationWitness_PanGlobalsContextExact
    {width : Nat} [NeZero width] (context : PanGlobalsContextExact width) :
    PanGlobalsContextExact.ofBroad (PanGlobalsContextExact.toBroad context) = context :=
  PanGlobalsContextExact.holFmapAsFiniteSupportWitness context

/-- Recursive initializer assembly using the original tail induction hypothesis.
All original premises are retained by initGlobalsGoal; only the literal guarded tail IH is added. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_init_globals_lemma"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem initGlobalsCons {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (ctxt : PanGlobalsContextExact width)
    (shape : ShapeHOL) (name : MlS) (expression : ExpHOL width)
    (decls : List (DeclHOL width))
    (ih : ∀ (value : ValueHOL width),
      @evalHOLFinite width σ _ s.emptyLocalsHOLFinite
        (fun a => Classical.propDecidable (s.memaddrs a)) expression = some value →
      shapeEqHOL shape (shapeOfHOLExact value) = true →
      ∀ nextContext, initGlobalsGoal (setGlobalHOLFinite name value s) decls nextContext) :
    initGlobalsGoal s (.decl shape name expression :: decls) ctxt := by
  classical
  intro s' decls' funs exns ctxt' t freeAddrs
    ⟨heval, hdecls, hcompile, hrel, hfree, hexcluded, hcoverage, halign, hcode, hdisjoint, hbound⟩
  simp only [evaluateDeclsHOLFinite] at heval
  cases hv : @evalHOLFinite width σ _ s.emptyLocalsHOLFinite
      (fun a => Classical.propDecidable (s.memaddrs a)) expression with
  | none => simp [hv] at heval
  | some value =>
    simp only [hv] at heval
    by_cases hs : shapeEqHOL shape (shapeOfHOLExact value) = true
    · rw [if_pos hs] at heval
      have hshape : shapeOfHOLExact value = shape := ((shapeEqHOL_eq_true _ _).mp hs).symm
      let tailSize := ((decShapesHOL decls).map sizeOfShapeHOL).sum
      let offset := ctxt.globalsSize + panBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL shape)
      let nextContext : PanGlobalsContextExact width :=
        {ctxt with globals := ctxt.globals.updateEq (name, (shape, offset)), globalsSize := offset}
      have hsize : ((decShapesHOL (.decl shape name expression :: decls)).map sizeOfShapeHOL).sum =
          sizeOfShapeHOL shape + tailSize := rfl
      rw [hsize] at hfree hbound
      subst freeAddrs
      obtain ⟨memory, hstore, hnextRel⟩ := PanGlobalsInitGlobalsState.initializerHeadStateRel
        s t ctxt name expression value shape tailSize hrel hv hshape hbound halign hcode
        hcoverage hexcluded hdisjoint
      have hcontext := PanGlobalsInitGlobalsContext.initializerContext
        s t ctxt name expression value shape hrel hv hshape halign
      have hwidth := hrel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      obtain ⟨htailCoverage, htailExcluded, _⟩ :=
        PanGlobalsInitGlobalsRanges.recursiveFreeRangePremises t.topAddr ctxt.globalsSize
          (sizeOfShapeHOL shape) tailSize s.memaddrs t.memaddrs hwidth hbound hcoverage hexcluded
      have htailDisjoint := PanGlobalsInitGlobalsRecursiveDisjoint.recursiveGlobalsFreeDisjoint
        s t ctxt name shape value tailSize hrel hbound hdisjoint
      have htailBound : (panBytesInWord width).toNat * tailSize < 2 ^ width :=
        Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_add_left _ _)) hbound
      have htailDecls : ∀ d ∈ decls, isDeclHOL d = true :=
        fun d hd => hdecls d (List.mem_cons_of_mem _ hd)
      generalize htailCompile : compileDecsExactHOL nextContext decls = compiled
      obtain ⟨initializers, functions, exceptions, finalContext⟩ := compiled
      have hcompiledExpression := initializerExpression s t ctxt expression value hrel hv
      obtain ⟨t', hrun, hfinalRel, hclock, hffi, hlocals, hfinalAlign⟩ :=
        ih value hv hs nextContext s' initializers functions exceptions finalContext
          {t with memory := memory}
          (addresses (t.topAddr - panBytesInWord width * BitVec.ofNat width tailSize - offset) tailSize)
          ⟨heval, htailDecls, htailCompile, hnextRel, rfl, htailExcluded, htailCoverage,
            hcontext.2.1, hcode, htailDisjoint, htailBound⟩
      simp only [compileDecsExactHOL, compileDecsGlobalAddressExact_eq] at hcompile
      change (let out := compileDecsExactHOL nextContext decls;
        (.store (.op .sub [.topAddr, .const offset]) (compileExpExactHOL ctxt expression) :: out.1,
        out.2.1, out.2.2.1, out.2.2.2)) = (decls', funs, exns, ctxt') at hcompile
      rw [htailCompile] at hcompile
      dsimp only at hcompile
      obtain ⟨rfl, rfl, rfl, rfl⟩ := Prod.mk.inj hcompile
      refine ⟨t', ?_, hfinalRel, hclock, hffi, hlocals, hfinalAlign⟩
      have hhead : evaluateHOLFiniteState t
          (.store (.op .sub [.topAddr, .const offset]) (compileExpExactHOL ctxt expression)) =
          (none, {t with memory := memory}) := by
        rw [evaluateHOLFiniteState_store]
        change (match (some (.val (.word (t.topAddr - offset))) : Option (ValueHOL width)) with
          | some (.val (.word address)) =>
            match @evalHOLFinite width σ _ t
                (fun a => Classical.propDecidable (t.memaddrs a)) (compileExpExactHOL ctxt expression) with
            | some value => match panMemStoresHOL address (flattenHOL value) t.memaddrs t.memory with
              | some memory => (none, {t with memory := memory})
              | none => (some (PanSemResultExact.error (width := width)), t)
            | none => (some (PanSemResultExact.error (width := width)), t)
          | _ => (some (PanSemResultExact.error (width := width)), t)) = _
        simp only [hcompiledExpression]
        rw [hstore]
      rw [nestedSeqHOL, evaluateHOLFiniteState_seq, hhead]
      simpa [fixClockHOLFinite] using hrun
    · rw [if_neg hs] at heval
      cases heval

/-- Declaration-list induction over the original initializer goal. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_init_globals_lemma"
  (fmap_as_finite_support_relation := [PanSemStateFiniteExact.locals,
    PanSemStateFiniteExact.globals, PanSemStateFiniteExact.code,
    PanSemStateFiniteExact.eshapes, PanGlobalsContextExact.globals])
  (words_as_type_indexed_bitvec)]
theorem initGlobalsAll {width : Nat} {σ : Type} [NeZero width]
    (s : PanSemStateFiniteExact width σ) (decls : List (DeclHOL width))
    (ctxt : PanGlobalsContextExact width) : initGlobalsGoal s decls ctxt := by
  induction decls generalizing s ctxt with
  | nil => exact initGlobalsNil s ctxt
  | cons declaration declarations ih =>
    cases declaration with
    | decl shape name expression =>
      exact initGlobalsCons s ctxt shape name expression declarations
        (fun value _ _ nextContext => ih (setGlobalHOLFinite name value s) nextContext)
    | name shape name =>
      intro s' ds fs es ctxt' t free h
      have impossible := h.2.1 (.name shape name) (by simp)
      simp [isDeclHOL] at impossible
    | function f =>
      intro s' ds fs es ctxt' t free h
      have impossible := h.2.1 (.function f) (by simp)
      simp [isDeclHOL] at impossible
    | exnDecl name shape =>
      intro s' ds fs es ctxt' t free h
      have impossible := h.2.1 (.exnDecl name shape) (by simp)
      simp [isDeclHOL] at impossible

end Flapjack.PanGlobalsInitGlobalsAssembly
