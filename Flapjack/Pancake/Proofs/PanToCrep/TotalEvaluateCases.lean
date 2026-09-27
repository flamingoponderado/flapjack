import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.Semantics.PanSem.TotalMeasureIf
import Flapjack.Pancake.Semantics.CrepSem.TotalEval
import Flapjack.Pancake.Semantics.PanSem.EvaluateFinite
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL
import Flapjack.Pancake.PanToCrep.CompileProg
import Flapjack.Pancake.Proofs.PanToCrep.CodeRelExact
import Flapjack.Pancake.Proofs.PanToCrep.StateRelFiniteSupport
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap

/-!
# Total evaluator cases for Pan-to-Crep correctness

The declarations here assemble selected constructor cases from the total,
HOL-result-shaped source and target evaluator clauses. They are induction-case
support for `pc_compile_correct`; they do not claim the complete evaluator
induction or receive a standalone `@[hol]` reference.
-/

namespace Flapjack

/-! The `Skip` constructor case uses the total result×state clauses on both
  sides. The source evaluator uses the production `PanSemState`, and the target
  evaluator uses the code-bearing runtime state converted by `toHolState`. The
  compiled target syntax is exactly `Skip`. The returned runtime post-state is
  the original target state, so all four state/code/exception/local relations
  are established at the post-state boundary without a target-run premise. -/
theorem panToCrepTotalSkipStateCase
    {σ : Type _}
    (context : PanToCrepProofContext (RiscV.Word 64))
    (sourceState : PanSemState (RiscV.Word 64) (FfiState σ))
    (targetState : CrepRuntimeState (RiscV.Word 64) σ)
    (hstate : stateRel sourceState targetState)
    (hcode : codeRel context (panSemCodeAsLookup sourceState.code)
      targetState.code)
    (hexcp : excpRel context.eids sourceState.exceptionShapes)
    (hlocals : localsRel context sourceState.locals targetState.locals) :
    panSemEvaluateExprIfFragmentRiscV64ByMeasure (.leaf .skip) sourceState =
        (none, sourceState) ∧
    compileCodeRelProg context (.skip : Prog (RiscV.Word 64)) =
        (CrepProg.skip : CrepProg (BitVec 64)) ∧
    ∃ targetPost : CrepRuntimeState (RiscV.Word 64) σ,
      evalCrepClockLeaf .skip targetState.toHolState =
          (none, targetPost.toHolState) ∧
      stateRel sourceState targetPost ∧
      codeRel context (panSemCodeAsLookup sourceState.code) targetPost.code ∧
      excpRel context.eids sourceState.exceptionShapes ∧
      localsRel context sourceState.locals targetPost.locals := by
  refine ⟨by simp [panSemEvaluateExprIfFragmentRiscV64ByMeasure], rfl, ?_⟩
  refine ⟨targetState, by simp, hstate, ?_, hexcp, hlocals⟩
  exact hcode

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Skip]`.
The proof resumes this leaf case at `pan_to_crepProofScript.sml:493-496`;
the source evaluator clause is `panSemScript.sml:557`, the exact compiler
clause is `pan_to_crepScript.sml:140`, and the target evaluator clause is
`crepSemScript.sml:241`. Over `ProgHOL` and `CrepProgHOL`, source `Skip`
evaluates to normal completion without changing the source state, compiles to
target `Skip`, and the total Crep evaluator returns normal completion with the
same target state. This exact-carrier helper carries state/code/local/exception
relations unchanged and assumes no target run or result. It is distinct from
`panToCrepTotalSkipStateCase`, which uses production Pan/Crep carriers. This is
not the full `pc_compile_correct` theorem and carries no `@[hol]` tag. -/
theorem panToCrepExactSkipTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals)
    (hcode : codeRelExactHOLW compileContext sourceContext.state.code
      targetState.code)
    (hexcp : panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes) :
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.skip : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (none, sourceContext) ∧
    compileProgExactHOLW compileContext
        (.skip : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.skip : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.skip : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (none, targetState) ∧
    panToCrepStateRelFiniteExact sourceContext.state targetState ∧
    panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals ∧
    codeRelExactHOLW compileContext sourceContext.state.code targetState.code ∧
    panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes := by
  refine ⟨?_, ?_, ?_, hstate, hlocals, hcode, hexcp⟩
  · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext]
  · simp [compileProgExactHOLW]
  · rw [show compileProgExactHOLW compileContext
      (.skip : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.skip : CrepProgHOL width) by simp [compileProgExactHOLW]]
    exact evalCrepSemHOLProg_skip targetState memDec shMemDec

/-! First exact evaluator fragment for upstream
`eval_nested_assign_distinct_eq` (`pan_to_crepProofScript.sml:540`). The
theorem below isolates a successful Assign leaf over the exact
`CrepProgHOL`/`CrepSemHOLState` evaluator. It proves the existing local is
updated to the exact evaluated word_lab value with normal completion. The full
theorem remains open: it quantifies over arbitrary expression/name lists and
has five premises, including expression-variable noninterference and distinct
assignment names; nested Seq composition remains a follow-up. This leaf is
Flapjack-specific support, not the HOL theorem, and therefore has no `@[hol]`
tag. -/
theorem evalCrepSemHOLProg_assign_success
    {width : Nat} [NeZero width] {σ : Type}
    (state : CrepSemHOLState width σ)
    (memDec : (a : BitVec width) → Decidable (state.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (state.shMemaddrs a))
    (name : Nat) (src : CrepExpHOL width) (value old : HolWordLab width)
    (heval : crepExactEvalExp state memDec src = some value)
    (hbound : state.locals.lookup name = some old) :
    evalCrepSemHOLProg state memDec shMemDec (.assign name src) =
      (none, CrepSemHOLState.setVar name value state) := by
  rw [evalCrepSemHOLProg_assign, heval, hbound]

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Break]`.
The HOL proof resumes this nonrecursive case at
`pan_to_crepProofScript.sml:499-503`; the source evaluator equation is
`panSemScript.sml:623`, the compiler equation is `pan_to_crepScript.sml:219`,
and the target evaluator equation is `crepSemScript.sml:309`. They give source
`Break`, compiled `Break 0`, and target `Break 0`, all with unchanged states.
This helper checks those equations over the finite-support HOL-shaped carriers
and records preservation of the exact state/local/code/exception relations.
It is still a Flapjack-specific case helper rather than the assembled theorem,
so it carries no `@[hol]` tag. -/
theorem panToCrepExactBreakTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals)
    (hcode : codeRelExactHOLW compileContext sourceContext.state.code targetState.code)
    (hexcp : panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes) :
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.break : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (some .break, sourceContext) ∧
    compileProgExactHOLW compileContext
        (.break : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.break 0 : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.break : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (some (.break 0), targetState) ∧
    panToCrepStateRelFiniteExact sourceContext.state targetState ∧
    panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals ∧
    codeRelExactHOLW compileContext sourceContext.state.code targetState.code ∧
    panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes := by
  refine ⟨?_, ?_, ?_, hstate, hlocals, hcode, hexcp⟩
  · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext]
  · simp [compileProgExactHOLW]
  · rw [show compileProgExactHOLW compileContext
      (.break : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.break 0 : CrepProgHOL width) by simp [compileProgExactHOLW]]
    exact evalCrepSemHOLProg_break targetState memDec shMemDec 0

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Continue]`.
The proof resumes the nonrecursive constructor at
`pan_to_crepProofScript.sml:505-509`; the source evaluator equation is
`panSemScript.sml:624`, the exact compiler clause is
`pan_to_crepScript.sml:220`, and the target evaluator equation is
`crepSemScript.sml:313`. This slice establishes source `Continue`, compiled
`Continue 0`, and target `Continue 0`, preserving the exact source/target
state and local/code/exception relations. It remains a Flapjack-specific case
helper rather than the full `pc_compile_correct` theorem, so it carries no
`@[hol]` tag. The production-codec bridge
`compileProgExactHOLW_continue_bridge` is a distinct theorem and is not
duplicated here. -/
theorem panToCrepExactContinueTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals)
    (hcode : codeRelExactHOLW compileContext sourceContext.state.code targetState.code)
    (hexcp : panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes) :
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.continue : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (some .continue, sourceContext) ∧
    compileProgExactHOLW compileContext
        (.continue : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.continue 0 : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.continue : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (some (.continue 0), targetState) ∧
    panToCrepStateRelFiniteExact sourceContext.state targetState ∧
    panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals ∧
    codeRelExactHOLW compileContext sourceContext.state.code targetState.code ∧
    panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes := by
  refine ⟨?_, ?_, ?_, hstate, hlocals, hcode, hexcp⟩
  · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext]
  · simp [compileProgExactHOLW]
  · rw [show compileProgExactHOLW compileContext
      (.continue : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.continue 0 : CrepProgHOL width) by simp [compileProgExactHOLW]]
    exact evalCrepSemHOLProg_continue targetState memDec shMemDec 0

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Annot]`.
The proof resumes this no-op constructor at
`pan_to_crepProofScript.sml:511-515`; the source evaluator clause is
`panSemScript.sml:656`, the exact compiler erasure is
`pan_to_crepScript.sml:307`, and the target `Skip` evaluator clause is
`crepSemScript.sml:241`. The exact source carrier uses `MlS` tag/text values;
the compiler erases both and produces `Skip`, so both evaluators preserve their
states. This helper proves that target transition directly and preserves the
finite-exact state/code/local/exception relations without assuming a target
run. `code_rel_def` is represented by `codeRelExactHOLW`; this no-op case
carries it unchanged. This remains a Flapjack-specific prerequisite rather
than the full `pc_compile_correct` case, so no `@[hol]` tag is claimed. The
generic String-based `panToCrepPcCompileCorrectAnnotCodeState` does not
establish this exact-carrier result. -/
theorem panToCrepExactAnnotTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (tag text : Flapjack.Pancake.PanLang.MlS)
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals)
    (hcode : codeRelExactHOLW compileContext sourceContext.state.code
      targetState.code)
    (hexcp : panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes) :
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.annot tag text : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (none, sourceContext) ∧
    compileProgExactHOLW compileContext
        (.annot tag text : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.skip : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.annot tag text : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (none, targetState) ∧
    panToCrepStateRelFiniteExact sourceContext.state targetState ∧
    panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals ∧
    codeRelExactHOLW compileContext sourceContext.state.code targetState.code ∧
    panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes := by
  refine ⟨?_, ?_, ?_, hstate, hlocals, hcode, hexcp⟩
  · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext]
  · simp [compileProgExactHOLW]
  · rw [show compileProgExactHOLW compileContext
      (.annot tag text : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.skip : CrepProgHOL width) by simp [compileProgExactHOLW]]
    exact evalCrepSemHOLProg_skip targetState memDec shMemDec

/-! Source-reviewed prerequisite for HOL `pc_compile_correct[Tick]`.
The HOL proof resumes this clock-sensitive case at
`pan_to_crepProofScript.sml:517-524`; its exact transition clauses are
`panSemScript.sml:653`, `pan_to_crepScript.sml:306`, and
`crepSemScript.sml:332`. The helper gives both clock branches: at zero both
evaluators time out and clear locals; above zero both complete normally and
decrement the clock. It proves the target evaluation directly and preserves
the exact state/local/code/exception relations. This remains a
Flapjack-specific slice, not the full `pc_compile_correct` case; no `@[hol]`
tag is claimed. The existing
`evalPanSemRecursiveCallFiniteContext_tick_projection` relates the finite and
broad exact Pan clause, while `compileProgExactHOLW_tick_bridge` only compares
the exact compiler's Tick output after its output codec with production
`compileProgRiscV`; neither theorem is a production evaluator equivalence. -/
theorem panToCrepExactTickTransition
    {width : Nat} {σ : Type} [NeZero width]
    (sourceContext : PanSemStateFiniteExact.FiniteEvalContext width σ)
    (targetState : CrepSemHOLState width σ)
    (compileContext : PanToCrepContextExact width)
    (memDec : (a : BitVec width) → Decidable (targetState.memaddrs a))
    (shMemDec : (a : BitVec width) → Decidable (targetState.shMemaddrs a))
    (hstate : panToCrepStateRelFiniteExact sourceContext.state targetState)
    (hlocals : panToCrepLocalsRelFiniteExact compileContext
      sourceContext.state.locals targetState.locals)
    (hcode : codeRelExactHOLW compileContext sourceContext.state.code targetState.code)
    (hexcp : panToCrepExcpRelFiniteExact compileContext.eids
      sourceContext.state.eshapes) :
    let sourcePost :=
      if sourceContext.state.clock = 0 then
        PanSemStateFiniteExact.emptyLocalsHOLFinite sourceContext.state
      else PanSemStateFiniteExact.decClockHOLFinite sourceContext.state
    let targetPost :=
      if targetState.clock = 0 then
        CrepSemHOLState.emptyLocals targetState
      else decClockCrepSemHOL targetState
    PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.tick : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
      some (if sourceContext.state.clock = 0 then some .timeOut else none,
        sourceContext.withState sourcePost
          (by by_cases hzero : sourceContext.state.clock = 0 <;>
            simp [sourcePost, PanSemStateFiniteExact.emptyLocalsHOLFinite,
              PanSemStateFiniteExact.decClockHOLFinite, hzero])
          (by by_cases hzero : sourceContext.state.clock = 0 <;>
            simp [sourcePost, PanSemStateFiniteExact.emptyLocalsHOLFinite,
              PanSemStateFiniteExact.decClockHOLFinite, hzero])) ∧
    compileProgExactHOLW compileContext
        (.tick : Flapjack.Pancake.PanLang.ProgHOL width) =
      (.tick : CrepProgHOL width) ∧
    evalCrepSemHOLProg targetState memDec shMemDec
        (compileProgExactHOLW compileContext
          (.tick : Flapjack.Pancake.PanLang.ProgHOL width)) =
      (if targetState.clock = 0 then
        (some .timeOut, CrepSemHOLState.emptyLocals targetState)
      else (none, decClockCrepSemHOL targetState)) ∧
    panToCrepStateRelFiniteExact sourcePost targetPost ∧
    panToCrepLocalsRelFiniteExact compileContext sourcePost.locals targetPost.locals ∧
    codeRelExactHOLW compileContext sourcePost.code targetPost.code ∧
    panToCrepExcpRelFiniteExact compileContext.eids sourcePost.eshapes := by
  let sourcePost : PanSemStateFiniteExact width σ :=
    if sourceContext.state.clock = 0 then
      PanSemStateFiniteExact.emptyLocalsHOLFinite sourceContext.state
    else PanSemStateFiniteExact.decClockHOLFinite sourceContext.state
  let targetPost : CrepSemHOLState width σ :=
    if targetState.clock = 0 then
      CrepSemHOLState.emptyLocals targetState
    else decClockCrepSemHOL targetState
  have hcodePost : codeRelExactHOLW compileContext sourcePost.code targetPost.code := by
    by_cases hsourceZero : sourceContext.state.clock = 0 <;>
      by_cases htargetZero : targetState.clock = 0 <;>
      simpa [sourcePost, targetPost, hsourceZero, htargetZero,
        PanSemStateFiniteExact.emptyLocalsHOLFinite,
        PanSemStateFiniteExact.decClockHOLFinite, CrepSemHOLState.emptyLocals,
        decClockCrepSemHOL] using hcode
  have hexcpPost : panToCrepExcpRelFiniteExact compileContext.eids sourcePost.eshapes := by
    by_cases hsourceZero : sourceContext.state.clock = 0 <;>
      by_cases htargetZero : targetState.clock = 0 <;>
      simpa [sourcePost, targetPost, hsourceZero, htargetZero,
        PanSemStateFiniteExact.emptyLocalsHOLFinite,
        PanSemStateFiniteExact.decClockHOLFinite, CrepSemHOLState.emptyLocals,
        decClockCrepSemHOL] using hexcp
  rcases hstate with ⟨hmem, hmemaddrs, hshmem, hstructs, hglobals,
    hclock, hbe, hffi, hbase, htop⟩
  have hsource :
      PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext
        (.tick : Flapjack.Pancake.PanLang.ProgHOL width) sourceContext =
        some (if sourceContext.state.clock = 0 then some .timeOut else none,
          sourceContext.withState sourcePost
            (by by_cases hz : sourceContext.state.clock = 0 <;>
              simp [sourcePost, PanSemStateFiniteExact.emptyLocalsHOLFinite,
                PanSemStateFiniteExact.decClockHOLFinite, hz])
            (by by_cases hz : sourceContext.state.clock = 0 <;>
              simp [sourcePost, PanSemStateFiniteExact.emptyLocalsHOLFinite,
                PanSemStateFiniteExact.decClockHOLFinite, hz])) := by
    by_cases hzero : sourceContext.state.clock = 0
    · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext,
        sourcePost, hzero]
    · simp [PanSemStateFiniteExact.evalPanSemRecursiveCallFiniteContext,
        sourcePost, hzero]
  have hcompile : compileProgExactHOLW compileContext
      (.tick : Flapjack.Pancake.PanLang.ProgHOL width) =
        (.tick : CrepProgHOL width) := by
    simp [compileProgExactHOLW]
  refine ⟨hsource, hcompile, ?_, ?_, ?_, hcodePost, hexcpPost⟩
  · rw [hcompile]
    exact evalCrepSemHOLProg_tick targetState memDec shMemDec
  · by_cases hzero : sourceContext.state.clock = 0
    · have htargetZero : targetState.clock = 0 := by rw [← hclock, hzero]
      simpa [panToCrepStateRelFiniteExact, sourcePost, targetPost, hzero,
        htargetZero, PanSemStateFiniteExact.emptyLocalsHOLFinite,
        CrepSemHOLState.emptyLocals] using
        (show panToCrepStateRelFiniteExact sourceContext.state targetState from
          ⟨hmem, hmemaddrs, hshmem, hstructs, hglobals, hclock, hbe, hffi,
            hbase, htop⟩)
    · have htargetNonzero : targetState.clock ≠ 0 := by
        intro hz
        exact hzero (hclock.trans hz)
      simpa [panToCrepStateRelFiniteExact, sourcePost, targetPost, hzero,
        htargetNonzero, PanSemStateFiniteExact.decClockHOLFinite,
        decClockCrepSemHOL, hclock] using
        (show panToCrepStateRelFiniteExact sourceContext.state targetState from
          ⟨hmem, hmemaddrs, hshmem, hstructs, hglobals, hclock, hbe, hffi,
            hbase, htop⟩)
  · by_cases hzero : sourceContext.state.clock = 0
    · rcases hlocals with ⟨hnoOverlap, hctxtMax, _hlocals⟩
      refine ⟨hnoOverlap, hctxtMax, ?_⟩
      intro name value hlookup
      simp [hzero, PanSemStateFiniteExact.emptyLocalsHOLFinite] at hlookup
    · have htargetNonzero : targetState.clock ≠ 0 := by
        intro hz
        exact hzero (hclock.trans hz)
      simpa [sourcePost, targetPost, hzero, htargetNonzero,
        PanSemStateFiniteExact.decClockHOLFinite, decClockCrepSemHOL] using hlocals

end Flapjack
