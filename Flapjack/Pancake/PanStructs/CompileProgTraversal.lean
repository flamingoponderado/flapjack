import Flapjack.Pancake.PanStructs.CompileExpCorrespondence

/-! Flapjack production traversal for reviewed expression compilation.
It preserves the existing pass context updates; it is codec infrastructure,
not an independently tagged HOL program-correctness theorem. -/
namespace Flapjack
open Pancake.PanLang

def structCompileProgExactProduction {width : Nat} [NeZero width]
    (context : StructPassContext) : Prog (BitVec width) → Prog (BitVec width)
  | .dec name shape value body =>
      .dec name (structCompileShapeExactProduction context.structs shape)
        (structCompileExpExactProduction context value)
        (structCompileProgExactProduction { context with locals := (name, shape) :: context.locals }
          body)
  | .assign kind name value =>
      .assign kind name (structCompileExpExactProduction context value)
  | .primitive name operator arguments =>
      .primitive name operator (structCompileExps context arguments)
  | .store address value =>
      .store (structCompileExpExactProduction context address)
        (structCompileExpExactProduction context value)
  | .store32 address value =>
      .store32 (structCompileExpExactProduction context address)
        (structCompileExpExactProduction context value)
  | .storeByte address value =>
      .storeByte (structCompileExpExactProduction context address)
        (structCompileExpExactProduction context value)
  | .seq first second =>
      .seq (structCompileProgExactProduction context first)
        (structCompileProgExactProduction context second)
  | .ite condition thenBranch elseBranch =>
      .ite (structCompileExpExactProduction context condition)
        (structCompileProgExactProduction context thenBranch)
        (structCompileProgExactProduction context elseBranch)
  | .while condition body =>
      .while (structCompileExpExactProduction context condition)
        (structCompileProgExactProduction context body)
  | .call info function arguments =>
      let compiledInfo := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar,
              structCompileProgExactProduction context handler))
      .call compiledInfo function (structCompileExps context arguments)
  | .decCall name shape function arguments body =>
      .decCall name (structCompileShapeExactProduction context.structs shape) function
        (structCompileExps context arguments)
        (structCompileProgExactProduction { context with locals := (name, shape) :: context.locals }
          body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function (structCompileExpExactProduction context configuration)
        (structCompileExpExactProduction context configurationLength)
        (structCompileExpExactProduction context array)
        (structCompileExpExactProduction context arrayLength)
  | .raise exception value =>
      .raise exception (structCompileExpExactProduction context value)
  | .return value =>
      .return (structCompileExpExactProduction context value)
  | .shMemLoad size kind name address =>
      .shMemLoad size kind name (structCompileExpExactProduction context address)
  | .shMemStore size address value =>
      .shMemStore size (structCompileExpExactProduction context address)
        (structCompileExpExactProduction context value)
  | program => program
termination_by program => sizeOf program
where
  structCompileExps (context : StructPassContext) :
      List (Exp (BitVec width)) → List (Exp (BitVec width))
    | [] => []
    | expression :: expressions =>
        structCompileExpExactProduction context expression ::
          structCompileExps context expressions
termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

/-- Flapjack codec infrastructure for the production program compiler's
Primitive, Call and DecCall argument lists. It has no HOL theorem original:
the list induction connects the executed traversal to `compileExpsExact`,
using only the input context and expression range invariants. Order and
multiplicity are preserved, and no compiled-output premise is assumed. -/
theorem structCompileProgExactProduction_exps_encode {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (expressions : List (Exp (BitVec width))) (he : ∀ e ∈ expressions, ExpByteRanged e) :
    (structCompileProgExactProduction.structCompileExps context expressions).map expToHOL =
      Pancake.PanStructs.CompileShapeExact.compileExpsExact
        (structPassContextToExact context) (expressions.map expToHOL) := by
  induction expressions with
  | nil => simp [structCompileProgExactProduction.structCompileExps,
      Pancake.PanStructs.CompileShapeExact.compileExpsExact]
  | cons expression expressions ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at he
      simp only [structCompileProgExactProduction.structCompileExps, List.map_cons,
        Pancake.PanStructs.CompileShapeExact.compileExpsExact]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg expression he.1,
        ← compileExpExact_encode context hc hl hg expression he.1, ih he.2]

/-- Flapjack expression argument-list equality on genuine ranged inputs. -/
theorem structCompileProgExactProduction_exps_eq_legacy {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (expressions : List (Exp (BitVec width))) (he : ∀ e ∈ expressions, ExpByteRanged e) :
    structCompileProgExactProduction.structCompileExps context expressions =
      structCompileProg.structCompileExps context expressions := by
  induction expressions with
  | nil => simp [structCompileProgExactProduction.structCompileExps,
      structCompileProg.structCompileExps]
  | cons expression expressions ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at he
      simp [structCompileProgExactProduction.structCompileExps,
        structCompileProg.structCompileExps,
        structCompileExpExactProduction_eq_legacy context hc hl hg expression he.1, ih he.2]

/-- Flapjack production traversal equality, including local binding and optional
handler contexts. This is codec infrastructure with no HOL theorem original. -/
theorem structCompileProgExactProduction_eq_legacy {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      structCompileProgExactProduction context program = structCompileProg context program
  | .skip, _ => by simp [structCompileProgExactProduction, structCompileProg]
  | .dec name shape value body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hname, hshape, hvalue, hbody⟩
      have hl' : ListParamByteRanged ((name, shape) :: context.locals) := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · cases hp; exact ⟨hname, hshape⟩
        · exact hl p hp
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileShapeExactProduction_eq_legacy context.structs shape hc hshape]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value hvalue]
      rw [structCompileProgExactProduction_eq_legacy
        { context with locals := (name, shape) :: context.locals }
        hc hl' hg body hbody]
  | .assign kind name value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .primitive name operator arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileProgExactProduction_exps_eq_legacy context hc hl hg arguments h.2]
  | .store address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg address h.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .store32 address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg address h.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .storeByte address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg address h.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .seq first second, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg first h.1]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg second h.2]
  | .ite condition thenBranch elseBranch, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg condition h.1]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg thenBranch h.2.1]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg elseBranch h.2.2]
  | .while condition body, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg condition h.1]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg body h.2]
  | .break, _ => by simp [structCompileProgExactProduction, structCompileProg]
  | .continue, _ => by simp [structCompileProgExactProduction, structCompileProg]
  | .call none function arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileProgExactProduction_exps_eq_legacy context hc hl hg arguments h.2.1]
  | .call (some (returns, none)) function arguments, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileProgExactProduction_exps_eq_legacy context hc hl hg arguments h.2.1]
  | .call (some (returns, some (exception, handlerVar, handler))) function arguments, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨_, hargs, _, _, _, hhandler⟩
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileProgExactProduction_exps_eq_legacy context hc hl hg arguments hargs]
      rw [structCompileProgExactProduction_eq_legacy context hc hl hg handler hhandler]
  | .decCall name shape function arguments body, h => by
      simp only [ProgByteRanged] at h
      rcases h with ⟨hname, hshape, _, hargs, hbody⟩
      have hl' : ListParamByteRanged ((name, shape) :: context.locals) := by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with hp | hp
        · cases hp; exact ⟨hname, hshape⟩
        · exact hl p hp
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileShapeExactProduction_eq_legacy context.structs shape hc hshape]
      rw [structCompileProgExactProduction_exps_eq_legacy context hc hl hg arguments hargs]
      rw [structCompileProgExactProduction_eq_legacy
        { context with locals := (name, shape) :: context.locals }
        hc hl' hg body hbody]
  | .extCall function configuration configurationLength array arrayLength, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg configuration h.2.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg configurationLength h.2.2.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg array h.2.2.2.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg arrayLength h.2.2.2.2]
  | .raise exception value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .return value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h]
  | .shMemLoad size kind name address, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg address h.2]
  | .shMemStore size address value, h => by
      simp only [ProgByteRanged] at h
      simp only [structCompileProgExactProduction, structCompileProg]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg address h.1]
      rw [structCompileExpExactProduction_eq_legacy context hc hl hg value h.2]
  | .tick, _ => by simp [structCompileProgExactProduction, structCompileProg]
  | .annot tag text, _ => by simp [structCompileProgExactProduction, structCompileProg]
termination_by program _ => sizeOf program
decreasing_by
  all_goals
    first
    | decreasing_trivial
    | (simp_wf; omega)
    | omega


/-- Flapjack output-range infrastructure for the executed program traversal.
Only parser input and context invariants are assumed; the output range needed
by decoding is established here, rather than supplied as a premise. -/
theorem structCompileProgExactProduction_byteRanged {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (program : Prog (BitVec width)) (hp : ProgByteRanged program) :
    ProgByteRanged (structCompileProgExactProduction context program) := by
  rw [structCompileProgExactProduction_eq_legacy context hc hl hg program hp]
  exact structCompileProg_byteRanged context hc program hp

/-- Flapjack production-output codec roundtrip. The required output range is
derived internally, including identifiers in recursive bodies and handlers.
This is codec infrastructure with no independent HOL theorem original. -/
theorem structCompileProgExactProduction_codec_roundtrip {width : Nat} [NeZero width]
    (context : StructPassContext) (hc : CtxBR context.structs)
    (hl : ListParamByteRanged context.locals) (hg : ListParamByteRanged context.globals)
    (program : Prog (BitVec width)) (hp : ProgByteRanged program) :
    progOfHOL (progToHOL (structCompileProgExactProduction context program)) =
      structCompileProgExactProduction context program :=
  progOfHOL_progToHOL _
    (structCompileProgExactProduction_byteRanged context hc hl hg program hp)

end Flapjack
