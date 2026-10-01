import Flapjack.Compiler.Backend.Semantics.StackSem.Inst
import Flapjack.Compiler.Backend.StackProps.ExpressionClock

/-! Full original StackProps instruction field-preservation and clock/FFI
commutation statements over the native total primitive instHOL operation.
Inherited reals_as_rational_cuts remains the external SOUNDNESS item 8
assumption; this does not establish the stronger full real-carrier acceptance
criterion or the clocked evaluator/whole compiler theorem. -/
namespace Flapjack.StackPropsInstructionConstants
open Compiler.Encoders.Asm StackSemInst StackSemIntegerInstructions
  StackSemFpInstructions StackSemFpRegisterInstructions StackSemExpressions
  StackSemStateOps StackPropsExpressionClock

/-- Same-module canonical codec for the actual native state owner. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
        (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
        StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateOps.holFmapAsFiniteSupportWitness

/-- Full original thirteen-field successful-instruction conclusion. Only the
original primitive execution equality is a premise. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "inst_const"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem instConst {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : HolInst width) (s t : StackSemStateFiniteExact width C F)
    (h : instHOL i s = some t) :
    t.ffi = s.ffi ∧ t.clock = s.clock ∧ t.useAlloc = s.useAlloc ∧
    t.useStore = s.useStore ∧ t.useStack = s.useStack ∧ t.code = s.code ∧
    t.be = s.be ∧ t.gcFun = s.gcFun ∧ t.mdomain = s.mdomain ∧
    t.shMdomain = s.shMdomain ∧ t.bitmaps = s.bitmaps ∧
    t.compile = s.compile ∧ t.compileOracle = s.compileOracle := by
  cases i <;> simp only [instHOL, instFp, instInteger, instFpRegister,
    instFpSqrt, instFpToInt, instFpFromInt, Option.join_some] at h
  all_goals repeat' split at h
  all_goals try simp only [assign] at h
  all_goals repeat' split at h
  all_goals try contradiction
  all_goals try simp only [Option.some.injEq] at h
  all_goals cases h
  all_goals try simp [setVar, setFpVar]
  all_goals have hmem := ‹StackSemStateOps.memStore _ _ s = some t›
  all_goals unfold StackSemStateOps.memStore at hmem
  all_goals split at hmem
  all_goals cases hmem
  all_goals simp

/-- Flapjack auxiliary: the same native expression evaluator reads no FFI
field. There is no standalone HOL declaration for this helper; it discharges
an internal step of the original inst_clock_neutral_ffi proof. -/
private theorem wordExpWithFfi {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (s : StackSemStateFiniteExact width C F)
    (y : WordLangExpHOL (BitVec width)) (k : HolFfiState OtherF) :
    wordExp ({ s with ffi := k } : StackSemStateFiniteExact width C OtherF) y = wordExp s y := by
  refine WordLangExpHOL.rec
    (motive_1 := fun e : WordLangExpHOL (BitVec width) =>
      wordExp ({ s with ffi := k } : StackSemStateFiniteExact width C OtherF) e = wordExp s e)
    (motive_2 := fun es : List (WordLangExpHOL (BitVec width)) =>
      ∀ e ∈ es, wordExp ({ s with ffi := k } : StackSemStateFiniteExact width C OtherF) e = wordExp s e)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ y
  · intro value; simp only [wordExp]
  · intro register; simp only [wordExp]
  · intro name; simp only [wordExp]
  · intro address ih
    simp only [wordExp, ih, memLoad]
  · intro operator arguments ih
    simp only [wordExp]
    have hmap : arguments.attach.map (fun e => wordExp ({ s with ffi := k } : StackSemStateFiniteExact width C OtherF) e.val) =
        arguments.attach.map (fun e => wordExp s e.val) := by
      apply List.map_congr_left
      intro e _
      exact ih e.val e.property
    rw [hmap]
  · intro operator left right ihLeft ihRight
    simp only [wordExp, ihLeft, ihRight]
  · intro e h; cases h
  · intro head tail ihHead ihTail e he
    rcases List.mem_cons.mp he with rfl | ht
    · exact ihHead
    · exact ihTail e ht

/-- Flapjack auxiliary for the original FFI commutation proof, derived from
actual expression evaluation and register update. No callback law is assumed. -/
private theorem assignWithFfi {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (x : Nat) (y : WordLangExpHOL (BitVec width))
    (s : StackSemStateFiniteExact width C F) (k : HolFfiState OtherF) :
    assign x y ({ s with ffi := k } : StackSemStateFiniteExact width C OtherF) =
      (assign x y s).map (fun s => { s with ffi := k }) := by
  simp only [assign, wordExpWithFfi]
  cases wordExp s y <;> simp [setVar]

/-- Full original OPTION_MAP clock commutation, over the actual complete
native primitive operation; success and semantic failure are both included. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "inst_with_const"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem instWithClock {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : HolInst width) (s : StackSemStateFiniteExact width C F) (k : Nat) :
    instHOL i { s with clock := k } =
      (instHOL i s).map (fun s => { s with clock := k }) := by
  cases i <;> simp only [instHOL, instFp, instInteger, instFpRegister,
    instFpSqrt, instFpToInt, instFpFromInt, Option.join_some,
    assignWithClock, wordExpWithClock, getVar, StackSemStateOps.getVars, getFpVar,
    memLoad, memStore, setVar, setFpVar]
  all_goals repeat' (split <;> try simp_all)
  all_goals try simp_all

/-- Full original two-implication conjunction, retaining its arbitrary t and
both the successful-result and semantic-failure branches. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "inst_clock_neutral"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem instClockNeutral {width : Nat} [NeZero width] {C : Type} {F : Type}
    (i : HolInst width) (s t : StackSemStateFiniteExact width C F) (k : Nat) :
    (instHOL i s = some t → instHOL i { s with clock := k } = some { t with clock := k }) ∧
    (instHOL i s = none → instHOL i { s with clock := k } = none) := by
  constructor <;> intro h <;> simp [instWithClock, h]

/-- Flapjack Option-map auxiliary discharging the full original local
inst_clock_neutral_ffi statement; not a separate tagged HOL theorem. -/
private theorem instWithFfi {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (i : HolInst width) (s : StackSemStateFiniteExact width C F) (k : HolFfiState OtherF) :
    instHOL i ({ s with ffi := k } : StackSemStateFiniteExact width C OtherF) =
      (instHOL i s).map (fun s => { s with ffi := k }) := by
  cases i <;> simp only [instHOL, instFp, instInteger, instFpRegister,
    instFpSqrt, instFpToInt, instFpFromInt, Option.join_some,
    assignWithFfi, wordExpWithFfi, getVar, StackSemStateOps.getVars, getFpVar,
    memLoad, memStore, setVar, setFpVar]
  all_goals repeat' (split <;> try simp_all)
  all_goals try simp_all

/-- Full original FFI-update conjunction, with both success and NONE cases.
The updated FFI state has the original arbitrary host carrier. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "inst_clock_neutral_ffi"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem instClockNeutralFfi {width : Nat} [NeZero width] {C : Type} {F : Type} {OtherF : Type}
    (i : HolInst width) (s t : StackSemStateFiniteExact width C F) (k : HolFfiState OtherF) :
    (instHOL i s = some t → instHOL i ({ s with ffi := k } : StackSemStateFiniteExact width C OtherF) = some { t with ffi := k }) ∧
    (instHOL i s = none → instHOL i ({ s with ffi := k } : StackSemStateFiniteExact width C OtherF) = none) := by
  constructor <;> intro h <;> simp [instWithFfi, h]

end Flapjack.StackPropsInstructionConstants
