import Flapjack.HolRef
import Flapjack.Pancake.WordLang
import Flapjack.Pancake.WordLang.OccurrencesExact
import Flapjack.Compiler.Encoders.Asm
import Flapjack.Compiler.Backend.RegAlloc

/-!
# CakeML backend `wordConvs` syntactic conventions

Counterpart of `cakeml/compiler/backend/semantics/wordConvsScript.sml`.  This
module ports the label-preservation relation and `extract_labels` over the
faithful backend `wordLang$prog` model of `Flapjack.Pancake.WordLang`; the
remaining conventions land in follow-up slices.

HOL's `set new_labs SUBSET set old_labs` is represented pointwise as
`∀ label, label ∈ newLabels → label ∈ oldLabels`, which is exactly set
inclusion and needs no `DecidableEq` instance; `ALL_DISTINCT` is `List.Nodup`.
The `num_set` cut-set carriers of `WordLangProg` are modelled by
`FiniteMap Nat Unit`, which fixes `num_set` lookup behaviour;
`extract_labels` never inspects them.
-/

namespace Flapjack

open Flapjack.Compiler.Encoders.Asm

/-- Exact source counterpart of CakeML `wordConvs$labels_rel_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:139-143`): labels may be
forgotten but not invented, and distinctness is preserved. -/
@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_def"]
def labelsRel (oldLabels newLabels : List β) : Prop :=
  (oldLabels.Nodup → newLabels.Nodup) ∧
    ∀ label, label ∈ newLabels → label ∈ oldLabels

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_refl"]
theorem labelsRel_refl (labels : List β) : labelsRel labels labels :=
  ⟨fun distinct => distinct, fun _ member => member⟩

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_APPEND"]
theorem labelsRel_append {xs xs₁ ys ys₁ : List β}
    (hxs : labelsRel xs xs₁) (hys : labelsRel ys ys₁) :
    labelsRel (xs ++ ys) (xs₁ ++ ys₁) := by
  obtain ⟨hxsDistinct, hxsSubset⟩ := hxs
  obtain ⟨hysDistinct, hysSubset⟩ := hys
  refine ⟨?_, ?_⟩
  · intro hdistinct
    obtain ⟨hxsNodup, hysNodup, hdisjoint⟩ := List.nodup_append.mp hdistinct
    refine List.nodup_append.mpr ⟨hxsDistinct hxsNodup, hysDistinct hysNodup, ?_⟩
    intro a inXs₁ b inYs₁ equal
    exact hdisjoint a (hxsSubset a inXs₁) b (hysSubset b inYs₁) equal
  · intro label member
    rw [List.mem_append] at member
    rw [List.mem_append]
    rcases member with member | member
    · exact Or.inl (hxsSubset label member)
    · exact Or.inr (hysSubset label member)

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_CONS"]
theorem labelsRel_cons {x x₁ : β} {ys ys₁ : List β}
    (hx : labelsRel [x] [x₁]) (hys : labelsRel ys ys₁) :
    labelsRel (x :: ys) (x₁ :: ys₁) := by
  simpa using labelsRel_append hx hys

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "labels_rel_TRANS"]
theorem labelsRel_trans {xs ys zs : List β}
    (hxy : labelsRel xs ys) (hyz : labelsRel ys zs) : labelsRel xs zs := by
  obtain ⟨hxyDistinct, hxySubset⟩ := hxy
  obtain ⟨hyzDistinct, hyzSubset⟩ := hyz
  exact ⟨fun distinct => hyzDistinct (hxyDistinct distinct),
    fun label member => hxySubset label (hyzSubset label member)⟩

@[hol "cakeml/compiler/backend/semantics/wordConvsScript.sml" "PERM_IMP_labels_rel"]
theorem labelsRel_of_perm {xs ys : List β} (hperm : xs.Perm ys) : labelsRel ys xs :=
  ⟨fun distinct => hperm.symm.nodup distinct, fun _ member => hperm.subset member⟩

/-- Exact source counterpart of CakeML `wordConvs$extract_labels_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:440-459`): collect the
handler label pairs a program mentions, descending into `Call` return/handler
bodies, `MustTerminate`, `Seq`, `Loop`, and `If`, and returning no labels for
every other constructor.  The `Call` case keeps HOL's nesting: with no return
metadata there are no labels; otherwise the return-handler labels come first
(followed by the handler-body pair when a handler exists, and the
return-handler's own labels last).

HOL's `wordLang$prog` carries `num_set` and `mlstring` fields exactly in the
WordLangProgHOL carrier below. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def extractLabels {width : Nat} : WordLangProgHOL (BitVec width) → List (Nat × Nat)
  | .call returns _ _ handler =>
      match returns, handler with
      | none, _ => []
      | some (_, _, returnHandler, l1, l2), none =>
          [(l1, l2)] ++ extractLabels returnHandler
      | some (_, _, returnHandler, l1, l2), some (_, handlerProg, l1', l2') =>
          [(l1, l2), (l1', l2')] ++ extractLabels returnHandler ++
            extractLabels handlerProg
  | .mustTerminate body => extractLabels body
  | .seq first second => extractLabels first ++ extractLabels second
  | .loop _ body _ => extractLabels body
  | .ite _ _ _ thenBranch elseBranch =>
      extractLabels thenBranch ++ extractLabels elseBranch
  | _ => []

/-- Exact source counterpart of CakeML `wordConvs$distinct_tar_reg_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:267-279`): whether an
instruction's destination differs from the registers it reads.  Every other
instruction is accepted.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def distinctTarReg {width : Nat} : WordLangInst (BitVec width) → Bool
  | .arith (.binop _ r1 _ ri) => match ri with
      | .reg r => decide (r ≠ r1)
      | .imm _ => true
  | .arith (.shift _ r1 _ ri) => match ri with
      | .reg r => decide (r ≠ r1)
      | .imm _ => true
  | .arith (.addCarry r1 _ r3 r4) => decide (r1 ≠ r3 ∧ r1 ≠ r4)
  | .arith (.addOverflow r1 _ r3 _) => decide (r1 ≠ r3)
  | .arith (.subOverflow r1 _ r3 _) => decide (r1 ≠ r3)
  | _ => true

/-- Exact source counterpart of CakeML `wordConvs$two_reg_inst_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:284-296`): whether an
instruction is two-register (the destination equals the first source) for the
arithmetic forms that require it.  Every other instruction is accepted.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def twoRegInst {width : Nat} : WordLangInst (BitVec width) → Bool
  | .arith (.binop _ r1 r2 _) => r1 == r2
  | .arith (.shift _ r1 r2 _) => r1 == r2
  | .arith (.addCarry r1 r2 _ _) => r1 == r2
  | .arith (.addOverflow r1 r2 _ _) => r1 == r2
  | .arith (.subOverflow r1 r2 _ _) => r1 == r2
  | _ => true

/-- Exact source counterpart of CakeML `wordConvs$every_inst_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:299-315`): whether a
predicate holds on every `Inst` reachable through the program's structural
positions (`Seq`, `Loop`, `If`, `MustTerminate`, `Call` bodies, and the
synthetic instruction of `OpCurrHeap`).  Note HOL's `Call` nesting: when the
return metadata is `NONE` the result is `T` regardless of the handler. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def everyInst {width : Nat} (P : WordLangInst (BitVec width) → Bool) :
    WordLangProgHOL (BitVec width) → Bool
  | .inst instruction => P instruction
  | .seq first second => everyInst P first && everyInst P second
  | .loop _ body _ => everyInst P body
  | .ite _ _ _ thenBranch elseBranch => everyInst P thenBranch && everyInst P elseBranch
  | .opCurrHeap bop r1 r2 => P (.arith (.binop bop r1 r2 (.reg r2)))
  | .mustTerminate body => everyInst P body
  | .call returns _ _ handler =>
      match returns with
      | none => true
      | some (_, _, returnHandler, _, _) =>
          everyInst P returnHandler &&
            match handler with
            | none => true
            | some (_, handlerProg, _, _) => everyInst P handlerProg
  | _ => true

/-- HOL `wordConvs$flat_exp_conventions` (`wordConvsScript.sml:179-205`):
whether a program keeps all expressions flat.  Top-level expressions are
forbidden in `Assign` and `Store`, allowed only as `Var` in `Set`, and in
`ShareInst` allowed only as `Var` or `Op Add [Var r; Const c]`.  Descends
through `Seq`, `Loop`, `If`, `MustTerminate` and both `Call` bodies (the
return and handler cases are both required, so a `Call` with no return
metadata but a non-flat handler is rejected). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def flatExpConventions {width : Nat} : WordLangProgHOL (BitVec width) → Bool
  | .assign _ _ => false
  | .store _ _ => false
  | .set _ (.var _) => true
  | .set _ _ => false
  | .shareInst _ _ (.var _) => true
  | .shareInst _ _ (.op .add [.var _, .const _]) => true
  | .shareInst _ _ _ => false
  | .seq first second => flatExpConventions first && flatExpConventions second
  | .loop _ body _ => flatExpConventions body
  | .ite _ _ _ thenBranch elseBranch =>
      flatExpConventions thenBranch && flatExpConventions elseBranch
  | .mustTerminate body => flatExpConventions body
  | .call returns _ _ handler =>
      (match returns with
        | none => true
        | some (_, _, returnHandler, _, _) => flatExpConventions returnHandler) &&
        (match handler with
          | none => true
          | some (_, handlerProg, _, _) => flatExpConventions handlerProg)
  | _ => true

/-- Exact source counterpart of CakeML `wordConvs$inst_ok_less_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:208-249`).  This is the
weaker per-instruction well-formedness predicate used by
`compile_to_word_conventions2`: unlike `asm$inst_ok` it omits the operand
register checks and only constrains the configuration-dependent immediate and
offset conditions.  The `Mem` branch lists `Load`/`Store`/`Load16`/`Store16`/
`Load32`/`Store32` in its first case, so the `hw_offset_ok` case is only
reachable for the remaining memops in the HOL definition.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def instOkLess {width : Nat} (config : AsmConfig width) :
    WordLangInst (BitVec width) → Bool
  | .arith (.binop operator _ _ (.imm value)) => config.validImm (.inl operator) value
  | .arith (.shift operator _ _ (.imm value)) =>
      (!(value == 0) || operator == .lsl) && value.toNat < width
  | .arith (.div ..) =>
      config.isa == .armv8 || config.isa == .mips || config.isa == .riscv
  | .arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) =>
      (!(config.isa == .armv7) || !(destinationLeft == destinationRight)) &&
        (!(config.isa == .armv8 || config.isa == .riscv || config.isa == .ag32) ||
          (!(destinationLeft == sourceLeft) && !(destinationLeft == sourceRight)))
  | .arith (.longDiv ..) => config.isa == .x86_64
  | .arith (.addCarry destination _ sourceLeft sourceRight) =>
      (!(config.isa == .mips || config.isa == .riscv) ||
        (!(destination == sourceLeft) && !(destination == sourceRight)))
  | .arith (.addOverflow destination _ sourceLeft _) =>
      (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))
  | .arith (.subOverflow destination _ sourceLeft _) =>
      (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))
  | .mem operator _ (.addr _ offset) =>
      (if operator == .load || operator == .store || operator == .load16 ||
          operator == .store16 || operator == .load32 || operator == .store32 then
        asmAddrOffsetOk config offset
       else if operator == .load16 || operator == .store16 then
        asmHwOffsetOk config offset
       else
        asmByteOffsetOk config offset)
  | _ => true

/-- Flapjack-only shared program traversal for the broad executed validity
predicate and its exact-carrier counterpart. HOL has a fixed configuration
argument, not these policy parameters; this infrastructure has no HOL original.
The complete recursive clause order and Call/ShareInst behavior are shared. -/
def fullInstOkLessWith {width : Nat}
    (instructionOk : WordLangInst (BitVec width) → Bool)
    (addressOk : HolMemop → BitVec width → Bool) :
    WordLangProgHOL (BitVec width) → Bool
  | .inst value => instructionOk value
  | .seq first second =>
      fullInstOkLessWith instructionOk addressOk first && fullInstOkLessWith instructionOk addressOk second
  | .loop _ body _ => fullInstOkLessWith instructionOk addressOk body
  | .ite _ _ _ thenBranch elseBranch =>
      fullInstOkLessWith instructionOk addressOk thenBranch && fullInstOkLessWith instructionOk addressOk elseBranch
  | .mustTerminate body => fullInstOkLessWith instructionOk addressOk body
  | .call returns _ _ handler =>
      match returns with
      | none => true
      | some (_, _, returnHandler, _, _) =>
          fullInstOkLessWith instructionOk addressOk returnHandler &&
            match handler with
            | none => true
            | some (_, handlerProg, _, _) => fullInstOkLessWith instructionOk addressOk handlerProg
  | .shareInst operator _ address =>
      match expToAddrHOL address with
      | some (.addr _ offset) => addressOk operator offset
      | none => false
  | _ => true

/-- Broad program-validity compatibility wrapper. It retains the original
width-general behavior, including width zero, and uses AsmConfig whose encoder
consumes AsmData and produces UInt8 lists. Those carriers differ from HOL's
positive-width asm_config with HolAsm/word8 encoder, so this wrapper is untagged.
The faithful full_inst_ok_less port is fullInstOkLessExact in the counterpart
submodule; the shared recursive traversal avoids a duplicate program semantics.
Source-call audit: this guard is a proof-side HOL correctness predicate, not
an invoked CLI compiler validation pass. The native naming/convention proofs
and executed regression runner use the exact predicate. This older wrapper
is retained only for explicitly untagged compatibility checks; its encoder
carrier difference is not discharged by the matching bounded test results. -/
def fullInstOkLess {width : Nat} (config : AsmConfig width)
    (program : WordLangProgHOL (BitVec width)) : Bool :=
  fullInstOkLessWith (instOkLess config) (fun operator offset =>
    if operator == .load || operator == .store ||
        operator == .load32 || operator == .store32 then
      asmAddrOffsetOk config offset
    else if operator == .load16 || operator == .store16 then
      asmHwOffsetOk config offset
    else asmByteOffsetOk config offset) program

/-- HOL `wordConvs$inst_arg_convention` (`wordConvsScript.sml:378-386`):
per-instruction calling-convention argument placement.
    Not an exact HOL port: this Lean declaration quantifies `width : Nat`
    without `[NeZero width]`, so `BitVec 0` is admitted, whereas HOL `word`
    dimensions are positive.  The manifest records this mismatch (bead
    flapjack-4ac.6); restore the HOL tag only after correcting the width
    binder and reviewing callers.
    -/
def instArgConvention {width : Nat} : WordLangInst (BitVec width) -> Bool
  | .arith (.addCarry _ _ _ r4) => r4 == 0
  | .arith (.shift _ _ _ (.reg r)) => r == 8
  | .arith (.addOverflow _ _ _ r4) => r4 == 0
  | .arith (.subOverflow _ _ _ r4) => r4 == 0
  | .arith (.longMul r1 r2 r3 r4) =>
      r1 == 6 && r2 == 0 && r3 == 0 && r4 == 4
  | .arith (.longDiv r1 r2 r3 r4 _) =>
      r1 == 0 && r2 == 6 && r3 == 6 && r4 == 0
  | _ => true

/-- Production helper corresponding to HOL `call_arg_convention_def`.
Untagged because its whole-program argument uses the production AST fields
`FiniteMap Nat Unit` and `String`, rather than HOL's `unit spt` and `mlstring`.
`GENLIST f n` is represented by `(List.range n).map f`. -/
def callArgConvention {width : Nat} : WordLangProg (BitVec width) -> Bool
  | .inst value => instArgConvention value
  | .return _ values => values == (List.range values.length).map (fun x => 2 * (x + 1))
  | .raise exception => exception == 2
  | .install ptr len _ _ _ => ptr == 2 && len == 4
  | .ffi _ configuration configurationLength array arrayLength _ =>
      configuration == 2 && configurationLength == 4 &&
        array == 6 && arrayLength == 8
  | .alloc destination _ => destination == 2
  | .storeConsts a b c d _ => a == 0 && b == 2 && c == 4 && d == 6
  | .call returns _ arguments handler =>
      (match returns with
        | none => arguments == (List.range arguments.length).map (fun x => 2 * x)
        | some (returns, _, returnHandler, _, _) =>
            arguments == (List.range arguments.length).map (fun x => 2 * (x + 1)) &&
            returns == (List.range returns.length).map (fun x => 2 * (x + 1)) &&
            callArgConvention returnHandler &&
            (match handler with
              | none => true
              | some (value, handlerProg, _, _) =>
                  value == 2 && callArgConvention handlerProg))
  | .mustTerminate body => callArgConvention body
  | .seq first second => callArgConvention first && callArgConvention second
  | .loop _ body _ => callArgConvention body
  | .ite _ _ _ thenBranch elseBranch =>
      callArgConvention thenBranch && callArgConvention elseBranch
  | _ => true

/-- Exact HOL `wordConvs$call_arg_convention` over the faithful program
carrier. `GENLIST f n` is represented by `(List.range n).map f`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def callArgConventionHOL {width : Nat} : WordLangProgHOL (BitVec width) → Bool
  | .inst value => instArgConvention value
  | .return _ values => values == (List.range values.length).map (fun x => 2 * (x + 1))
  | .raise exception => exception == 2
  | .install ptr len _ _ _ => ptr == 2 && len == 4
  | .ffi _ configuration configurationLength array arrayLength _ =>
      configuration == 2 && configurationLength == 4 &&
        array == 6 && arrayLength == 8
  | .alloc destination _ => destination == 2
  | .storeConsts a b c d _ => a == 0 && b == 2 && c == 4 && d == 6
  | .call returns _ arguments handler =>
      (match returns with
        | none => arguments == (List.range arguments.length).map (fun x => 2 * x)
        | some (returns, _, returnHandler, _, _) =>
            arguments == (List.range arguments.length).map (fun x => 2 * (x + 1)) &&
            returns == (List.range returns.length).map (fun x => 2 * (x + 1)) &&
            callArgConventionHOL returnHandler &&
            (match handler with
              | none => true
              | some (value, handlerProg, _, _) =>
                  value == 2 && callArgConventionHOL handlerProg))
  | .mustTerminate body => callArgConventionHOL body
  | .seq first second => callArgConventionHOL first && callArgConventionHOL second
  | .loop _ body _ => callArgConventionHOL body
  | .ite _ _ _ thenBranch elseBranch =>
      callArgConventionHOL thenBranch && callArgConventionHOL elseBranch
  | _ => true

/-- HOL `ARB : memop`, represented by a fixed representative. Untagged
Flapjack-specific stand-in: `not_created_subprogs` cannot denote HOL's
arbitrary value directly. The `no_alloc`/`no_install`/`no_mt`/`no_share_inst`
specialisations below are invariant to this choice, because each only tests
its own constant. -/
def wordLangArbMemOp : WordMemOp := .load

/-- HOL `wordConvs$not_created_subprogs_def` (`wordConvsScript.sml:536-566`)
over the older function-backed WordLang syntax. The Boolean checker and
choice-independent specializations on `WordLangProgHOL` are in the
`WordConvs.NotCreated` submodule. `P` here is `Prop`-valued (HOL's is
`Bool`): the `Alloc`/`Install` clauses compare against `(LN,LN)` and the
`ShareInst` clause against `ARB`, and `WordLangNumSet` has no decidable
equality. The recursion and every constructor clause match HOL. Untagged:
exact HOL statement shape is not claimed while the value is `Prop`. -/
def notCreatedSubprogs {width : Nat}
    (P : WordLangProg (BitVec width) → Prop) :
    WordLangProg (BitVec width) → Prop
  | .mustTerminate body => P (.mustTerminate .skip) ∧ notCreatedSubprogs P body
  | .seq first second =>
      notCreatedSubprogs P first ∧ notCreatedSubprogs P second
  | .loop _ body _ => notCreatedSubprogs P body
  | .ite _ _ _ thenBranch elseBranch =>
      notCreatedSubprogs P thenBranch ∧ notCreatedSubprogs P elseBranch
  | .call returns destination _arguments handler =>
      P (.call none destination [] none) ∧
        (match returns with
          | none => True
          | some (_, _, body, _, _) => notCreatedSubprogs P body) ∧
        (match handler with
          | none => True
          | some (_, body, label, _) =>
              P (.call none none [] (some (0, .skip, label, 0))) ∧
                notCreatedSubprogs P body)
  | .alloc _ _ => P (.alloc 0 ((FEMPTY : WordLangNumSet), (FEMPTY : WordLangNumSet)))
  | .locValue _ label => P (.locValue 0 label)
  | .shareInst _ _ _ => P (.shareInst wordLangArbMemOp 0 (.var 0))
  | .install _ _ _ _ _ =>
      P (.install 0 0 0 0 ((FEMPTY : WordLangNumSet), (FEMPTY : WordLangNumSet)))
  | _ => True

/-- HOL `wordConvs$no_alloc_subprogs_def`: `not_created_subprogs (λq. q ≠ Alloc 0 (LN,LN))`. -/
def noAllocSubprogs {width : Nat} (program : WordLangProg (BitVec width)) : Prop :=
  notCreatedSubprogs
    (fun q => q ≠ .alloc 0 ((FEMPTY : WordLangNumSet), (FEMPTY : WordLangNumSet)))
    program

/-- HOL `wordConvs$no_install_subprogs_def`. -/
def noInstallSubprogs {width : Nat} (program : WordLangProg (BitVec width)) : Prop :=
  notCreatedSubprogs
    (fun q => q ≠ .install 0 0 0 0 ((FEMPTY : WordLangNumSet), (FEMPTY : WordLangNumSet)))
    program

/-- HOL `wordConvs$no_mt_subprogs_def`. -/
def noMtSubprogs {width : Nat} (program : WordLangProg (BitVec width)) : Prop :=
  notCreatedSubprogs (fun q => q ≠ .mustTerminate .skip) program

/-- HOL `wordConvs$no_share_inst_subprogs_def`. -/
def noShareInstSubprogs {width : Nat} (program : WordLangProg (BitVec width)) : Prop :=
  notCreatedSubprogs
    (fun q => q ≠ .shareInst wordLangArbMemOp 0 (.var 0))
    program

/-- Literal handler-ownership predicate on the HOL-shaped WordLang carrier.
The positive HOL word dimension is represented by `BitVec width`; the tag
records that carrier translation. Nat handler-label equality uses the standard
decidable equality. A Call without a return ignores its handler entirely. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def goodHandlersHOL {width : Nat} [NeZero width] (n : Nat) :
    WordLangProgHOL (BitVec width) -> Bool
  | .call returns _ _ handler =>
      match returns with
      | none => true
      | some (_, _, returnHandler, _, _) =>
          goodHandlersHOL n returnHandler &&
            (match handler with
             | some (_, handlerProg, handlerLabel, _) =>
                 handlerLabel == n && goodHandlersHOL n handlerProg
             | none => true)
  | .seq first second => goodHandlersHOL n first && goodHandlersHOL n second
  | .loop _ body _ => goodHandlersHOL n body
  | .ite _ _ _ thenBranch elseBranch =>
      goodHandlersHOL n thenBranch && goodHandlersHOL n elseBranch
  | .mustTerminate body => goodHandlersHOL n body
  | _ => true

/-- HOL `wordConvsScript$pre_alloc_conventions_def` (`wordConvsScript.sml:425-429`).
It asserts the pre-allocation convention on a backend program: every name in
the program's cut sets is a stack variable (`is_stack_var`), and the call
argument convention holds.  Untagged: it is built from the untagged
`everyStackVar`/`callArgConvention` (the `num_set` sub-terms use the audited
order-insensitive domain model of `docs/NUM-SET-AUDIT.md`). -/
def preAllocConventions {width : Nat} (program : WordLangProg (BitVec width)) : Prop :=
  everyStackVar isStackVar program ∧ callArgConvention program

/-- Literal pre-allocation convention over the faithful Spt-backed program
(`wordConvsScript.sml:425-429`): every cut-set name is a stack variable and the
call argument convention holds. The positive-width word translation is the sole
carrier difference; HOL's `∧` of Booleans is `&&`. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def preAllocConventionsHOL {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) : Bool :=
  everyStackVarHOL isStackVar program && callArgConventionHOL program

/-- HOL `wordConvsScript$post_alloc_conventions_def` (`wordConvsScript.sml:432-437`).
It asserts the post-allocation convention on a backend program: every register
is a physical register (`is_phy_var`), every name in the cut sets is at least
`2 * k`, and the call argument convention holds.  Untagged for the same reason
as `preAllocConventions`. -/
def postAllocConventions {width : Nat} (k : Nat) (program : WordLangProg (BitVec width)) : Prop :=
  everyVar isPhyVar program ∧
    everyStackVar (fun name => decide (name ≥ 2 * k)) program ∧
    callArgConvention program

/-- Literal post-allocation convention over the faithful Spt-backed program.
The positive-width word translation is the sole carrier difference. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def postAllocConventionsHOL {width : Nat} [NeZero width]
    (k : Nat) (program : WordLangProgHOL (BitVec width)) : Bool :=
  everyVarHOL isPhyVar program &&
    (everyStackVarHOL (fun name => decide (name ≥ 2 * k)) program &&
      callArgConventionHOL program)

/-- Exact HOL port of the positive-dimensional word-type declaration
HOL `distinct_tar_reg_def` (`cakeml/compiler/backend/semantics/wordConvsScript.sml`),
stated over the exact positive-dimension `HolInst` carrier (HOL's `'a inst`)
with an explicit `[NeZero width]` binder.  The width-general executed form
above remains untagged; this declaration is the faithful positive-width
counterpart tracked by bead flapjack-4ac.6.1. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def distinctTarRegExact {width : Nat} [NeZero width] : HolInst width → Bool
  | .arith (.binop _ r1 _ ri) => match ri with
      | .reg r => decide (r ≠ r1)
      | .imm _ => true
  | .arith (.shift _ r1 _ ri) => match ri with
      | .reg r => decide (r ≠ r1)
      | .imm _ => true
  | .arith (.addCarry r1 _ r3 r4) => decide (r1 ≠ r3 ∧ r1 ≠ r4)
  | .arith (.addOverflow r1 _ r3 _) => decide (r1 ≠ r3)
  | .arith (.subOverflow r1 _ r3 _) => decide (r1 ≠ r3)
  | _ => true

/-- Exact HOL port of the positive-dimensional word-type declaration
HOL `two_reg_inst_def` (`cakeml/compiler/backend/semantics/wordConvsScript.sml`),
stated over the exact positive-dimension `HolInst` carrier (HOL's `'a inst`)
with an explicit `[NeZero width]` binder.  The width-general executed form
above remains untagged; this declaration is the faithful positive-width
counterpart tracked by bead flapjack-4ac.6.1. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def twoRegInstExact {width : Nat} [NeZero width] : HolInst width → Bool
  | .arith (.binop _ r1 r2 _) => r1 == r2
  | .arith (.shift _ r1 r2 _) => r1 == r2
  | .arith (.addCarry r1 r2 _ _) => r1 == r2
  | .arith (.addOverflow r1 r2 _ _) => r1 == r2
  | .arith (.subOverflow r1 r2 _ _) => r1 == r2
  | _ => true

/-- Exact HOL port of the positive-dimensional word-type declaration
HOL `inst_arg_convention_def` (`cakeml/compiler/backend/semantics/wordConvsScript.sml`),
stated over the exact positive-dimension `HolInst` carrier (HOL's `'a inst`)
with an explicit `[NeZero width]` binder.  The width-general executed form
above remains untagged; this declaration is the faithful positive-width
counterpart tracked by bead flapjack-4ac.6.1. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def instArgConventionExact {width : Nat} [NeZero width] : HolInst width -> Bool
  | .arith (.addCarry _ _ _ r4) => r4 == 0
  | .arith (.shift _ _ _ (.reg r)) => r == 8
  | .arith (.addOverflow _ _ _ r4) => r4 == 0
  | .arith (.subOverflow _ _ _ r4) => r4 == 0
  | .arith (.longMul r1 r2 r3 r4) =>
      r1 == 6 && r2 == 0 && r3 == 0 && r4 == 4
  | .arith (.longDiv r1 r2 r3 r4 _) =>
      r1 == 0 && r2 == 6 && r3 == 6 && r4 == 0
  | _ => true

/-- Exact HOL `wordConvs$inst_ok_less_def`
(`cakeml/compiler/backend/semantics/wordConvsScript.sml:208-264`): the weaker
per-instruction well-formedness predicate used by
`compile_to_word_conventions2`, stated over the exact positive-dimension
`AsmConfigExact`/`HolInst` carriers (HOL's `'a asm_config`/`'a inst`) with an
explicit `[NeZero width]` binder.  The HOL `Mem` branch lists
`Load`/`Store`/`Load16`/`Store16`/`Load32`/`Store32` in its first case, so the
`hw_offset_ok` case is only reachable for the remaining memops.  The
width-general executed form above remains untagged; this declaration is the
faithful positive-width counterpart tracked by bead flapjack-4ac.6.1.2. -/
-- riscv-mi: integer-only specialization of the referenced HOL declaration.

def instOkLessExact {width : Nat} [NeZero width] (config : AsmConfigExact width) :
    HolInst width → Bool
  | .arith (.binop operator _ _ (.imm value)) => config.validImm (.inl operator) value
  | .arith (.shift operator _ _ (.imm value)) =>
      (!(value == 0) || operator == .lsl) && value.toNat < width
  | .arith (.div ..) =>
      config.isa == .armv8 || config.isa == .mips || config.isa == .riscv
  | .arith (.longMul destinationLeft destinationRight sourceLeft sourceRight) =>
      (!(config.isa == .armv7) || !(destinationLeft == destinationRight)) &&
        (!(config.isa == .armv8 || config.isa == .riscv || config.isa == .ag32) ||
          (!(destinationLeft == sourceLeft) && !(destinationLeft == sourceRight)))
  | .arith (.longDiv ..) => config.isa == .x86_64
  | .arith (.addCarry destination _ sourceLeft sourceRight) =>
      (!(config.isa == .mips || config.isa == .riscv) ||
        (!(destination == sourceLeft) && !(destination == sourceRight)))
  | .arith (.addOverflow destination _ sourceLeft _) =>
      (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))
  | .arith (.subOverflow destination _ sourceLeft _) =>
      (!(config.isa == .mips || config.isa == .riscv) || !(destination == sourceLeft))
  | .mem operator _ (.addr _ offset) =>
      (if operator == .load || operator == .store || operator == .load16 ||
          operator == .store16 || operator == .load32 || operator == .store32 then
        asmAddrOffsetOkExact config offset
       else if operator == .load16 || operator == .store16 then
        asmHwOffsetOkExact config offset
       else
        asmByteOffsetOkExact config offset)
  | _ => true

end Flapjack
