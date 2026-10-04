import Flapjack.Pancake.PanToWord.ProductionPrefix
import Flapjack.Pancake.PanToTarget
import Mathlib.Data.List.TakeDrop

/-! Source-entry codec contracts for the anonymous first LET of the original
whole compiler. Reuse the reviewed `mainFirstHOL` infrastructure; there is no
independent HOL declaration to tag for this extracted operation. -/
namespace Flapjack.Pancake.PanToTarget
open Flapjack Pancake.PanLang Basis.Pure.MlString

private theorem mainName_codec (name : String) (ranged : NameRanged name) :
    ofString name = ofString "main" ↔ name = "main" := by
  constructor
  · intro encoded
    have decoded := congrArg toStringOfBytes encoded
    rw [toStringOfBytes_ofString_of_bytes name ranged] at decoded
    exact decoded
  · intro same
    rw [same]

/-- Native first-match split keeps every original source declaration field.
    The real source byte invariant supplies the comparison codec premise. -/
theorem splitStart_encode {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ d ∈ declarations, DeclByteRanged d) :
    ((panTargetSplitStart "main" declarations).1.map declToHOL,
      (panTargetSplitStart "main" declarations).2.map declToHOL) =
    (declarations.map declToHOL).span (fun declaration =>
      match declaration with
      | .function entry => decide (entry.name ≠ ofString "main")
      | _ => true) := by
  induction declarations with
  | nil => rfl
  | cons head tail ih =>
      have tailSource : ∀ d ∈ tail, DeclByteRanged d :=
        fun d member => source d (List.mem_cons_of_mem head member)
      have headSource := source head (List.mem_cons_self ..)
      have splitTail := ih tailSource
      cases head with
      | function entry =>
          have ranged : NameRanged entry.name := headSource.1
          have nameCodec := mainName_codec entry.name ranged
          by_cases same : entry.name = "main"
          all_goals simp_all [panTargetSplitStart, List.map_cons,
            declToHOL, funDeclToHOL]
      | decl shape name value =>
          simp_all [panTargetSplitStart, declToHOL]
      | exnDecl name shape =>
          simp_all [panTargetSplitStart, declToHOL]
      | name struct fields =>
          simp_all [panTargetSplitStart, declToHOL]

private theorem splitStart_any {width : Nat}
    (declarations : List (Decl (BitVec width))) :
    declarations.any (fun declaration => match declaration with
      | .function function => function.name == "main"
      | _ => false) = !(panTargetSplitStart "main" declarations).2.isEmpty := by
  induction declarations with
  | nil => rfl
  | cons head tail ih =>
      cases head with
      | function entry =>
          by_cases same : entry.name = "main"
          all_goals simp_all [panTargetSplitStart]
      | decl shape name value => simp_all [panTargetSplitStart]
      | exnDecl name shape => simp_all [panTargetSplitStart]
      | name struct fields => simp_all [panTargetSplitStart]

private theorem defaultMain_eq {width : Nat}
    (declarations : List (Decl (BitVec width))) :
    panTargetDeclarationsWithDefaultMain declarations =
      if declarations.any (fun declaration => match declaration with
        | .function function => function.name == "main"
        | _ => false) then declarations
      else match declarations with
        | [] => []
        | _ => .function ⟨"main", false, false, [], .return (.const 0), .one⟩ :: declarations := by
  unfold panTargetDeclarationsWithDefaultMain
  congr 2
  · congr 1
    funext declaration
    cases declaration <;> rfl
  · cases declarations <;> rfl

/-- The actual caller's default insertion and first-match movement encode to
    the complete original anonymous first LET, including empty/missing and
    duplicate-main inputs. No distinct-name hypothesis is introduced. -/
theorem sourceEntry_encode {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ d ∈ declarations, DeclByteRanged d) :
    (panTargetMoveStartToFront "main"
      (panTargetDeclarationsWithDefaultMain declarations)).map declToHOL =
      mainFirstHOL (declarations.map declToHOL) := by
  unfold mainFirstHOL
  erw [← splitStart_encode declarations source]
  have partition := panTargetSplitStart_append "main" declarations
  have present := splitStart_any declarations
  cases splitEq : panTargetSplitStart "main" declarations with
  | mk before after =>
      rw [splitEq] at partition present
      cases before <;> cases after
      all_goals simp only [List.isEmpty, Bool.not_true,
        Bool.not_false, List.append_nil, List.nil_append] at present partition
      all_goals rw [defaultMain_eq]
      all_goals erw [present]
      all_goals simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals simp_all [panTargetMoveStartToFront, panTargetSplitStart,
        declToHOL, funDeclToHOL]
      all_goals rw [← partition]
      all_goals simp [panTargetSplitStart, declToHOL, funDeclToHOL,
        progToHOL, expToHOL, shapeToHOL]

/-- Source-input producer using the same default-main preparation as the
parser-backed actual callers. Parsing/static-check errors and downstream
assembly remain separate; this prefix adds no additional defaults. -/
def compileSourceWordNative? {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ d ∈ declarations, DeclByteRanged d) :
    Option (List (Nat × Nat × WordLangProgHOL (BitVec width))) :=
  compileFlapjackFrontendWordNative? (panTargetDeclarationsWithDefaultMain declarations)
    (panTargetDeclarationsWithDefaultMain_byteRanged declarations source)

/-- Complete original source preparation followed by all six original passes.
The source-byte invariant alone derives every codec and producer premise,
including missing/empty/duplicate-main source lists. -/
theorem compileSourceWordNative_original {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (source : ∀ d ∈ declarations, DeclByteRanged d) :
    compileSourceWordNative? declarations source =
      some (panToWordCompileProgHOL .riscv (mainFirstHOL (declarations.map declToHOL))) := by
  unfold compileSourceWordNative?
  rw [compileFlapjackFrontendWordNative_original, sourceEntry_encode declarations source]

end Flapjack.Pancake.PanToTarget
