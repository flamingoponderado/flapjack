import Flapjack.Pancake.PanGlobals
import Flapjack.Pancake.PanGlobals.DeclarationProgramRoute
import Flapjack.Pancake.PanGlobals.CompileTopExact
import Flapjack.Pancake.PanLang.Decl
import Flapjack.Pancake.PanLang.Prog

/-!
Byte-range preservation facts for the executed PanGlobals pass.

The exact DeclHOL compiler boundary can only be used after the production
String declarations have been shown to round-trip through DeclHOL. The parser
provides that invariant, but the final global pass also rewrites programs and
can synthesize names. These lemmas establish the pass-local facts needed to
prove the invariant at the actual compiler boundary.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString (toStringOfBytes)

private theorem nameRanged_append {left right : String}
    (hleft : NameRanged left) (hright : NameRanged right) :
    NameRanged (left ++ right) := by
  intro character hcharacter
  rw [String.toList_append, List.mem_append] at hcharacter
  rcases hcharacter with h | h
  · exact hleft character h
  · exact hright character h

private theorem globalApostrophes_nameRanged (count : Nat) :
    NameRanged (globalApostrophes count) := by
  induction count with
  | zero => simp [globalApostrophes, NameRanged]
  | succ count ih =>
      apply nameRanged_append
      · decide
      · simpa [globalApostrophes] using ih

private theorem freshNameHOL_literal_byteRanged (seed : String)
    (hseed : NameRanged seed) (names : List String) :
    NameRanged (freshNameHOL seed names) :=
  holMlStringWitness_freshNameHOL seed names hseed

/-- Every shape found in a global compilation context is byte-ranged. -/
def GlobalContextShapesByteRanged [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) : Prop :=
  ∀ name shape address,
    lookupInfo name context.globals = some (shape, address) → ShapeByteRanged shape

private theorem globalContextShapesByteRanged_update [BEq String]
    {width : Nat} (context : GlobalPassContext (BitVec width))
    (name : String) (shape : Shape) (address : BitVec width)
    (hcontext : GlobalContextShapesByteRanged context)
    (hshape : ShapeByteRanged shape) :
    GlobalContextShapesByteRanged
      { context with globals := (name, (shape, address)) :: context.globals } := by
  intro key foundShape foundAddress hlookup
  by_cases hname : name == key
  · simp [lookupInfo, hname] at hlookup
    cases hlookup.1
    exact hshape
  · simp [lookupInfo, hname] at hlookup
    exact hcontext key foundShape foundAddress hlookup

private theorem globalRenameFunctionName_byteRanged [DecidableEq String]
    (source target name : String)
    (hsource : NameRanged source) (htarget : NameRanged target)
    (hname : NameRanged name) :
    NameRanged (globalRenameFunctionName source target name) := by
  by_cases hsourceName : source = name
  · simpa [globalRenameFunctionName, fpermName, hsourceName] using htarget
  · by_cases htargetName : target = name
    · simpa [globalRenameFunctionName, fpermName, hsourceName, htargetName] using hsource
    · simpa [globalRenameFunctionName, fpermName, hsourceName, htargetName] using hname

private theorem globalDeclsFilter_mem_source {α : Type} {predicate : Decl α → Bool}
    {declarations : List (Decl α)} {declaration : Decl α}
    (hmem : declaration ∈ globalDeclsFilter predicate declarations) :
    declaration ∈ declarations := by
  induction declarations with
  | nil => simp [globalDeclsFilter] at hmem
  | cons head tail ih =>
      simp only [globalDeclsFilter] at hmem
      split at hmem
      · simp only [List.mem_cons] at hmem
        rcases hmem with heq | hmem
        · subst declaration
          simp
        · exact List.mem_cons_of_mem head (ih hmem)
      · exact List.mem_cons_of_mem head (ih hmem)

private theorem globalRenameProg_byteRanged {width : Nat} [BEq String]
    [Add (BitVec width)] [Mul (BitVec width)]
    (source target : String) (hsource : NameRanged source)
    (htarget : NameRanged target) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      ProgByteRanged (globalRenameProg source target program) := by
  let inductionContext : GlobalPassContext (BitVec width) :=
    { globals := [], globalsSize := 0, maxGlobalsSize := 0,
      bytesInWord := 0, fromNat := fun _ => 0 }
  apply globalCompileProg.induct inductionContext
    (motive := fun program =>
      ProgByteRanged program → ProgByteRanged (globalRenameProg source target program))
  all_goals
    intros
    simp_all [globalRenameProg, ProgByteRanged]
  case case1 name shape value body ih hinput => exact hinput.1
  case case2 name value shape address hlookup hinput => exact hinput.1
  case case3 name value hlookup hinput => exact hinput.1
  case case4 name value hinput => exact hinput.1
  case case5 name operator arguments hinput => exact hinput.1
  case case12 function arguments hinput =>
    exact globalRenameFunctionName_byteRanged source target function
      hsource htarget hinput.1
  case case13 function arguments hinput =>
    exact globalRenameFunctionName_byteRanged source target function
      hsource htarget hinput.1
  case case14 function arguments exception handlerVar handler ih hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1⟩
  case case15 function arguments name hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2⟩
  case case16 function arguments name exception handlerVar handler ih hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1, hinput.2.2.2.2.1⟩
  case case17 function arguments name shape address hlookup hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1, hinput.2.2⟩
  case case18 function arguments name hlookup hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1, hinput.2.2⟩
  case case19 function arguments name exception handlerVar handler shape address hlookup ih hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1, hinput.2.2.2.2.1⟩
  case case20 function arguments name exception handlerVar handler hlookup ih hinput =>
    exact ⟨globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1, hinput.2.2.2.2.1⟩
  case case21 name shape function arguments body ih hinput =>
    exact ⟨hinput.1,
      globalRenameFunctionName_byteRanged source target function
        hsource htarget hinput.2.2.1⟩
  case case22 function configuration configurationLength array arrayLength hinput => exact hinput.1
  case case23 exception value hinput => exact hinput.1
  case case25 size name address hinput => exact hinput.1
  case case26 size name address globalAddress hlookup hinput => exact hinput.1
  case case27 size name address hlookup hinput => exact hinput.1

private theorem globalRenameDecls_byteRanged {width : Nat} [BEq String]
    [Add (BitVec width)] [Mul (BitVec width)]
    (source target : String) (hsource : NameRanged source)
    (htarget : NameRanged target) :
    ∀ declarations : List (Decl (BitVec width)),
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
      ∀ declaration ∈ globalRenameDecls source target declarations,
        DeclByteRanged declaration := by
  intro declarations
  induction declarations with
  | nil => simp [globalRenameDecls]
  | cons declaration declarations ih =>
      intro hinput output houtput
      cases declaration with
      | function function =>
          simp only [globalRenameDecls, List.mem_cons] at houtput
          rcases houtput with heq | houtput
          · cases heq
            have hfunction := hinput (.function function) (by simp)
            simp only [DeclByteRanged, FunDeclByteRanged] at hfunction
            exact ⟨globalRenameFunctionName_byteRanged source target function.name
                hsource htarget hfunction.1,
              hfunction.2.1,
              globalRenameProg_byteRanged source target hsource htarget
                function.body hfunction.2.2.1,
              hfunction.2.2.2⟩
          · exact ih (by
              intro item hitem
              exact hinput item (by simp [hitem])) output houtput
      | decl shape name value =>
          simp only [globalRenameDecls, List.mem_cons] at houtput
          rcases houtput with heq | houtput
          · cases heq
            exact hinput (.decl shape name value) (by simp)
          · exact ih (by
              intro item hitem
              exact hinput item (by simp [hitem])) output houtput
      | exnDecl exception shape =>
          simp only [globalRenameDecls, List.mem_cons] at houtput
          rcases houtput with heq | houtput
          · cases heq
            exact hinput (.exnDecl exception shape) (by simp)
          · exact ih (by
              intro item hitem
              exact hinput item (by simp [hitem])) output houtput
      | name struct fields =>
          simp only [globalRenameDecls, List.mem_cons] at houtput
          rcases houtput with heq | houtput
          · cases heq
            exact hinput (.name struct fields) (by simp)
          · exact ih (by
              intro item hitem
              exact hinput item (by simp [hitem])) output houtput

private theorem globalResortDecls_byteRanged {width : Nat}
    (declarations : List (Decl (BitVec width)))
    (hinput : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    ∀ declaration ∈ globalResortDecls declarations, DeclByteRanged declaration := by
  intro declaration houtput
  unfold globalResortDecls at houtput
  rcases List.mem_append.mp houtput with hleft | hfunction
  · rcases List.mem_append.mp hleft with hleft | hglobal
    · rcases List.mem_append.mp hleft with hname | hexn
      · exact hinput declaration (globalDeclsFilter_mem_source hname)
      · exact hinput declaration (globalDeclsFilter_mem_source hexn)
    · exact hinput declaration (globalDeclsFilter_mem_source hglobal)
  · exact hinput declaration (globalDeclsFilter_mem_source hfunction)

/-- The parser-proved compiler route can encode its production declarations
    into the reviewed HOL carrier and decode them again without changing them.
    This is the roundtrip needed to route the PanGlobals transforms through
    their tagged HOL definitions; it is available only on the byte-ranged
    path because production identifiers and shapes are String-backed. -/
private theorem map_declOfHOL_declToHOL_byteRanged {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width)))
    (hinput : ∀ declaration ∈ declarations, DeclByteRanged declaration) :
    (declarations.map declToHOL).map declOfHOL = declarations := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations ih =>
      have hhead := hinput declaration (by simp)
      have htail : ∀ item ∈ declarations, DeclByteRanged item := by
        intro item hmem
        exact hinput item (by simp [hmem])
      simp only [List.map_cons]
      rw [declOfHOL_declToHOL declaration hhead, ih htail]

/-- Parser-path implementation of the declaration regrouping that executes
    the exact `resortDeclsHOL` port and decodes its result. -/
private def globalResortDeclsViaHOL {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) : List (Decl (BitVec width)) :=
  (resortDeclsHOL (declarations.map declToHOL)).map declOfHOL

/-- Parser-path implementation of the generated `main` name that executes
    the exact `newMainNameHOL` port over `MlString`. -/
private def globalNewMainNameViaHOL {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) : FunName :=
  toStringOfBytes (newMainNameHOL (declarations.map declToHOL))

/-- Parser-path shape projection through the exact `decShapesHOL` port. -/
private def globalDeclShapesViaHOL {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) : List Shape :=
  (decShapesHOL (declarations.map declToHOL)).map shapeOfHOL

private theorem globalFindFunction_byteRanged {width : Nat} [BEq String]
    (name : String) (declarations : List (Decl (BitVec width)))
    (hinput : ∀ declaration ∈ declarations, DeclByteRanged declaration)
    (function : FunDecl (BitVec width))
    (hfind : globalFindFunction name declarations = some function) :
    FunDeclByteRanged function := by
  induction declarations with
  | nil => simp [globalFindFunction] at hfind
  | cons declaration declarations ih =>
      cases declaration with
      | function fd =>
          by_cases hname : fd.name == name
          · simp [globalFindFunction, hname] at hfind
            have heq : fd = function := hfind
            subst function
            exact hinput (.function fd) (by simp)
          · simp [globalFindFunction, hname] at hfind
            exact ih (fun d hd => hinput d (by simp [hd])) hfind
      | decl shape name' value =>
          simp only [globalFindFunction] at hfind
          exact ih (fun d hd => hinput d (by simp [hd])) hfind
      | exnDecl exception shape =>
          simp only [globalFindFunction] at hfind
          exact ih (fun d hd => hinput d (by simp [hd])) hfind
      | name struct fields =>
          simp only [globalFindFunction] at hfind
          exact ih (fun d hd => hinput d (by simp [hd])) hfind

private theorem nestedSeq_byteRanged {width : Nat}
    (programs : List (Prog (BitVec width)))
    (hprograms : ∀ program ∈ programs, ProgByteRanged program) :
    ProgByteRanged (nestedSeq programs) := by
  induction programs with
  | nil => simp [nestedSeq, ProgByteRanged]
  | cons head tail ih =>
      simp only [nestedSeq, ProgByteRanged]
      exact ⟨hprograms head (by simp), ih (by
        intro program hmem
        exact hprograms program (by simp [hmem]))⟩

private theorem globalCompileTopParameters_byteRanged {width : Nat}
    (parameters : List (String × Shape))
    (hparameters : ListParamByteRanged parameters) :
    ∀ expression : Exp (BitVec width),
      expression ∈ parameters.map
        (fun parameter : String × Shape => Exp.var .local parameter.1) →
      ExpByteRanged expression := by
  intro expression hmem
  rcases List.mem_map.mp hmem with ⟨parameter, hparameter, heq⟩
  cases heq
  exact (hparameters parameter hparameter).1

end Flapjack
