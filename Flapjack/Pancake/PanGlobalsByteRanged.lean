module

public import Flapjack.Pancake.PanGlobals
public import Flapjack.Pancake.PanGlobals.DeclarationProgramRoute
public import Flapjack.Pancake.PanGlobals.CompileTopExact
public import Flapjack.Pancake.PanLang.Decl
public import Flapjack.Pancake.PanLang.Prog

@[expose] public section

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

def GlobalContextShapesByteRanged [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) : Prop :=
  ∀ name shape address,
    lookupInfo name context.globals = some (shape, address) → ShapeByteRanged shape

private theorem fpermName_byteRanged [DecidableEq String]
    (source target name : String)
    (hsource : NameRanged source) (htarget : NameRanged target)
    (hname : NameRanged name) :
    NameRanged (fpermName source target name) := by
  by_cases hsourceName : source = name
  · simpa [fpermName, hsourceName] using htarget
  · by_cases htargetName : target = name
    · simpa [fpermName, hsourceName, htargetName] using hsource
    · simpa [fpermName, hsourceName, htargetName] using hname

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
    exact fpermName_byteRanged source target function
      hsource htarget hinput.1
  case case13 function arguments hinput =>
    exact fpermName_byteRanged source target function
      hsource htarget hinput.1
  case case14 function arguments exception handlerVar handler ih hinput =>
    exact ⟨fpermName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1⟩
  case case15 function arguments name hinput =>
    exact ⟨fpermName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2⟩
  case case16 function arguments name exception handlerVar handler ih hinput =>
    exact ⟨fpermName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1, hinput.2.2.2.2.1⟩
  case case17 function arguments name shape address hlookup hinput =>
    exact ⟨fpermName_byteRanged source target function
        hsource htarget hinput.1, hinput.2.2⟩
  case case18 function arguments name hlookup hinput =>
    exact ⟨fpermName_byteRanged source target function
        hsource htarget hinput.1, hinput.2.2⟩
  case case19 function arguments name exception handlerVar handler shape address hlookup ih hinput =>
    exact ⟨fpermName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1, hinput.2.2.2.2.1⟩
  case case20 function arguments name exception handlerVar handler hlookup ih hinput =>
    exact ⟨fpermName_byteRanged source target function
        hsource htarget hinput.1,
      hinput.2.2.1, hinput.2.2.2.1, hinput.2.2.2.2.1⟩
  case case21 name shape function arguments body ih hinput =>
    exact ⟨hinput.1,
      fpermName_byteRanged source target function
        hsource htarget hinput.2.2.1⟩
  case case22 function configuration configurationLength array arrayLength hinput => exact hinput.1
  case case23 exception value hinput => exact hinput.1
  case case25 size name address hinput => exact hinput.1
  case case26 size name address globalAddress hlookup hinput => exact hinput.1
  case case27 size name address hlookup hinput => exact hinput.1

end Flapjack
