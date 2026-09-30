import Flapjack.Pancake.PanGlobals.CompileExpExact
import Flapjack.Pancake.PanLang.Exp

/-!
Finite-support routing infrastructure between the executed PanGlobals
`compileExpCake` chain and the reviewed exact `compileExpExactHOL`.

`pan_globals$compile_exp_def` is ported at the exact carrier in
`Flapjack/Pancake/PanGlobals/CompileExpExact.lean`, but the executed
`compileDecsCake`/`compileProgCake`/`compileExpCake` chain still computes the
production String-backed function.  The production `GlobalPassContext.globals`
is an association list (`InfoMap`), so it does carry finite support; the adapter
`PanGlobalsContextExact.ofPass` below reconstructs the exact finite-support
context from it, decoding production `String` names through `NameRanged` and
shapes through `shapeToHOL`.

The kernel-checked equality `compileExpCake_ofPass_eq` then routes the executed
expression compiler on that production context through the reviewed
`compileExpExactHOL` under the byte-range premise the parser supplies:
`compileExpCake (cakeContextOfPass context) e = expOfHOL (compileExpExactHOL
(ofPass context) (expToHOL e))`.

This is Flapjack routing infrastructure, not a HOL declaration, so nothing here
carries an `@[hol]` tag.  The legacy `compileDecsCake`/`compileProgCake`/
`compileExpCake` bodies are unchanged and still compute the production
String-backed function directly; they cannot be rewritten in place because they
are total over arbitrary `String` and `CakeContext.globals` erases the
finite-support structure (`α → Option β`) the exact `HolFiniteMapExact` field
requires.

The byte-ranged executable path added below *is* textual routing, however:
`compileExpRouteCake` (this module) has body
`expOfHOL (compileExpExactHOL (ofPass context) (expToHOL e))`, and
`compileProgCakeOfExact`/`compileDecsCakeOfExact` thread `GlobalPassContext`
through the executed decl/prog compiler, with kernel-checked equalities
`compileProgCakeOfExact_eq` (under `ProgByteRanged`) and
`compileDecsCakeOfExact_eq` (under `IsCakeCanonical` + `DeclByteRanged`) to the
production functions.  The executed `globalCompileTopForStartSomeCakeOfExact`
(`PanGlobalsByteRanged.lean`) and `Pipeline.lean:654` run these routed siblings
on the parser-proof (byte-range) branch, so that branch textually calls the
tagged `compileExpExactHOL`.

The fallback branch (input not proved byte-ranged) remains the legacy
production functions; this is not a claim that all arbitrary `String` inputs
are routed. -/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
  (MlS ShapeHOL ExpHOL expToHOL expOfHOL varExpHOL ExpByteRanged ListExpByteRanged NameRanged
    shapeToHOL shapeOfHOL ShapeByteRanged ProgHOL progToHOL progOfHOL ProgByteRanged
    DeclByteRanged FunDeclByteRanged)

/-- `lookupInfo` returns `some` only for a key that occurs in the association
    list.  Used to build the finite-support witness of the exact context from
    the production `InfoMap`.  Flapjack infrastructure (untagged). -/
theorem lookupInfo_exists_of_ne_none [BEq String] [LawfulBEq String] {α : Type}
    (key : String) : (entries : List (String × α)) →
      lookupInfo key entries ≠ none → ∃ entry ∈ entries, entry.1 = key := by
  intro entries
  induction entries with
  | nil => intro h; simp [lookupInfo] at h
  | cons head tail ih =>
      intro h
      obtain ⟨candidate, value⟩ := head
      simp only [lookupInfo] at h
      split at h
      · rename_i hcond
        exact ⟨(candidate, value), by simp, beq_iff_eq.mp hcond⟩
      · obtain ⟨entry, hmem, hkey⟩ := ih h
        exact ⟨entry, by simp [hmem], hkey⟩

/-- The value `lookupInfo` returns belongs to the association list (after
    re-associating its key).  Flapjack infrastructure (untagged). -/
theorem lookupInfo_eq_some_mem [BEq String] [LawfulBEq String] {α : Type}
    (key : String) : (entries : List (String × α)) → {value : α} →
      lookupInfo key entries = some value → (key, value) ∈ entries := by
  intro entries
  induction entries with
  | nil => intro value h; simp [lookupInfo] at h
  | cons head tail ih =>
      intro value h
      obtain ⟨candidate, v⟩ := head
      simp only [lookupInfo] at h
      split at h
      · rename_i hcond
        have hv : v = value := Option.some.inj h
        subst hv
        have hce : candidate = key := beq_iff_eq.mp hcond
        subst hce
        simp
      · exact List.mem_cons_of_mem _ (ih h)

namespace PanGlobalsContextExact

/-- Finite-support exact `pan_globals` context induced by the production
    `GlobalPassContext` association list.  Lookup decodes the `MlS` key through
    `toStringOfBytes` and maps each payload shape with `shapeToHOL`; the finite
    support is the image under `ofString` of the production `InfoMap` keys.
    Flapjack adapter infrastructure (untagged), the production-to-exact
    direction of `cakeContextOfExact`. -/
def ofPass [BEq String] [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) : PanGlobalsContextExact width where
  globals :=
    { lookup := fun name =>
        (lookupInfo (toStringOfBytes name) context.globals).map
          (fun entry => (shapeToHOL entry.1, entry.2))
      finiteSupport := by
        refine ⟨context.globals.map (fun entry => ofString entry.1), ?_⟩
        intro name hlookup
        have hne : lookupInfo (toStringOfBytes name) context.globals ≠ none := by
          intro hnone
          rw [hnone, Option.map_none] at hlookup
          exact hlookup rfl
        obtain ⟨entry, hmem, hkey⟩ :=
          lookupInfo_exists_of_ne_none (toStringOfBytes name) context.globals hne
        rw [List.mem_map]
        exact ⟨entry, hmem, by rw [hkey, ofString_toStringOfBytes]⟩ }
  globalsSize := context.globalsSize
  maxGlobalsSize := context.maxGlobalsSize

/-- Lookup of `ofPass` exposes the production `InfoMap` search and the shape
    encoding.  Flapjack infrastructure (untagged). -/
@[simp] theorem ofPass_globals_lookup [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width] (context : GlobalPassContext (BitVec width)) (name : MlS) :
    (ofPass context).globals.lookup name =
      (lookupInfo (toStringOfBytes name) context.globals).map
        (fun entry => (shapeToHOL entry.1, entry.2)) := rfl

end PanGlobalsContextExact

open PanGlobalsContextExact

/-- Looking up a key in the association list returns an entry whose shape is in
    the list; on a byte-ranged list the shape decode of its `shapeToHOL` image
    is the identity.  Flapjack infrastructure (untagged). -/
theorem lookupInfo_decode_shape_eq [BEq String] [LawfulBEq String] {width : Nat}
    (key : String) (entries : List (String × (Shape × BitVec width)))
    (hshapes : ∀ entry ∈ entries, ShapeByteRanged entry.2.1) :
    (lookupInfo key entries).map (fun entry => (shapeOfHOL (shapeToHOL entry.1), entry.2))
      = lookupInfo key entries := by
  cases h : lookupInfo key entries with
  | none => simp only [Option.map_none]
  | some entry =>
      obtain ⟨shape, address⟩ := entry
      have hmem : (key, (shape, address)) ∈ entries := lookupInfo_eq_some_mem key entries h
      have hshape : ShapeByteRanged shape := hshapes (key, (shape, address)) hmem
      simp only [Option.map_some]
      rw [Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL shape hshape]

/-- The exact context extracted from a production `GlobalPassContext` decodes,
    on byte-ranged keys, to the same production `CakeContext` produced by
    `cakeContextOfPass`, provided the stored shapes are byte-ranged.  Flapjack
    routing infrastructure (untagged). -/
theorem cakeContextOfExact_ofPass_globals [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width] (context : GlobalPassContext (BitVec width))
    (hshapes : ∀ entry ∈ context.globals, ShapeByteRanged entry.2.1)
    (key : String) (hkey : NameRanged key) :
    (cakeContextOfExact (ofPass context)).globals key
      = (cakeContextOfPass context).globals key := by
  show ((lookupInfo (toStringOfBytes (ofString key)) context.globals).map
      (fun entry => (shapeToHOL entry.1, entry.2))).map
        (fun entry => (shapeOfHOL entry.1, entry.2))
      = lookupInfo key context.globals
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes key hkey,
    Option.map_map]
  exact lookupInfo_decode_shape_eq key context.globals hshapes

/-- The executed `compileExpCake` is insensitive to replacing the
    `cakeContextOfPass` view of a byte-ranged production context by the exact
    `cakeContextOfExact (ofPass context)` view.  Flapjack routing infrastructure
    (untagged). -/
theorem compileExpCake_cakeContextOfExact_ofPass [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width))
    (hshapes : ∀ entry ∈ context.globals, ShapeByteRanged entry.2.1) :
    (expression : Exp (BitVec width)) → ExpByteRanged expression →
      compileExpCake (cakeContextOfExact (ofPass context)) expression
        = compileExpCake (cakeContextOfPass context) expression :=
  Flapjack.Exp.rec
    (motive_1 := fun expression =>
      ExpByteRanged expression →
        compileExpCake (cakeContextOfExact (ofPass context)) expression
          = compileExpCake (cakeContextOfPass context) expression)
    (motive_2 := fun expressions =>
      ListExpByteRanged expressions →
        compileExpCake.compileExpCakeList (cakeContextOfExact (ofPass context)) expressions
          = compileExpCake.compileExpCakeList (cakeContextOfPass context) expressions)
    (motive_3 := fun _ => True)
    (motive_4 := fun _ => True)
    (fun _value _ => by simp only [compileExpCake])
    (fun kind name hname => by
      cases kind with
      | «local» => simp only [compileExpCake]
      | global =>
          simp only [compileExpCake, FLOOKUP]
          rw [cakeContextOfExact_ofPass_globals context hshapes name hname])
    (fun expressions ih hexpressions => by
      simp only [compileExpCake]
      rw [ih hexpressions])
    (fun index value ih hvalue => by
      simp only [compileExpCake]
      rw [ih hvalue])
    (fun _name _fields _ih _ => by simp only [compileExpCake])
    (fun _name _value _ih _ => by simp only [compileExpCake])
    (fun _shape address ih hload => by
      obtain ⟨_hshape, haddress⟩ := hload
      simp only [compileExpCake]
      rw [ih haddress])
    (fun address ih haddress => by
      simp only [compileExpCake]
      rw [ih haddress])
    (fun address ih haddress => by
      simp only [compileExpCake]
      rw [ih haddress])
    (fun _operator args ih hargs => by
      simp only [compileExpCake]
      rw [ih hargs])
    (fun _operator args ih hargs => by
      simp only [compileExpCake]
      rw [ih hargs])
    (fun _operator left right ihl ihr hcmp => by
      obtain ⟨hl, hr⟩ := hcmp
      simp only [compileExpCake]
      rw [ihl hl, ihr hr])
    (fun _operator left right ihl ihr hshift => by
      obtain ⟨hl, hr⟩ := hshift
      simp only [compileExpCake]
      rw [ihl hl, ihr hr])
    (fun _ => by simp only [compileExpCake])
    (fun _ => by
      simp only [compileExpCake, PanGlobalsContextExact.cakeContextOfExact, ofPass,
        cakeContextOfPass])
    (fun _ => by simp only [compileExpCake])
    (fun _ => by simp only [compileExpCake.compileExpCakeList])
    (fun head tail ihHead ihTail hlist => by
      obtain ⟨hhead, htail⟩ := hlist
      simp only [compileExpCake.compileExpCakeList]
      rw [ihHead hhead, ihTail htail])
    True.intro
    (fun _ _ _ _ => True.intro)
    (fun _ _ _ => True.intro)

/-- Routing equality: on the production `cakeContextOfPass` view of a byte-ranged
    `GlobalPassContext`, the executed `compileExpCake` computes exactly the
    `expOfHOL` image of the reviewed exact `compileExpExactHOL` run on the exact
    finite-support context `ofPass context`.  This is Flapjack routing
    infrastructure (untagged); it does not change the production function body,
    which remains total over arbitrary `String`. -/
theorem compileExpCake_ofPass_eq [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width))
    (hshapes : ∀ entry ∈ context.globals, ShapeByteRanged entry.2.1)
    (expression : Exp (BitVec width)) (hranged : ExpByteRanged expression) :
    compileExpCake (cakeContextOfPass context) expression
      = expOfHOL (compileExpExactHOL (ofPass context) (expToHOL expression)) := by
  rw [← compileExpCake_cakeContextOfExact (ofPass context) expression hranged]
  exact (compileExpCake_cakeContextOfExact_ofPass context hshapes expression hranged).symm

/-! ### Routing the executed decl/prog compilers through `compileExpExactHOL`

The production `compileDecsCake`/`compileProgCake` bodies remain unchanged.
`compileDecsCakeOfExact`/`compileProgCakeOfExact` are routed siblings that thread
the production `GlobalPassContext` (as `globalCompileDecsThreaded` does) and
replace every expression call site with `compileExpRouteCake`, whose body
textually invokes the reviewed `compileExpExactHOL`.  The kernel-checked
equalities below show the routed siblings compute exactly the production output
on byte-ranged input, so rewiring the executed entry point keeps the observable
compiler result.  Flapjack routing infrastructure (untagged). -/

/-- Every stored shape in a production association list is byte-ranged: the
    strong, list-indexed companion of `GlobalContextShapesByteRanged`, needed by
    `compileExpCake_ofPass_eq`.  Flapjack routing infrastructure (untagged). -/
def GlobalContextListShapesByteRanged [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) : Prop :=
  ∀ entry ∈ context.globals, ShapeByteRanged entry.2.1

/-- Prepending a byte-ranged shape preserves the list-indexed shape invariant.
    Flapjack routing infrastructure (untagged). -/
theorem globalContextListShapesByteRanged_update [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) (name : String) (shape : Shape)
    (address : BitVec width)
    (hcontext : GlobalContextListShapesByteRanged context)
    (hshape : ShapeByteRanged shape) :
    GlobalContextListShapesByteRanged
      { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address } := by
  intro entry hmem
  rw [List.mem_cons] at hmem
  rcases hmem with hhead | htail
  · subst hhead
    exact hshape
  · exact hcontext entry htail

/-- The routed expression compiler: decode the production expression to the exact
    carrier, run the reviewed `compileExpExactHOL` on the finite-support context
    `ofPass context`, and encode the result back.  Flapjack routing
    infrastructure (untagged). -/
def compileExpRouteCake [BEq String] [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (expression : Exp (BitVec width)) :
    Exp (BitVec width) :=
  expOfHOL (compileExpExactHOL (ofPass context) (expToHOL expression))

/-- Use the tagged HOL `var_exp` for the parser-backed exact compiler's
    generated-name scan whenever the names it returns can be represented by
    HOL `mlstring`. The Boolean guard is deliberately over the emitted local
    names only: `varExpHOL_expToHOL_decode` needs precisely that domain, and
    other source names are not observable in this result. On arbitrary
    production strings outside that domain, retain the original collector.
    The theorem below proves this adapter always returns the production list. -/
def expLocalVarsViaHOLWhenByteRanged {width : Nat} [NeZero width]
    (expression : Exp (BitVec width)) : List String :=
  let names := Flapjack.expLocalVars expression
  if names.all (fun name => name.toList.all (fun c => decide (c.toNat < 256))) then
    (varExpHOL (expToHOL expression)).map toStringOfBytes
  else
    names

/-- The exact routed collector preserves the production list for every input:
    on byte-ranged emitted names this is `varExpHOL` decoded through the
    reviewed `String`/`MlString` bridge; otherwise it takes the unchanged
    production fallback. -/
@[simp] theorem expLocalVarsViaHOLWhenByteRanged_eq {width : Nat} [NeZero width]
    (expression : Exp (BitVec width)) :
    expLocalVarsViaHOLWhenByteRanged expression = Flapjack.expLocalVars expression := by
  unfold expLocalVarsViaHOLWhenByteRanged
  dsimp only
  by_cases hnames : (Flapjack.expLocalVars expression).all
      (fun name => name.toList.all (fun c => decide (c.toNat < 256))) = true
  · simp only [hnames, if_pos]
    apply Flapjack.Pancake.PanLang.varExpHOL_expToHOL_decode
    intro name hmem c hc
    have hname := List.all_eq_true.mp hnames name hmem
    have hchar := List.all_eq_true.mp hname c hc
    simpa only [decide_eq_true_eq] using hchar
  · simp [hnames]

/-- List form of the preceding pointwise equality, used by the generated-name
    calculation in the routed handled-call clause. -/
@[simp] theorem expLocalVarsViaHOLWhenByteRanged_flatMap_eq {width : Nat} [NeZero width]
    (expressions : List (Exp (BitVec width))) :
    expressions.flatMap expLocalVarsViaHOLWhenByteRanged =
      expressions.flatMap Flapjack.expLocalVars := by
  induction expressions with
  | nil => rfl
  | cons expression rest ih => simp [ih]

/-- Decoding exact argument-variable lists agrees with the production collector
    on decoded exact expressions. This Flapjack codec lemma has no separate HOL
    original; it supplies the argument component of the handled Call name list
    at `pan_globalsScript.sml:118`, without claiming whole-pass routing. -/
theorem exactArgumentNames_decode {width : Nat} [NeZero width]
    (arguments : List (ExpHOL width)) :
    (arguments.flatMap varExpHOL).map toStringOfBytes =
      (arguments.map expOfHOL).flatMap expLocalVarsViaHOLWhenByteRanged := by
  have hvarList (expressions : List (ExpHOL width))
      (hvars : ∀ expression ∈ expressions,
        (varExpHOL expression).map toStringOfBytes =
          Flapjack.expLocalVars (expOfHOL expression)) :
      ((expressions.map varExpHOL).flatten).map toStringOfBytes =
        Flapjack.expLocalVars.expLocalVarsList (expressions.map expOfHOL) := by
    induction expressions with
    | nil => simp [Flapjack.expLocalVars.expLocalVarsList]
    | cons head tail ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append,
        Flapjack.expLocalVars.expLocalVarsList.eq_2]
      rw [hvars head (by simp), ih (fun expression hmem => hvars expression (by simp [hmem]))]
  have hvarFieldList (fields : List (MlS × ExpHOL width))
      (hvars : ∀ field ∈ fields,
        (varExpHOL field.2).map toStringOfBytes =
          Flapjack.expLocalVars (expOfHOL field.2)) :
      ((fields.map (fun field => varExpHOL field.2)).flatten).map toStringOfBytes =
        Flapjack.expLocalVars.expLocalVarsFieldList
          (fields.map (fun field => (toStringOfBytes field.1, expOfHOL field.2))) := by
    induction fields with
    | nil => simp [Flapjack.expLocalVars.expLocalVarsFieldList]
    | cons head tail ih =>
      simp only [List.map_cons, List.flatten_cons, List.map_append,
        Flapjack.expLocalVars.expLocalVarsFieldList.eq_2]
      rw [hvars head (by simp), ih (fun field hmem => hvars field (by simp [hmem]))]
  have hexp (expression : ExpHOL width) :
      (varExpHOL expression).map toStringOfBytes =
        Flapjack.expLocalVars (expOfHOL expression) := by
    fun_induction varExpHOL expression <;>
      simp_all [Flapjack.expLocalVars, expOfHOL, List.map_append]
    all_goals first
      | apply hvarList _ <;> assumption
      | apply hvarFieldList _ <;> assumption
  induction arguments with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.flatMap_cons, List.map_append, List.map_cons,
        expLocalVarsViaHOLWhenByteRanged_eq]
      rw [hexp head]
      simpa only [expLocalVarsViaHOLWhenByteRanged_flatMap_eq] using
        congrArg (fun names => Flapjack.expLocalVars (expOfHOL head) ++ names) ih

/-- `MAP (compile_exp ctxt)` for the routed expression compiler.  Flapjack
    routing infrastructure (untagged). -/
def compileExpRouteCakeArgs [BEq String] [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) :
    List (Exp (BitVec width)) → List (Exp (BitVec width))
  | [] => []
  | expression :: expressions =>
      compileExpRouteCake context expression :: compileExpRouteCakeArgs context expressions

/-- The routed expression compiler agrees with the production `compileExpCake`
    on the `cakeContextOfPass` view, by `compileExpCake_ofPass_eq`.  Flapjack
    routing infrastructure (untagged). -/
theorem compileExpCake_eq_route [BEq String] [LawfulBEq String] {width : Nat}
    [NeZero width] (context : GlobalPassContext (BitVec width))
    (hshapes : GlobalContextListShapesByteRanged context)
    (expression : Exp (BitVec width)) (hranged : ExpByteRanged expression) :
    compileExpCake (cakeContextOfPass context) expression
      = compileExpRouteCake context expression :=
  compileExpCake_ofPass_eq context hshapes expression hranged

/-- The routed argument-list compiler agrees with the production
    `compileExpCakeArgs` on byte-ranged lists.  Flapjack routing infrastructure
    (untagged). -/
theorem compileExpCakeArgs_eq_route [BEq String] [LawfulBEq String] {width : Nat}
    [NeZero width] (context : GlobalPassContext (BitVec width))
    (hshapes : GlobalContextListShapesByteRanged context)
    (arguments : List (Exp (BitVec width)))
    (harguments : ∀ expression ∈ arguments, ExpByteRanged expression) :
    compileExpCakeArgs (cakeContextOfPass context) arguments
      = compileExpRouteCakeArgs context arguments := by
  induction arguments with
  | nil => simp only [compileExpCakeArgs, compileExpRouteCakeArgs]
  | cons expression expressions ih =>
      simp only [compileExpCakeArgs, compileExpRouteCakeArgs]
      rw [compileExpCake_ofPass_eq context hshapes expression (harguments expression (by simp)),
        ih (fun e he => harguments e (by simp [he]))]
      rfl

/-- Routed sibling of the production `compileProgCake`: it threads the production
    `GlobalPassContext` and replaces every expression call site with
    `compileExpRouteCake` (which textually invokes the reviewed
    `compileExpExactHOL`), while leaving every non-expression clause identical to
    `compileProgCake (cakeContextOfPass context)`.  Flapjack routing
    infrastructure (untagged). -/
def compileProgCakeOfExact [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) : Prog (BitVec width) → Prog (BitVec width)
  | .dec name shape value body =>
      .dec name shape (compileExpRouteCake context value)
        (compileProgCakeOfExact context body)
  | .assign .global name value =>
      match FLOOKUP (cakeContextOfPass context).globals name with
      | some (_, address) =>
          .store (.op .sub [.topAddr, .const address]) (compileExpRouteCake context value)
      | none => .skip
  | .assign .local name value => .assign .local name (compileExpRouteCake context value)
  | .primitive name operator arguments =>
      .primitive name operator (compileExpRouteCakeArgs context arguments)
  | .store address value =>
      .store (compileExpRouteCake context address) (compileExpRouteCake context value)
  | .store32 address value =>
      .store32 (compileExpRouteCake context address) (compileExpRouteCake context value)
  | .storeByte address value =>
      .storeByte (compileExpRouteCake context address) (compileExpRouteCake context value)
  | .seq first second =>
      .seq (compileProgCakeOfExact context first) (compileProgCakeOfExact context second)
  | .ite condition thenBranch elseBranch =>
      .ite (compileExpRouteCake context condition)
        (compileProgCakeOfExact context thenBranch) (compileProgCakeOfExact context elseBranch)
  | .while condition body =>
      .while (compileExpRouteCake context condition) (compileProgCakeOfExact context body)
  | .call info function arguments =>
      let compiledArguments := compileExpRouteCakeArgs context arguments
      match info with
        | none => .call none function compiledArguments
        | some (none, none) =>
            .call (some (none, none)) function compiledArguments
        | some (none, some (exception, handlerVar, handler)) =>
            .call (some (none, some (exception, handlerVar,
              compileProgCakeOfExact context handler))) function compiledArguments
        | some (some (.local, name), none) =>
            .call (some (some (.local, name), none)) function compiledArguments
        | some (some (.local, name), some (exception, handlerVar, handler)) =>
            .call (some (some (.local, name), some (exception, handlerVar,
              compileProgCakeOfExact context handler))) function compiledArguments
        | some (some (.global, name), none) =>
            match FLOOKUP (cakeContextOfPass context).globals name with
            | some (shape, address) =>
                .decCall "" shape function compiledArguments
                  (.store (.op .sub [.topAddr, .const address])
                    (.var .local ""))
            | none =>
                .call (some (none, none)) function compiledArguments
        | some (some (.global, name), some (exception, handlerVar, handler)) =>
            match FLOOKUP (cakeContextOfPass context).globals name with
            | some (shape, address) =>
                let compiledHandlerProgram := compileProgCakeOfExact context handler
                let names := handlerVar :: freeVarIds compiledHandlerProgram ++
                  compiledArguments.flatMap expLocalVarsViaHOLWhenByteRanged
                let resultName := freshNameHOL "" names
                let flagName := freshNameHOL "vn'" (resultName :: names)
                let handlerBody :=
                  .seq compiledHandlerProgram
                    (.assign .local flagName (.const (BitVec.ofNat width 1)))
                let callInfo := some (some (.local, resultName),
                  some (exception, handlerVar, handlerBody))
                let callProgram : Prog (BitVec width) :=
                  .call callInfo function compiledArguments
                let storeAddress : Exp (BitVec width) :=
                  .op .sub [.topAddr, .const address]
                .dec resultName shape (cakeShapeVal (cakeContextOfPass context) shape)
                  (.dec flagName .one (.const (BitVec.ofNat width 0))
                    (.seq callProgram
                      (.ite (.var .local flagName) .skip
                        (.store storeAddress
                          (.var .local resultName)))))
            | none =>
                .call (some (none, some (exception, handlerVar,
                  compileProgCakeOfExact context handler))) function compiledArguments
  | .decCall name shape function arguments body =>
      .decCall name shape function (compileExpRouteCakeArgs context arguments)
        (compileProgCakeOfExact context body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function (compileExpRouteCake context configuration)
        (compileExpRouteCake context configurationLength) (compileExpRouteCake context array)
        (compileExpRouteCake context arrayLength)
  | .raise exception value => .raise exception (compileExpRouteCake context value)
  | .return value => .return (compileExpRouteCake context value)
  | .shMemLoad size kind name address =>
      match kind, FLOOKUP (cakeContextOfPass context).globals name with
      | .local, _ =>
          .shMemLoad size .local name (compileExpRouteCake context address)
      | .global, some (.one, globalAddress) =>
          let localName := name ++ globalApostrophes 1
          .dec name .one (compileExpRouteCake context address)
            (.dec localName .one (.const (BitVec.ofNat width 0))
              (.seq
                (.shMemLoad size .local localName (.var .local name))
                (.store (.op .sub [.topAddr, .const globalAddress])
                  (.var .local localName))))
      | .global, _ => .skip
  | .shMemStore size address value =>
      .shMemStore size (compileExpRouteCake context address) (compileExpRouteCake context value)
  | program => program
termination_by program => sizeOf program

/-- Constructor-level commute fact for local assignment.  This is Flapjack
    proof infrastructure (untagged): it discharges the easiest `VarKind`
    branch of the bridge from the routed production compiler to the exact
    `pan_globals$compile_def` port.  Only the identifier needs byte-range
    evidence for decoding `MlS` back to `String`; the expression route itself
    is definitionally the exact compiler result decoded through `expOfHOL`. -/
theorem compileProgCakeOfExact_local_assign_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (name : String)
    (value : Exp (BitVec width)) (hname : NameRanged name) :
    compileProgCakeOfExact context (.assign .local name value) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.assign .local name value))) := by
  simp only [compileProgCakeOfExact, compileExpRouteCake, progOfHOL,
    compileProgExactHOL, progToHOL]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname]

/-- The exact finite-map lookup induced by a production `InfoMap` is the
    `shapeToHOL` image of the same production lookup for byte-ranged names.
    This is the carrier relation needed by the global `VarKind` clauses of the
    compiler commute proof; it is Flapjack infrastructure, not a HOL
    declaration. -/
theorem panGlobalsContextExact_ofPass_lookup [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (name : String)
    (hname : NameRanged name) :
    (PanGlobalsContextExact.ofPass context).globals.lookup (ofString name) =
      (lookupInfo name context.globals).map
        (fun entry => (shapeToHOL entry.1, entry.2)) := by
  simp [PanGlobalsContextExact.ofPass,
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname]

/-- Constructor-level commute fact for global assignment.  It uses the explicit
    exact-finite-map/production-`InfoMap` lookup relation above; it remains
    byte-range scoped because the exact context is keyed by `MlS`.  Flapjack
    routing infrastructure, not a HOL declaration. -/
theorem compileProgCakeOfExact_global_assign_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (name : String)
    (value : Exp (BitVec width)) (hname : NameRanged name) :
    compileProgCakeOfExact context (.assign .global name value) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.assign .global name value))) := by
  simp only [compileProgCakeOfExact, compileProgExactHOL, progToHOL, FLOOKUP,
    FLOOKUP_cakeContextOfPass_globals]
  rw [panGlobalsContextExact_ofPass_lookup context name hname]
  cases h : lookupInfo name context.globals with
  | none => simp [progOfHOL]
  | some entry =>
      obtain ⟨shape, address⟩ := entry
      simp [progOfHOL, compileExpRouteCake, expOfHOL]

/-- Constructor commute leaf for `.skip`.  This needs no byte-range premise:
    the production and exact compiler equations both preserve the constructor
    literally.  Flapjack routing infrastructure (untagged). -/
theorem compileProgCakeOfExact_skip_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) :
    compileProgCakeOfExact context (.skip : Prog (BitVec width)) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.skip : Prog (BitVec width)))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progOfHOL, progToHOL]

/-- Constructor commute leaf for `.return`.  The expression is encoded and
    decoded on both sides of the bridge in the same way, so no additional
    name-domain assumption is required.  Flapjack routing infrastructure
    (untagged). -/
theorem compileProgCakeOfExact_return_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (value : Exp (BitVec width)) :
    compileProgCakeOfExact context (.return value) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.return value))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progOfHOL, progToHOL,
    compileExpRouteCake]

/-- Constructor commute leaves for the three direct stores and shared-memory
    store.  Their expression fields are passed through the same exact codec on
    both sides, without introducing any name or context side condition.
    Flapjack routing infrastructure (untagged). -/
theorem compileProgCakeOfExact_store_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (address value : Exp (BitVec width)) :
    compileProgCakeOfExact context (.store address value) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.store address value))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progOfHOL, progToHOL,
    compileExpRouteCake]

/-- Flapjack-only constructor bridge: there is no separate HOL declaration for
    this representation-level commute. -/
theorem compileProgCakeOfExact_store32_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (address value : Exp (BitVec width)) :
    compileProgCakeOfExact context (.store32 address value) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.store32 address value))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progOfHOL, progToHOL,
    compileExpRouteCake]

/-- Flapjack-only constructor bridge: there is no separate HOL declaration for
    this representation-level commute. -/
theorem compileProgCakeOfExact_storeByte_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (address value : Exp (BitVec width)) :
    compileProgCakeOfExact context (.storeByte address value) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.storeByte address value))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progOfHOL, progToHOL,
    compileExpRouteCake]

/-- Flapjack-only constructor bridge: there is no separate HOL declaration for
    this representation-level commute. -/
theorem compileProgCakeOfExact_shMemStore_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (size : OpSize)
    (address value : Exp (BitVec width)) :
    compileProgCakeOfExact context (.shMemStore size address value) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.shMemStore size address value))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progOfHOL, progToHOL,
    compileExpRouteCake]

/-- The `.raise` constructor commute is exact when its exception identifier can
    be represented by HOL `mlstring`; that premise is needed only for the
    `String`/`MlS` round trip performed by `progOfHOL`.  Flapjack routing
    infrastructure (untagged). -/
theorem compileProgCakeOfExact_raise_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (exception : String)
    (value : Exp (BitVec width)) (hname : NameRanged exception) :
    compileProgCakeOfExact context (.raise exception value) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.raise exception value))) := by
  simp only [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL,
    compileExpRouteCake]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes exception hname]

/-- The `.extCall` constructor commute is exact when its function identifier is
    in HOL's byte-string domain.  The four expression fields follow the same
    exact expression route on each side.  Flapjack routing infrastructure
    (untagged). -/
theorem compileProgCakeOfExact_extCall_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (function : String)
    (configuration configurationLength array arrayLength : Exp (BitVec width))
    (hname : NameRanged function) :
    compileProgCakeOfExact context
        (.extCall function configuration configurationLength array arrayLength) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL
          (.extCall function configuration configurationLength array arrayLength))) := by
  simp only [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL,
    compileExpRouteCake]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hname]

/-- Flapjack-only list adapter: exposes that the routed argument list is the
    decoded `compileExpExactHOLList` result.  There is no separate HOL
    declaration for this factoring lemma; it unfolds the local route/list
    definitions and is intentionally untagged. -/
theorem compileExpRouteCakeArgs_eq_exact [BEq String] [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width))
    (arguments : List (Exp (BitVec width))) :
    compileExpRouteCakeArgs context arguments =
      (compileExpExactHOLList (PanGlobalsContextExact.ofPass context)
        (arguments.map expToHOL)).map expOfHOL := by
  induction arguments with
  | nil => simp [compileExpRouteCakeArgs, compileExpExactHOLList]
  | cons argument rest ih =>
      simp [compileExpRouteCakeArgs, compileExpRouteCake, compileExpExactHOLList, ih]

/-- The primitive constructor commute is exact when its primitive identifier is
    representable by HOL `mlstring`.  Its argument list uses the exact routed
    expression-list compiler on both sides.  Flapjack routing infrastructure
    (untagged). -/
theorem compileProgCakeOfExact_primitive_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (name : String)
    (operator : PrimOp) (arguments : List (Exp (BitVec width)))
    (hname : NameRanged name) :
    compileProgCakeOfExact context (.primitive name operator arguments) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.primitive name operator arguments))) := by
  simp only [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname]
  rw [compileExpRouteCakeArgs_eq_exact]

/-- Compositional `Seq` case for the exact compiler commute.  These are exactly
    the two recursive commute premises; no extra success or evaluator premise
    is introduced.  Flapjack routing infrastructure (untagged). -/
theorem compileProgCakeOfExact_seq_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width))
    (first second : Prog (BitVec width))
    (hfirst : compileProgCakeOfExact context first =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL first)))
    (hsecond : compileProgCakeOfExact context second =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL second))) :
    compileProgCakeOfExact context (.seq first second) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.seq first second))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progOfHOL, progToHOL,
    hfirst, hsecond]

/-- Compositional `If` case for the exact compiler commute.  It takes the two
    branch commute facts as its recursive premises; the condition follows the
    same exact expression route on both sides.  Flapjack routing infrastructure
    (untagged). -/
theorem compileProgCakeOfExact_ite_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (condition : Exp (BitVec width))
    (thenBranch elseBranch : Prog (BitVec width))
    (hthen : compileProgCakeOfExact context thenBranch =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL thenBranch)))
    ( helse : compileProgCakeOfExact context elseBranch =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL elseBranch))) :
    compileProgCakeOfExact context (.ite condition thenBranch elseBranch) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.ite condition thenBranch elseBranch))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progOfHOL, progToHOL,
    compileExpRouteCake, hthen, helse]

/-- Compositional `While` case for the exact compiler commute, with precisely
    the recursive body commute premise.  Flapjack routing infrastructure
    (untagged). -/
theorem compileProgCakeOfExact_while_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (condition : Exp (BitVec width))
    (body : Prog (BitVec width))
    (hbody : compileProgCakeOfExact context body =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL body))) :
    compileProgCakeOfExact context (.while condition body) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.while condition body))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progOfHOL, progToHOL,
    compileExpRouteCake, hbody]

/-- Compositional `.dec` case.  The body commute is the recursive premise;
    `NameRanged` and `ShapeByteRanged` are precisely the codecs needed to
    recover the production binder and shape after the HOL round trip.  Flapjack
    routing infrastructure (untagged). -/
theorem compileProgCakeOfExact_dec_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (name : String) (shape : Shape)
    (value : Exp (BitVec width)) (body : Prog (BitVec width))
    (hname : NameRanged name) (hshape : ShapeByteRanged shape)
    (hbody : compileProgCakeOfExact context body =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL body))) :
    compileProgCakeOfExact context (.dec name shape value body) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.dec name shape value body))) := by
  simp only [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL,
    compileExpRouteCake]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname,
    Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL shape hshape, hbody]

/-- Compositional `.decCall` case.  The body equality is the sole recursive
    premise.  The declaration/callee identifiers and shape retain the exact
    parser-backed codec premises; arguments use the pointwise exact expression
    route.  Flapjack routing infrastructure (untagged). -/
theorem compileProgCakeOfExact_decCall_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (name : String) (shape : Shape)
    (function : String) (arguments : List (Exp (BitVec width)))
    (body : Prog (BitVec width))
    (hname : NameRanged name) (hshape : ShapeByteRanged shape)
    (hfunction : NameRanged function)
    (hbody : compileProgCakeOfExact context body =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL body))) :
    compileProgCakeOfExact context (.decCall name shape function arguments body) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.decCall name shape function arguments body))) := by
  simp only [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname,
    Flapjack.Pancake.PanLang.shapeOfHOL_shapeToHOL shape hshape,
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction,
    hbody, compileExpRouteCakeArgs_eq_exact]

/-- Global return calls without handlers commute for both production lookup
    outcomes.  The `One`-independent shape binder is recovered from the
    parser-backed context shape invariant; call arguments themselves require
    no byte-range premise because both paths pass through `expToHOL`.  This is
    Flapjack routing infrastructure, not a distinct HOL declaration. -/
theorem compileProgCakeOfExact_call_global_return_no_handler_exact_bridge
    [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (name function : String)
    (arguments : List (Exp (BitVec width)))
    (hname : NameRanged name) (hfunction : NameRanged function)
    (hshapes : GlobalContextListShapesByteRanged context) :
    compileProgCakeOfExact context
        (.call (some (some (.global, name), none)) function arguments) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.call (some (some (.global, name), none)) function arguments))) := by
  have hnameDecode : toStringOfBytes (ofString name) = name :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname
  have hempty : toStringOfBytes (ofString "") = "" :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes "" (by decide)
  cases hlookup : lookupInfo name context.globals with
  | none =>
      simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL,
        PanGlobalsContextExact.ofPass_globals_lookup, FLOOKUP,
        FLOOKUP_cakeContextOfPass_globals, hlookup, progOfHOL, hnameDecode,
        Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction,
        compileExpRouteCakeArgs_eq_exact]
  | some entry =>
      obtain ⟨shape, address⟩ := entry
      have hshape : ShapeByteRanged shape :=
        hshapes (name, (shape, address))
          (lookupInfo_eq_some_mem name context.globals hlookup)
      simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL,
        PanGlobalsContextExact.ofPass_globals_lookup, FLOOKUP,
        FLOOKUP_cakeContextOfPass_globals, hlookup, progOfHOL, hnameDecode,
        hshape,
        Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes function hfunction,
        hempty, expOfHOL, compileExpRouteCakeArgs_eq_exact]

/-- The local `.shMemLoad` commute is exact under the byte-string premise for
    its binder; its address uses the same exact expression route on both sides.
    Flapjack routing infrastructure (untagged). -/
theorem compileProgCakeOfExact_shMemLoad_local_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (size : OpSize) (name : String)
    (address : Exp (BitVec width)) (hname : NameRanged name) :
    compileProgCakeOfExact context (.shMemLoad size .local name address) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.shMemLoad size .local name address))) := by
  simp only [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL,
    compileExpRouteCake]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname]

/-- Global shared-memory loads commute with the exact compiler for the
    production `InfoMap` lookup outcomes.  The generated local binder is
    decoded with the same byte codec used to construct `ofPass`; this is
    Flapjack-only routing infrastructure, not a separate HOL declaration. -/
theorem compileProgCakeOfExact_shMemLoad_global_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (size : OpSize) (name : String)
    (address : Exp (BitVec width)) (hname : NameRanged name) :
    compileProgCakeOfExact context (.shMemLoad size .global name address) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.shMemLoad size .global name address))) := by
  have hnameDecode : toStringOfBytes (ofString name) = name :=
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes name hname
  have hlocal :
      toStringOfBytes
          (Flapjack.Pancake.PanLang.mlstrAppend (ofString name) (ofString "'")) =
        name ++ globalApostrophes 1 := by
    rw [toStringOfBytes_mlstrAppend, hnameDecode, toStringOfBytes_ofString_quote]
    rfl
  cases hlookup : lookupInfo name context.globals with
  | none =>
      simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL,
        PanGlobalsContextExact.ofPass_globals_lookup, FLOOKUP,
        FLOOKUP_cakeContextOfPass_globals, hlookup, progOfHOL, hnameDecode]
  | some entry =>
      obtain ⟨shape, globalAddress⟩ := entry
      cases shape with
      | one =>
          simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL,
            PanGlobalsContextExact.ofPass_globals_lookup, FLOOKUP,
            FLOOKUP_cakeContextOfPass_globals, hlookup, progOfHOL, expOfHOL,
            compileExpRouteCake, shapeToHOL, shapeOfHOL, hnameDecode, hlocal]
      | comb fields =>
          simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL,
            PanGlobalsContextExact.ofPass_globals_lookup, FLOOKUP,
            FLOOKUP_cakeContextOfPass_globals, hlookup, progOfHOL,
            shapeToHOL, hnameDecode]
      | named fieldName =>
          simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL,
            PanGlobalsContextExact.ofPass_globals_lookup, FLOOKUP,
            FLOOKUP_cakeContextOfPass_globals, hlookup, progOfHOL,
            shapeToHOL, hnameDecode]

/-- Literal control constructors `.break`, `.continue`, and `.tick` commute
    without byte-range premises because both compilers leave them unchanged.
    Flapjack routing infrastructure (untagged). -/
theorem compileProgCakeOfExact_break_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) :
    compileProgCakeOfExact context (.break : Prog (BitVec width)) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.break : Prog (BitVec width)))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL]

/-- Flapjack-only constructor bridge: there is no separate HOL declaration for
    this representation-level commute. -/
theorem compileProgCakeOfExact_continue_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) :
    compileProgCakeOfExact context (.continue : Prog (BitVec width)) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.continue : Prog (BitVec width)))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL]

/-- Flapjack-only constructor bridge: there is no separate HOL declaration for
    this representation-level commute. -/
theorem compileProgCakeOfExact_tick_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) :
    compileProgCakeOfExact context (.tick : Prog (BitVec width)) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.tick : Prog (BitVec width)))) := by
  simp [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL]

/-- The annotation constructor is the exact fallback case when both literal
    annotation strings are in HOL's byte-string domain.  Flapjack routing
    infrastructure (untagged). -/
theorem compileProgCakeOfExact_annot_exact_bridge [LawfulBEq String]
    {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (tag text : String)
    (htag : NameRanged tag) (htext : NameRanged text) :
    compileProgCakeOfExact context (.annot tag text) =
      progOfHOL (compileProgExactHOL (PanGlobalsContextExact.ofPass context)
        (progToHOL (.annot tag text))) := by
  simp only [compileProgCakeOfExact, compileProgExactHOL, progToHOL, progOfHOL]
  rw [Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes tag htag,
    Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes text htext]

/-- The routed program compiler computes exactly the production `compileProgCake`
    on the `cakeContextOfPass` view, for byte-ranged programs.  Flapjack routing
    infrastructure (untagged). -/
theorem compileProgCakeOfExact_eq [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width))
    (hshapes : GlobalContextListShapesByteRanged context) :
    ∀ program : Prog (BitVec width), ProgByteRanged program →
      compileProgCakeOfExact context program
        = compileProgCake (cakeContextOfPass context) program := by
  apply compileProgCake.induct (cakeContextOfPass context)
    (motive := fun program =>
      ProgByteRanged program →
        compileProgCakeOfExact context program
          = compileProgCake (cakeContextOfPass context) program)
  all_goals
    intros
    simp_all [compileProgCakeOfExact, compileProgCake, ProgByteRanged,
      compileExpCake_eq_route context hshapes, compileExpCakeArgs_eq_route context hshapes]

/-- Routed sibling of the production `compileDecsCake`: it threads the production
    `GlobalPassContext` by consing each `.decl` onto the association list (exactly
    as `globalCompileDecsThreaded` does) and routes function bodies and
    initializer expressions through the routed siblings
    `compileProgCakeOfExact`/`compileExpRouteCake`.  Flapjack routing
    infrastructure (untagged). -/
def compileDecsCakeOfExact [LawfulBEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) :
    List (Decl (BitVec width)) → CakeCompileDecsResult width
  | [] =>
      { initializers := [], functions := [], exceptions := []
        context := cakeContextOfPass context }
  | .function declaration :: declarations =>
      let rest := compileDecsCakeOfExact context declarations
      { initializers := rest.initializers
        functions := .function { declaration with
            body := compileProgCakeOfExact context declaration.body } :: rest.functions
        exceptions := rest.exceptions
        context := rest.context }
  | .exnDecl exception shape :: declarations =>
      let rest := compileDecsCakeOfExact context declarations
      { rest with exceptions := .exnDecl exception shape :: rest.exceptions }
  | .name _ _ :: declarations => compileDecsCakeOfExact context declarations
  | .decl shape name value :: declarations =>
      let address := cakeAddress (cakeContextOfPass context) shape
      let nextContext := { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address }
      let rest := compileDecsCakeOfExact nextContext declarations
      { initializers :=
          .store (.op .sub [.topAddr, .const address])
            (compileExpRouteCake context value) :: rest.initializers
        functions := rest.functions
        exceptions := rest.exceptions
        context := rest.context }

/-- The routed declaration compiler computes exactly the production
    `compileDecsCake` on the `cakeContextOfPass` view, for byte-ranged
    declarations.  Flapjack routing infrastructure (untagged). -/
theorem compileDecsCakeOfExact_eq [LawfulBEq String] {width : Nat} [NeZero width]
    (declarations : List (Decl (BitVec width))) :
    ∀ (context : GlobalPassContext (BitVec width)),
      context.IsCakeCanonical → GlobalContextListShapesByteRanged context →
      (∀ declaration ∈ declarations, DeclByteRanged declaration) →
        compileDecsCakeOfExact context declarations
          = compileDecsCake (cakeContextOfPass context) declarations := by
  induction declarations with
  | nil => intro context _ _ _; rfl
  | cons declaration declarations ih =>
      intro context hcanonical hshapes hdecl
      have hcanonical' : context.IsCakeCanonical := hcanonical
      cases declaration with
      | function function =>
          have hbody : ProgByteRanged function.body :=
            (hdecl (.function function) (by simp)).2.2.1
          simp only [compileDecsCakeOfExact, compileDecsCake]
          rw [ih context hcanonical' hshapes
              (fun d hd => hdecl d (by simp [hd])),
            compileProgCakeOfExact_eq context hshapes function.body hbody]
      | exnDecl exception shape =>
          simp only [compileDecsCakeOfExact, compileDecsCake]
          rw [ih context hcanonical' hshapes
            (fun d hd => hdecl d (by simp [hd]))]
      | name struct fields =>
          simp only [compileDecsCakeOfExact, compileDecsCake]
          exact ih context hcanonical' hshapes
            (fun d hd => hdecl d (by simp [hd]))
      | decl shape name value =>
          have hhead := hdecl (.decl shape name value) (by simp)
          simp only [DeclByteRanged] at hhead
          obtain ⟨hshape, _hname, hvalue⟩ := hhead
          have htail : ∀ d ∈ declarations, DeclByteRanged d :=
            fun d hd => hdecl d (by simp [hd])
          have hshapes' : GlobalContextListShapesByteRanged
              { context with
                globals := (name, (shape, cakeAddress (cakeContextOfPass context) shape))
                  :: context.globals
                globalsSize := cakeAddress (cakeContextOfPass context) shape } :=
            globalContextListShapesByteRanged_update context name shape
              (cakeAddress (cakeContextOfPass context) shape) hshapes hshape
          have hcanonicalNext : ({ context with
                globals := (name, (shape, cakeAddress (cakeContextOfPass context) shape))
                  :: context.globals
                globalsSize := cakeAddress (cakeContextOfPass context) shape } :
              GlobalPassContext (BitVec width)).IsCakeCanonical := hcanonical
          simp only [compileDecsCakeOfExact, compileDecsCake]
          erw [← cakeContextOfPass_update context name shape
            (cakeAddress (cakeContextOfPass context) shape)]
          rw [ih _ hcanonicalNext hshapes' htail,
            compileExpCake_eq_route context hshapes value hvalue]

end Flapjack
