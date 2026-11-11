module

public import Flapjack.HolRef
public import Flapjack.FiniteMap.Basic
public import Flapjack.Pancake.PanStructs
public import Flapjack.Pancake.PanSimp
public import Flapjack.Pancake.PanLang.Prog
public import Flapjack.Pancake.PanLang.Decl

@[expose] public section

/-!
The core of Pancake's `pan_globals` pass.

Global values are laid out in the heap from `TopAddr`. This module keeps the
word representation abstract and receives the natural-number-to-word map in
the context, allowing the same executable pass to be instantiated with
`BitVec` for the RISC-V backend or with `Nat` in small tests.
-/

namespace Flapjack

structure GlobalPassContext (α : Type u) where
  globals : InfoMap (Shape × α)
  globalsSize : α
  maxGlobalsSize : α
  bytesInWord : α
  fromNat : Nat → α

structure GlobalCompiledProgram (α : Type u) where
  initializers : List (Prog α)
  declarations : List (Decl α)
  context : GlobalPassContext α

def globalAddress [Add α] [Mul α] (context : GlobalPassContext α) (shape : Shape) : α :=
  context.globalsSize + context.bytesInWord * context.fromNat (Shape.shapeSize shape)

def globalCompileExp [BEq String] (context : GlobalPassContext α) : Exp α → Exp α
  | .var .local name => .var .local name
  | .var .global name =>
      match lookupInfo name context.globals with
      | some (shape, address) =>
          .load shape (.op .sub [.topAddr, .const address])
      | none => .const (context.fromNat 0)
  | .rStruct expressions => .rStruct (globalCompileExps context expressions)
  | .rField index expression => .rField index (globalCompileExp context expression)
  | .nStruct _ _ => .const (context.fromNat 0)
  | .nField _ _ => .const (context.fromNat 0)
  | .load shape address => .load shape (globalCompileExp context address)
  | .load32 address => .load32 (globalCompileExp context address)
  | .loadByte address => .loadByte (globalCompileExp context address)
  | .op operator expressions => .op operator (globalCompileExps context expressions)
  | .panOp operator expressions => .panOp operator (globalCompileExps context expressions)
  | .cmp operator left right =>
      .cmp operator (globalCompileExp context left) (globalCompileExp context right)
  | .shift operator left right =>
      .shift operator (globalCompileExp context left) (globalCompileExp context right)
  | .topAddr => .op .sub [.topAddr, .const context.maxGlobalsSize]
  | expression => expression
termination_by expression => sizeOf expression
where
  globalCompileExps [BEq String] (context : GlobalPassContext α) :
      List (Exp α) → List (Exp α)
    | [] => []
    | expression :: expressions =>
        globalCompileExp context expression :: globalCompileExps context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def globalCompileExpList [BEq String] (context : GlobalPassContext α) :
    List (Exp α) → List (Exp α)
  | [] => []
  | expression :: expressions =>
      globalCompileExp context expression :: globalCompileExpList context expressions
termination_by expressions => sizeOf expressions
decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

def globalApostrophes : Nat → String
  | 0 => ""
  | count + 1 => "'" ++ globalApostrophes count

def globalFreshNameAux [BEq String] (name : String) (names : List String) :
    Nat → Nat → String
  | candidate, 0 => name ++ globalApostrophes candidate
  | candidate, fuel + 1 =>
      let candidateName := name ++ globalApostrophes candidate
      if names.contains candidateName then
        globalFreshNameAux name names (candidate + 1) fuel
      else candidateName

def globalFreshName [BEq String] (name : String) (names : List String) : String :=
  globalFreshNameAux name names 0 names.length

/-! Counterpart of Cake's `fresh_name_correct`
    (`pan_globalsProofScript.sml:993`): the name chosen by the fresh-name search
    is never a member of the list it was searching.  The search starts with
    `names.length` fuel and tries `name`, `name'`, `name''`, ... in turn, so if
    it ran out of fuel it would have found `names.length + 1` distinct candidates
    already present in `names`, which is impossible. -/
theorem globalApostrophes_length (count : Nat) :
    (globalApostrophes count).length = count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hsingleton : ("'" : String).length = 1 := rfl
      simp [globalApostrophes, String.length_append, ih, hsingleton]
      omega

theorem append_globalApostrophes_injective (name : String) :
    Function.Injective (fun count => name ++ globalApostrophes count) := by
  intro left right heq
  have hlen := congrArg String.length heq
  rw [String.length_append, String.length_append, globalApostrophes_length,
    globalApostrophes_length] at hlen
  exact Nat.add_left_cancel hlen

theorem globalFreshNameAux_not_mem_or_all_mem [BEq String] [LawfulBEq String]
    (name : String) (names : List String) (candidate fuel : Nat) :
    globalFreshNameAux name names candidate fuel ∉ names ∨
      ∀ k, k ≤ fuel → name ++ globalApostrophes (candidate + k) ∈ names := by
  induction fuel generalizing candidate with
  | zero =>
      rw [globalFreshNameAux]
      by_cases hmem : name ++ globalApostrophes candidate ∈ names
      · exact Or.inr (fun k hk => by
          have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
          subst hk0
          exact hmem)
      · exact Or.inl hmem
  | succ fuel ih =>
      rw [globalFreshNameAux]
      by_cases hcontains :
          names.contains (name ++ globalApostrophes candidate) = true
      · rw [if_pos hcontains]
        rcases ih (candidate + 1) with hnotmem | hall
        · exact Or.inl hnotmem
        · refine Or.inr (fun k hk => ?_)
          cases k with
          | zero =>
              simpa using (List.contains_iff_mem.mp hcontains)
          | succ j =>
              have hj : j ≤ fuel := Nat.succ_le_succ_iff.mp hk
              have hstep : candidate + (j + 1) = candidate + 1 + j := by omega
              rw [hstep]
              exact hall j hj
      · rw [if_neg hcontains]
        exact Or.inl (fun hmem =>
          hcontains (List.contains_iff_mem.mpr hmem))

theorem globalFreshName_not_mem [BEq String] [LawfulBEq String]
    (name : String) (names : List String) :
    globalFreshName name names ∉ names := by
  intro hmem
  rcases globalFreshNameAux_not_mem_or_all_mem name names 0 names.length with
    hnotmem | hall
  · exact hnotmem hmem
  · have hsubset :
        ∀ x ∈ (List.range (names.length + 1)).map
            (fun k => name ++ globalApostrophes k), x ∈ names := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_range] at hk
      simpa using hall k (by omega)
    have hnodup :
        ((List.range (names.length + 1)).map
          (fun k => name ++ globalApostrophes k)).Nodup :=
      List.Pairwise.map (fun k => name ++ globalApostrophes k)
        (fun left right hne heq =>
          hne (append_globalApostrophes_injective name heq))
        List.nodup_range
    have hle := List.Nodup.length_le_of_subset hnodup hsubset
    simp at hle
    omega

/-! Counterpart of Cake's `fresh_name_correct'`
    (`pan_globalsProofScript.sml:1003`): a name chosen fresh for `names` is
    also absent from any list whose members all lie in `names`. -/
theorem globalFreshName_not_mem_of_subset [BEq String] [LawfulBEq String]
    (name : String) (names names' : List String)
    (hsubset : ∀ candidate, candidate ∈ names' → candidate ∈ names) :
    globalFreshName name names ∉ names' := by
  intro hmem
  exact globalFreshName_not_mem name names (hsubset _ hmem)
/-- Maximum `String.length` over a list of names; used only to justify
    termination of the exact `fresh_name` port below. -/
def maxNameLength : List String → Nat
  | [] => 0
  | name :: names => max name.length (maxNameLength names)

theorem length_le_maxNameLength {name : String} {names : List String}
    (hmem : name ∈ names) : name.length ≤ maxNameLength names := by
  induction names with
  | nil => cases hmem
  | cons head tail ih =>
      rw [maxNameLength]
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst hhead
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

/-- Qualified HOL port of Cake's `fresh_name` (`pan_globalsScript.sml:55`):
    while the candidate is already a member of `names`, append one apostrophe
    and retry.  The Lean clauses match HOL's exactly --
    `if name ∈ names then freshNameHOL (name ++ "'") names else name` versus
    `if MEM name names then fresh_name (strcat name «'») names else name` --
    with `∈` being `String`/list equality and `++`/`strcat` the same
    one-character append.  Termination is proved with a Flapjack-specific
    measure (`maxNameLength`); HOL uses a `strlen`/`MAX_SET` measure, but the
    measure is not operational, and `String.length`/`strlen` occur only there,
    never in the result.  The sole operational difference is the name carrier:
    production `String` versus HOL `mlstring`.

    `name` is byte-observable: the generated name crosses the compiler
    boundary, and the same-module witness `holMlStringWitness_freshNameHOL`
    establishes `NameRanged (freshNameHOL name names)` from the input premise
    `NameRanged name` (only apostrophes are appended).  The executed path
    supplies byte-ranged seeds: `globalCompile` uses `freshNameHOL "" names` and
    `freshNameHOL "vn'" (resultName :: names)`, and `globalNewMainName` uses the
    literal `"main"`.  `names : List String` represents the HOL `mlstring list`
    names and is classified `equality/map-key-only`: it is used only for
    membership equality, never inspected, and is never byte-observable.  This is
    consistent with the `names` classification already reviewed for
    `freshNameHOL_not_mem_hol`/`freshNameHOL_not_mem_of_subset_hol`.  Direct HOL
    rows are in `scripts/hol-probes/pan_globals_fresh_name_probe.out`; Lean rows
    and the byte-rangedness guard are in
    `Flapjack/Test/PanGlobalsNameByteRangedParity.lean`. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "fresh_name_def"
  (names_as_string := [name, names]) (names_as_string_boundary := [name])]
def freshNameHOL (name : String) (names : List String) : String :=
  if name ∈ names then freshNameHOL (name ++ "'") names else name
termination_by 1 + maxNameLength names - name.length
decreasing_by
  simp_wf
  have hmem : name ∈ names := ‹name ∈ names›
  have hle := length_le_maxNameLength hmem
  have hone : ("'" : String).length = 1 := rfl
  rw [hone]
  omega

/-- Untagged helper: the source-shaped theorem that a name returned by the
    fresh-name search is not a member of the search list. This is the internal
    workhorse used by `globalNewMainName`; the `@[hol]`-tagged exact port of
    Cake's `fresh_name_correct`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:993`) lives in the HOL
    proof counterpart `Flapjack/Pancake/Proofs/PanGlobals.lean`
    (`freshNameHOL_not_mem_hol`), per the HOL-script placement rule. -/
theorem freshNameHOL_not_mem (name : String) (names : List String) :
    freshNameHOL name names ∉ names := by
  fun_induction freshNameHOL name names with
  | case1 name names ih => exact ih
  | case2 name names => assumption

def globalShapeVal (context : GlobalPassContext α) : Shape → Exp α
  | .one => .const (context.fromNat 0)
  | .named _ => .const (context.fromNat 0)
  | .comb shapes => .rStruct (shapes.map (globalShapeVal context))
termination_by shape => sizeOf shape

def globalCompileProg [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : Prog α → Prog α
  | .dec name shape value body =>
      .dec name shape (globalCompileExp context value)
        (globalCompileProg context body)
  | .assign .global name value =>
      match lookupInfo name context.globals with
      | some (_, address) =>
          .store (.op .sub [.topAddr, .const address])
            (globalCompileExp context value)
      | none => .skip
  | .assign .local name value =>
      .assign .local name (globalCompileExp context value)
  | .primitive name operator arguments =>
      .primitive name operator (globalCompileExpList context arguments)
  | .store address value =>
      .store (globalCompileExp context address) (globalCompileExp context value)
  | .store32 address value =>
      .store32 (globalCompileExp context address) (globalCompileExp context value)
  | .storeByte address value =>
      .storeByte (globalCompileExp context address) (globalCompileExp context value)
  | .seq first second =>
      .seq (globalCompileProg context first) (globalCompileProg context second)
  | .ite condition thenBranch elseBranch =>
      .ite (globalCompileExp context condition)
        (globalCompileProg context thenBranch) (globalCompileProg context elseBranch)
  | .while condition body =>
      .while (globalCompileExp context condition) (globalCompileProg context body)
  | .call info function arguments =>
      let compiledArguments := globalCompileExpList context arguments
      match info with
        | none => .call none function compiledArguments
        | some (none, none) =>
            .call (some (none, none)) function compiledArguments
        | some (none, some (exception, handlerVar, handler)) =>
            .call (some (none, some (exception, handlerVar,
              globalCompileProg context handler))) function compiledArguments
        | some (some (.local, name), none) =>
            .call (some (some (.local, name), none)) function compiledArguments
        | some (some (.local, name), some (exception, handlerVar, handler)) =>
            .call (some (some (.local, name), some (exception, handlerVar,
              globalCompileProg context handler))) function compiledArguments
        | some (some (.global, name), none) =>
            match lookupInfo name context.globals with
            | some (shape, address) =>
                .decCall "" shape function compiledArguments
                  (.store (.op .sub [.topAddr, .const address])
                    (.var .local ""))
            | none =>
                .call (some (none, none)) function compiledArguments
        | some (some (.global, name), some (exception, handlerVar, handler)) =>
            match lookupInfo name context.globals with
            | some (shape, address) =>
                let compiledHandlerProgram := globalCompileProg context handler
                let names := handlerVar :: freeVarIds compiledHandlerProgram ++
                  compiledArguments.flatMap expLocalVars
                let resultName := freshNameHOL "" names
                /- Cake's `compile_def` uses the fixed seed `"vn'"` for its
                   handler flag, independently of the fresh result name. -/
                let flagName := freshNameHOL "vn'" (resultName :: names)
                let handlerBody :=
                  .seq compiledHandlerProgram
                    (.assign .local flagName (.const (context.fromNat 1)))
                let callInfo := some (some (.local, resultName),
                  some (exception, handlerVar, handlerBody))
                let callProgram : Prog α :=
                  .call callInfo function compiledArguments
                let storeAddress : Exp α :=
                  .op .sub [.topAddr, .const address]
                .dec resultName shape (globalShapeVal context shape)
                  (.dec flagName .one (.const (context.fromNat 0))
                    (.seq callProgram
                      (.ite (.var .local flagName) .skip
                        (.store storeAddress
                          (.var .local resultName)))))
            | none =>
                .call (some (none, some (exception, handlerVar,
                  globalCompileProg context handler))) function compiledArguments
  | .decCall name shape function arguments body =>
      .decCall name shape function (globalCompileExpList context arguments)
        (globalCompileProg context body)
  | .extCall function configuration configurationLength array arrayLength =>
      .extCall function (globalCompileExp context configuration)
        (globalCompileExp context configurationLength) (globalCompileExp context array)
        (globalCompileExp context arrayLength)
  | .raise exception value => .raise exception (globalCompileExp context value)
  | .return value => .return (globalCompileExp context value)
  | .shMemLoad size kind name address =>
      match kind, lookupInfo name context.globals with
      | .local, _ =>
          .shMemLoad size .local name (globalCompileExp context address)
      | .global, some (.one, globalAddress) =>
          let localName := name ++ globalApostrophes 1
          .dec name .one (globalCompileExp context address)
            (.dec localName .one (.const (context.fromNat 0))
              (.seq
                (.shMemLoad size .local localName (.var .local name))
                (.store (.op .sub [.topAddr, .const globalAddress])
                  (.var .local localName))))
      | .global, _ => .skip
  | .shMemStore size address value =>
      .shMemStore size (globalCompileExp context address) (globalCompileExp context value)
  | program => program
termination_by program => sizeOf program

/-! The declaration-order and function-permutation helpers used by
    CakeML's `pan_to_target`.  Keeping these transformations separate from
    global allocation makes their name-preservation contracts reusable by the
    target-facing pipeline. -/

/-- Exact HOL port of Cake's `fperm_name_def`
    (`cakeml/pancake/pan_globalsScript.sml:184-189`):

    HOL `fperm_name f g h = if f = h then g else if g = h then f else h`.

    HOL's `fperm_name_def` carries no type annotation, so HOL generalizes the
    constant to the polymorphic `'a -> 'a -> 'a -> 'a` (HOL equality is defined
    on every type, with no typeclass side condition).  The faithful Lean port is
    therefore generic in `α` with the computable equality instance
    `[DecidableEq α]`, following the tagged generic-`α` HOL ports `afindi_def`
    (`Flapjack/Pancake/PanStructs.lean:20-21`) and `distinct_lists_def`
    (`Flapjack/Pancake/PanCommon.lean:24-25`).  The clauses, branch order, the
    comparison `=` and the result names match HOL exactly with no side
    condition.  Call sites use this definition directly at `α := String`
    (`FunName`), so no `String`-specialized wrapper remains.  Direct
    HOL/Lean edge-case fixtures: `scripts/hol-probes/pan_globals_fperm_name_probe.out`
    and `Flapjack/Test/PanGlobalsFpermNameParity.lean`. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "fperm_name_def"]
def fpermName {α : Type u} [DecidableEq α] (f g h : α) : α :=
  if f = h then g else if g = h then f else h

section FpermExact

open Flapjack.Pancake.PanLang (MlS ProgHOL DeclHOL)

/-! Exact structural-renaming ports over the reviewed MlString/word-indexed
    `ProgHOL`/`DeclHOL` carriers (bead `flapjack-pxn.18.3.5.8.20`).  HOL's
    `fperm_def`/`fperm_decs_def` (`cakeml/pancake/pan_globalsScript.sml:191-214`,
    `:216-221`) recurse only on program/declaration structure, so they transfer
    constructor-for-constructor to `ProgHOL width` / `List (DeclHOL width)`; the
    name rename is the already-reviewed exact polymorphic `fpermName` above.
    The former generic-carrier `globalRenameProg`/`globalRenameDecls`
    production analogues were retired; these exact twins are the reviewed
    ports of the same HOL definitions. -/

/-- Exact port of HOL `fperm_def` (`cakeml/pancake/pan_globalsScript.sml:191-214`)
    over the reviewed word-indexed `ProgHOL width` carrier.

    The seven equations match HOL clause-for-clause: `Dec`, `Seq`, `If`,
    `While`, `Call` (recursing into the optional exception-handler program and
    renaming the call name with the exact `fpermName`), `DecCall` (renaming the
    callee and recursing into the body), and the identity default.  The `Call`
    metadata nesting
    `Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width))`
    matches HOL
    `(((varkind # varname) option # ((eid # varname # prog) option)) option)`
    constructor-for-constructor.  Every expression payload is left untouched,
    exactly as in HOL. The word qualifier records the positive HOL type-indexed
    word dimension as `width` under `[NeZero width]`; native names and all
    constructor/option/list structure are unchanged. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "fperm_def"
  (words_as_type_indexed_bitvec)]
def fpermHOL {width : Nat} [NeZero width] (f g : MlS) : ProgHOL width → ProgHOL width
  | .dec name shape value body => .dec name shape value (fpermHOL f g body)
  | .seq first second => .seq (fpermHOL f g first) (fpermHOL f g second)
  | .ite condition thenBranch elseBranch =>
      .ite condition (fpermHOL f g thenBranch) (fpermHOL f g elseBranch)
  | .while condition body => .while condition (fpermHOL f g body)
  | .call info name args =>
      .call (match info with
             | none => none
             | some (kindOpt, handlerOpt) =>
                 some (kindOpt, match handlerOpt with
                               | none => none
                               | some (eid, binding, handler) =>
                                   some (eid, binding, fpermHOL f g handler)))
        (fpermName f g name) args
  | .decCall name shape function args body =>
      .decCall name shape (fpermName f g function) args (fpermHOL f g body)
  | program => program
termination_by program => sizeOf program
decreasing_by
  all_goals decreasing_trivial

/-- Exact port of HOL `fperm_decs_def`
    (`cakeml/pancake/pan_globalsScript.sml:216-221`) over the reviewed
    word-indexed `DeclHOL width` carrier.  The three equations match HOL
    clause-for-clause: `[]`, `Function fi :: decs` (renaming `fi.name` with the
    exact `fpermName` and `fi.body` with the exact `fpermHOL`), and
    `d :: decs` leaving every other declaration in place. The word qualifier
    records only the positive type-indexed word dimension of the declaration
    and program payloads; every other function field is unchanged. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "fperm_decs_def"
  (words_as_type_indexed_bitvec)]
def fpermDecsHOL {width : Nat} [NeZero width] (f g : MlS) :
    List (DeclHOL width) → List (DeclHOL width)
  | [] => []
  | .function declaration :: declarations =>
      .function { declaration with
        name := fpermName f g declaration.name
        body := fpermHOL f g declaration.body } ::
        fpermDecsHOL f g declarations
  | declaration :: declarations =>
      declaration :: fpermDecsHOL f g declarations
termination_by declarations => sizeOf declarations
decreasing_by
  all_goals decreasing_trivial

end FpermExact

/-! Cake's polymorphic `fperm_name` (`pan_globalsScript.sml:184`) is the
    reviewed exact port `fpermName` above; its `cancel`/`cong` lemmas are the
    tagged `fpermName_cancel`/`fpermName_cong` in the HOL proof counterpart
    `Flapjack/Pancake/Proofs/PanGlobals.lean`.  Call sites use `fpermName`
    directly at `α := String`, so no `String`-specialized wrapper remains.
    Direct HOL/Lean edge-case fixtures:
    `scripts/hol-probes/pan_globals_fperm_name_probe.out` and
    `Flapjack/Test/PanGlobalsFpermNameParity.lean`. -/


section FpermBridge

open Flapjack.Pancake.PanLang (MlS ProgHOL DeclHOL progOfHOL declOfHOL funDeclOfHOL)
open Flapjack.Basis.Pure.MlString

/-- `toStringOfBytes` is injective on the exact `MlString` carrier: the byte
    codec reads each 8-bit character back exactly, so `ofString` is a
    left-inverse. -/
theorem toStringOfBytes_injective : Function.Injective toStringOfBytes := by
  intro left right h
  have := congrArg ofString h
  simpa [ofString_toStringOfBytes] using this

end FpermBridge






/-! Counterpart of Cake's `exceptions_append`
    (`pan_globalsProofScript.sml:2507`): the exception table distributes over
    list append. -/
theorem exceptionEntries_cons (declaration : Decl α) (declarations : List (Decl α)) :
    exceptionEntries (declaration :: declarations) =
      (match declaration with
       | .exnDecl exception shape =>
           (exception, shape) :: exceptionEntries declarations
       | _ => exceptionEntries declarations) := by
  cases declaration <;> rw [exceptionEntries.eq_def]

theorem exceptionEntries_append (declarations rest : List (Decl α)) :
    exceptionEntries (declarations ++ rest) =
      exceptionEntries declarations ++ exceptionEntries rest := by
  induction declarations with
  | nil => simp [exceptionEntries]
  | cons declaration declarations ih =>
      cases declaration <;> simp [exceptionEntries_cons, ih]

def globalDeclsFilter (predicate : Decl α → Bool) : List (Decl α) → List (Decl α)
  | [] => []
  | declaration :: declarations =>
      if predicate declaration then
        declaration :: globalDeclsFilter predicate declarations
      else globalDeclsFilter predicate declarations
termination_by declarations => sizeOf declarations

theorem globalDeclsFilter_all (predicate : Decl α → Bool)
    (declarations : List (Decl α)) :
    (globalDeclsFilter predicate declarations).all predicate = true := by
  induction declarations with
  | nil => simp [globalDeclsFilter]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : predicate declaration = true
      · rw [if_pos hpred]; simp [hpred, ih]
      · rw [if_neg hpred]; exact ih

/-- Flapjack-specific filter support: membership in a filtered list reports the
    predicate. This generic fact has no separate HOL theorem declaration. -/
theorem mem_globalDeclsFilter {predicate : Decl α → Bool} {declaration : Decl α}
    {declarations : List (Decl α)}
    (hmem : declaration ∈ globalDeclsFilter predicate declarations) :
    predicate declaration = true := by
  induction declarations with
  | nil => rw [globalDeclsFilter.eq_def] at hmem; simp at hmem
  | cons head tail ih =>
      simp only [globalDeclsFilter] at hmem
      by_cases hpred : predicate head = true
      · simp [hpred] at hmem
        rcases hmem with heq | htail
        · subst heq; exact hpred
        · exact ih htail
      · simp [hpred] at hmem
        exact ih hmem

def globalDeclIsName : Decl α → Bool
  | .name _ _ => true
  | _ => false

def globalDeclIsException : Decl α → Bool
  | .exnDecl _ _ => true
  | _ => false

def globalDeclIsGlobal : Decl α → Bool
  | .decl _ _ _ => true
  | _ => false

def globalDeclIsFunction : Decl α → Bool
  | .function _ => true
  | _ => false


/-! Direct source-shaped counterparts of the declaration predicates from
    `panLangScript.sml:234-249`.  The global-pass predicates above are kept
    as its existing pass-facing names; these names retain the source API. -/
def isDecl : Decl α → Bool
  | .decl _ _ _ => true
  | _ => false

def isExnDecl : Decl α → Bool
  | .exnDecl _ _ => true
  | _ => false

def isName : Decl α → Bool
  | .name _ _ => true
  | _ => false

/-- Flapjack-only constructor projection used to reuse the exact HOL
`size_of_eids_def`.  The source definition observes only whether a declaration
is `ExnDecl`; the generic production payload, names, and shapes are discarded
here and are not being claimed as HOL carriers. -/
def declClassViewHOL (declaration : Decl α) :
    Flapjack.Pancake.PanLang.DeclHOL 1 :=
  match declaration with
  | .exnDecl _ _ =>
      .exnDecl (Flapjack.Basis.Pure.MlString.ofString "") .one
  | _ =>
      .name (Flapjack.Basis.Pure.MlString.ofString "") []

/-- Count exception declarations by applying the reviewed HOL definition to a
constructor-only view of production declarations.  This does not make the
generic `Decl α` carrier an exact HOL port.  Also, compiler exception-table
generation uses `crepGetEidsFromDecls` directly; this helper is currently used
for proof-side size facts, not by that executed path. -/
def sizeOfEids (declarations : List (Decl α)) : Nat :=
  Flapjack.Pancake.PanLang.sizeOfEidsHOL (declarations.map declClassViewHOL)


/-- The cons equation for `sizeOfEids`, stated as an `if` on `isExnDecl`. -/
theorem sizeOfEids_cons (declaration : Decl α) (declarations : List (Decl α)) :
    sizeOfEids (declaration :: declarations) =
      if isExnDecl declaration then 1 + sizeOfEids declarations
      else sizeOfEids declarations := by
  unfold sizeOfEids
  rw [Flapjack.Pancake.PanLang.sizeOfEidsHOL_eq_filter, List.map_cons,
    List.filter_cons]
  cases declaration <;>
    simp [declClassViewHOL, isExnDecl, Flapjack.Pancake.PanLang.isExnDeclHOL] <;>
      omega


/-! ### Checked codec bridge to the exact `DeclHOL` predicates (bead `flapjack-ni1.1`)

`isDecl`/`isExnDecl`/`isName`/`globalDeclIsFunction` and `sizeOfEids` consume
the production `Decl α`, while their HOL predicates consume exact
`DeclHOL width` (`MlS`/`ShapeHOL`/word-valued expressions). The
`declOfHOL` lemmas below establish a total relation on the exact codec image;
direct call routing is unavailable because the carriers differ and a general
production `Decl α` cannot be encoded as `DeclHOL width` without value and
name assumptions. `sizeOfEids` on arbitrary production declarations therefore
uses its documented constructor-only projection above. These are checked
source-helper bridges, not a claim that `crepGetEidsFromDecls` routes through
`sizeOfEidsHOL`. -/

section DeclHOLBridge

open Flapjack.Pancake.PanLang
  (DeclHOL declOfHOL isDeclHOL isExnDeclHOL isNameHOL isFunctionHOL)

theorem isDecl_declOfHOL {width : Nat} [NeZero width] (declaration : DeclHOL width) :
    isDecl (declOfHOL declaration) = isDeclHOL declaration := by
  cases declaration <;> rfl

theorem isExnDecl_declOfHOL {width : Nat} [NeZero width] (declaration : DeclHOL width) :
    isExnDecl (declOfHOL declaration) = isExnDeclHOL declaration := by
  cases declaration <;> rfl

@[simp] theorem isName_declOfHOL {width : Nat} [NeZero width] (declaration : DeclHOL width) :
    isName (declOfHOL declaration) = isNameHOL declaration := by
  cases declaration <;> rfl

end DeclHOLBridge

section ResortShapeExact

open Flapjack.Pancake.PanLang
  (MlS DeclHOL ShapeHOL functionsHOL isNameHOL isExnDeclHOL isDeclHOL isFunctionHOL
   mlstrAppend)
open Flapjack.Basis.Pure.MlString (MlString ofString toStringOfBytes)

/-!
Exact-carrier ports of the three declaration-list transformations of
Cake's `pan_globals` pass (bead `flapjack-pxn.18.3.5.8.21`). They run over
the reviewed word-indexed `List (DeclHOL width)` carrier and reuse the
already tagged sibling ports
`isNameHOL`/`isExnDeclHOL`/`isDeclHOL`/`isFunctionHOL`
(`panLangScript.sml:234-249`, `:314-317`), `freshNameHOL`
(`fresh_name_def`), and `functionsHOL` (`functions_def`).  The former
generic-carrier `globalResortDecls`/`globalNewMainName`/`globalDeclShapes`
production forms were retired; these exact twins are the reviewed ports of the
same HOL definitions, and the byte-range witnesses live beside them.
-/

/-- Exact port of HOL `resort_decls_def`
    (`cakeml/pancake/pan_globalsScript.sml:179`):

    HOL `resort_decls decs = FILTER is_name decs ++ FILTER is_exn_decl decs ++
    FILTER is_decl decs ++ FILTER is_function decs`.

    The four filters are applied to the same argument, use the tagged
    `isNameHOL`/`isExnDeclHOL`/`isDeclHOL`/`isFunctionHOL` predicates, and are
    concatenated left-to-right in exactly HOL's order.  The carrier is the
    reviewed word-indexed `List (DeclHOL width)` (MlString identifiers,
    word-indexed expressions), so no qualifier applies. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "resort_decls_def"]
def resortDeclsHOL {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) : List (DeclHOL width) :=
  (declarations.filter isNameHOL) ++ (declarations.filter isExnDeclHOL) ++
    (declarations.filter isDeclHOL) ++ (declarations.filter isFunctionHOL)

/-! ### Exact `mlstring`-native `fresh_name` and `new_main_name`

`freshNameHOL` above is the String-backed production rendering of HOL
`fresh_name`, kept under the `names_as_string` qualifier.  Below is the
`mlstring`-native restatement over the exact `MlS` carrier, so that
`newMainNameHOL` is an unqualified exact port of `new_main_name_def` rather than
a computation routed through the String codec. -/

/-- Maximum `MlS` character-list length over a list of names; used only to
    justify termination of the exact `fresh_name` port. -/
def maxMlsLength : List MlS → Nat
  | [] => 0
  | name :: names => max (MlString.explode name).length (maxMlsLength names)

theorem length_le_maxMlsLength {name : MlS} {names : List MlS}
    (hmem : name ∈ names) :
    (MlString.explode name).length ≤ maxMlsLength names := by
  induction names with
  | nil => cases hmem
  | cons head tail ih =>
      rw [maxMlsLength]
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst hhead
        exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih htail) (Nat.le_max_right _ _)

/-- Exact `mlstring`-native port of HOL `pan_globals$fresh_name`
    (`cakeml/pancake/pan_globalsScript.sml:55`):

    HOL `fresh_name name names =
      if MEM name names then fresh_name (strcat name «'») names else name`.

    The clauses match clause for clause over the exact `MlS` carrier: `∈` is
    `mlstring` list equality, `MEM` is list membership, and
    `mlstrAppend name (ofString "'")` is HOL `strcat name «'»`.  HOL's
    non-operational `strlen`/`MAX_SET` measure is replaced by `maxMlsLength`,
    which occurs only in the termination argument, never in the result.  No
    qualifier applies because the carrier is already HOL's `mlstring`. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "fresh_name_def"]
def freshNameMlS (name : MlS) (names : List MlS) : MlS :=
  if name ∈ names then
    freshNameMlS (mlstrAppend name (ofString "'")) names
  else name
termination_by 1 + maxMlsLength names - (MlString.explode name).length
decreasing_by
  simp_wf
  have hmem : name ∈ names := ‹name ∈ names›
  have hle := length_le_maxMlsLength hmem
  have happ :
      (MlString.explode (mlstrAppend name (ofString "'"))).length =
        (MlString.explode name).length + 1 := by
    simp [mlstrAppend, ofString, MlString.explode_implode, List.length_append]
  rw [happ]
  omega

/-- Exact port of HOL `pan_globals$new_main_name`
    (`cakeml/pancake/pan_globalsScript.sml:224`):

    HOL `new_main_name decls = fresh_name «main» (MAP FST (functions decls))`.

    The input is the exact `List (DeclHOL width)`; `functionsHOL` is the tagged
    `mlstring`-keyed port of HOL `functions`, so `(functionsHOL decls).map
    Prod.fst` is exactly `MAP FST (functions decls)`.  The source name is the
    `MlS` literal `«main»` (`ofString "main"`) and the search is the tagged
    exact `freshNameMlS`.  No qualifier applies because every carrier is already
    exact. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "new_main_name_def"]
def newMainNameHOL {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) : MlS :=
  freshNameMlS (ofString "main") ((functionsHOL declarations).map Prod.fst)

/-- Exact port of HOL `dec_shapes_def`
    (`cakeml/pancake/pan_globalsScript.sml:228-234`):

    HOL `dec_shapes (Function _::ds) = dec_shapes ds`,
    `dec_shapes (Decl sh _ _::ds) = sh::dec_shapes ds`,
    `dec_shapes (Name _ _::ds) = dec_shapes ds`,
    `dec_shapes (ExnDecl _ _::ds) = dec_shapes ds`,
    `dec_shapes [] = []`.

    The clauses match HOL's clause order and shape selection exactly: only
    `Decl` contributes its shape, and function/name/exception declarations are
    skipped.  The carrier is `List (DeclHOL width)` and the result is
    `List ShapeHOL`, so no qualifier applies. -/
@[hol "cakeml/pancake/pan_globalsScript.sml" "dec_shapes_def"]
def decShapesHOL {width : Nat} [NeZero width] :
    List (DeclHOL width) → List ShapeHOL
  | [] => []
  | .function _ :: declarations => decShapesHOL declarations
  | .decl shape _ _ :: declarations => shape :: decShapesHOL declarations
  | .name _ _ :: declarations => decShapesHOL declarations
  | .exnDecl _ _ :: declarations => decShapesHOL declarations

end ResortShapeExact


/-! ## `holMlStringWitness_*`: same-module byte-boundary witnesses

The `names_as_string` qualifier (`Flapjack/HolRef.lean`) records Lean `String`
fields standing for HOL `mlstring` names.  Declarations tagged with it are
expected to carry a checked `holMlStringWitness_*` witness **in the same
module**, establishing the byte-range condition of the generated names.  HOL
`mlstring` is a list of 8-bit characters, so a generated name must never contain
a code point `>= 256`; `Flapjack.Pancake.PanLang.NameRanged` is exactly that
condition (and is definitionally the parser-chain `StringByteRanged`).

The witnesses below are premise-aware: `freshNameHOL`, `globalFreshNameAux`, and
`globalFreshName` may append apostrophes to an input name, so they preserve
byte-rangedness only when the input name is byte-ranged. `globalNewMainName`
starts from the literal `"main"` and therefore needs no premise. The witness
for `freshNameHOL` supports its names-only `names_as_string` tag; the
`globalNewMainName` witness remains a Flapjack production byte-safety fact and
does not establish that its generic declaration carrier matches HOL. -/

private theorem nameRanged_append {s₁ s₂ : String}
    (h₁ : Flapjack.Pancake.PanLang.NameRanged s₁)
    (h₂ : Flapjack.Pancake.PanLang.NameRanged s₂) :
    Flapjack.Pancake.PanLang.NameRanged (s₁ ++ s₂) := by
  intro c hc
  rw [String.toList_append, List.mem_append] at hc
  rcases hc with h | h
  · exact h₁ c h
  · exact h₂ c h

private theorem nameRanged_quote : Flapjack.Pancake.PanLang.NameRanged "'" := by
  unfold Flapjack.Pancake.PanLang.NameRanged
  decide

private theorem globalApostrophes_nameRanged (count : Nat) :
    Flapjack.Pancake.PanLang.NameRanged (globalApostrophes count) := by
  induction count with
  | zero =>
      simp [globalApostrophes, Flapjack.Pancake.PanLang.NameRanged]
  | succ count ih =>
      rw [globalApostrophes]
      exact nameRanged_append nameRanged_quote ih

/-- Witness: the source-shaped HOL `fresh_name` port preserves byte-rangedness
    of the input name (it only appends apostrophes). -/
theorem holMlStringWitness_freshNameHOL (name : String) (names : List String)
    (h : Flapjack.Pancake.PanLang.NameRanged name) :
    Flapjack.Pancake.PanLang.NameRanged (freshNameHOL name names) := by
  fun_induction freshNameHOL name names with
  | case1 name names ih =>
      exact ih (nameRanged_append h nameRanged_quote)
  | case2 name names => exact h

/-- Witness: the fuel-bounded production fresh-name search preserves
    byte-rangedness of the input name. -/
theorem holMlStringWitness_globalFreshNameAux [BEq String] (name : String)
    (h : Flapjack.Pancake.PanLang.NameRanged name) (names : List String)
    (candidate fuel : Nat) :
    Flapjack.Pancake.PanLang.NameRanged
      (globalFreshNameAux name names candidate fuel) := by
  induction fuel generalizing candidate with
  | zero =>
      rw [globalFreshNameAux]
      exact nameRanged_append h (globalApostrophes_nameRanged candidate)
  | succ fuel ih =>
      rw [globalFreshNameAux]
      by_cases hc : names.contains (name ++ globalApostrophes candidate) = true
      · rw [if_pos hc]
        exact ih (candidate + 1)
      · rw [if_neg hc]
        exact nameRanged_append h (globalApostrophes_nameRanged candidate)

/-- Witness: production `globalFreshName` preserves byte-rangedness of the input
    name. -/
theorem holMlStringWitness_globalFreshName [BEq String] (name : String)
    (h : Flapjack.Pancake.PanLang.NameRanged name) (names : List String) :
    Flapjack.Pancake.PanLang.NameRanged (globalFreshName name names) :=
  holMlStringWitness_globalFreshNameAux name h names 0 names.length

/-! Counterpart of Cake's `exceptions_FILTER_is_function`
    (`pan_globalsProofScript.sml:2515`). -/
theorem exceptionEntries_globalDeclsFilter_of_true
    {predicate : Decl α → Bool}
    (hexn : ∀ exception shape, predicate (.exnDecl exception shape) = true)
    (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter predicate declarations) =
      exceptionEntries declarations := by
  induction declarations with
  | nil => simp [globalDeclsFilter, exceptionEntries]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : predicate declaration = true
      · rw [if_pos hpred]
        cases declaration <;> simp_all [exceptionEntries_cons]
      · rw [if_neg hpred]
        cases declaration <;> simp_all [exceptionEntries_cons]

theorem exceptionEntries_globalDeclsFilter_of_false
    {predicate : Decl α → Bool}
    (hexn : ∀ exception shape, predicate (.exnDecl exception shape) = false)
    (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter predicate declarations) = [] := by
  induction declarations with
  | nil => simp [globalDeclsFilter, exceptionEntries]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : predicate declaration = true
      · rw [if_pos hpred]
        cases declaration <;> simp_all [exceptionEntries_cons]
      · rw [if_neg hpred]
        cases declaration <;> simp_all

theorem exceptionEntries_filter_function (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter globalDeclIsFunction declarations) = [] :=
  exceptionEntries_globalDeclsFilter_of_false (fun _ _ => rfl) declarations

theorem exceptionEntries_filter_not_function (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter (fun declaration => !globalDeclIsFunction declaration)
      declarations) = exceptionEntries declarations :=
  exceptionEntries_globalDeclsFilter_of_true (fun _ _ => rfl) declarations

theorem exceptionEntries_filter_exception (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter globalDeclIsException declarations) =
      exceptionEntries declarations :=
  exceptionEntries_globalDeclsFilter_of_true (fun _ _ => rfl) declarations

theorem exceptionEntries_filter_name (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter globalDeclIsName declarations) = [] :=
  exceptionEntries_globalDeclsFilter_of_false (fun _ _ => rfl) declarations

theorem exceptionEntries_filter_global (declarations : List (Decl α)) :
    exceptionEntries (globalDeclsFilter globalDeclIsGlobal declarations) = [] :=
  exceptionEntries_globalDeclsFilter_of_false (fun _ _ => rfl) declarations

/-! Predicate helpers behind Cake's `not_is_function`
    (`pan_globalsProofScript.sml:2527`): name, value, and exception
    declarations are never function declarations. The exact HOL-shaped
    conjunction is the `@[hol]`-tagged `not_is_function` in the proof
    counterpart `Flapjack.Pancake.Proofs.PanGlobals`. -/
theorem isName_not_function (declaration : Decl α) :
    isName declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [isName, globalDeclIsFunction]

theorem isDecl_not_function (declaration : Decl α) :
    isDecl declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [isDecl, globalDeclIsFunction]

theorem isExnDecl_not_function (declaration : Decl α) :
    isExnDecl declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [isExnDecl, globalDeclIsFunction]

/-! Counterparts of Cake's `functions_filter_nil`, `functions_FILTER_exn_decl`,
    and `functions_FILTER_is_name` (`pan_globalsProofScript.sml:2967, 2042,
    2049`): filtering by a predicate that excludes function declarations
    leaves an empty function table. -/
theorem functions_globalDeclsFilter_nil_of_predicate
    (predicate : Decl α → Bool)
    (hpredicate : ∀ declaration, predicate declaration = true →
      globalDeclIsFunction declaration = false)
    (declarations : List (Decl α)) :
    functions (globalDeclsFilter predicate declarations) = [] := by
  induction declarations with
  | nil => simp [globalDeclsFilter, functions, functionEntries]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : predicate declaration = true
      · rw [if_pos hpred]
        have hnotfun := hpredicate declaration hpred
        cases declaration <;> simp [globalDeclIsFunction] at hnotfun
        all_goals simp [functions, functionEntries]
        all_goals exact ih
      · rw [if_neg hpred]
        exact ih

theorem functions_globalDeclsFilter_not_function (declarations : List (Decl α)) :
    functions
      (globalDeclsFilter
        (fun declaration => !globalDeclIsFunction declaration) declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _
    (fun declaration hpred => by simpa using hpred) declarations

theorem functions_globalDeclsFilter_exnDecl (declarations : List (Decl α)) :
    functions (globalDeclsFilter isExnDecl declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ isExnDecl_not_function declarations

theorem functions_globalDeclsFilter_isName (declarations : List (Decl α)) :
    functions (globalDeclsFilter isName declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ isName_not_function declarations

theorem globalDeclIsGlobal_not_function (declaration : Decl α) :
    globalDeclIsGlobal declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [globalDeclIsGlobal, globalDeclIsFunction]

theorem globalDeclIsName_not_function (declaration : Decl α) :
    globalDeclIsName declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [globalDeclIsName, globalDeclIsFunction]

theorem globalDeclIsException_not_function (declaration : Decl α) :
    globalDeclIsException declaration = true → globalDeclIsFunction declaration = false := by
  cases declaration <;> simp [globalDeclIsException, globalDeclIsFunction]

theorem functions_globalDeclsFilter_globalName (declarations : List (Decl α)) :
    functions (globalDeclsFilter globalDeclIsName declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ globalDeclIsName_not_function
    declarations

theorem functions_globalDeclsFilter_globalException (declarations : List (Decl α)) :
    functions (globalDeclsFilter globalDeclIsException declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ globalDeclIsException_not_function
    declarations

theorem functions_globalDeclsFilter_isGlobal (declarations : List (Decl α)) :
    functions (globalDeclsFilter globalDeclIsGlobal declarations) = [] :=
  functions_globalDeclsFilter_nil_of_predicate _ globalDeclIsGlobal_not_function
    declarations

theorem functions_globalDeclsFilter_isFunction (declarations : List (Decl α)) :
    functions (globalDeclsFilter globalDeclIsFunction declarations) =
      functions declarations := by
  induction declarations with
  | nil => simp [globalDeclsFilter, functions, functionEntries]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : globalDeclIsFunction declaration = true
      · rw [if_pos hpred]
        cases declaration <;> simp_all [globalDeclIsFunction, functions, functionEntries]
      · rw [if_neg hpred]
        cases declaration <;> simp_all [globalDeclIsFunction, functions, functionEntries]

theorem functions_append (declarations rest : List (Decl α)) :
    functions (declarations ++ rest) = functions declarations ++ functions rest := by
  induction declarations with
  | nil => simp [functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration <;> simp [functions, functionEntries, ih]





def globalFindFunction [BEq String] (name : FunName) :
    List (Decl α) → Option (FunDecl α)
  | [] => none
  | .function declaration :: declarations =>
      if declaration.name == name then some declaration
      else globalFindFunction name declarations
  | _ :: declarations => globalFindFunction name declarations
termination_by declarations => sizeOf declarations

def globalCollect [Add α] [Mul α] (context : GlobalPassContext α) :
    List (Decl α) → GlobalPassContext α
  | [] => context
  | .decl shape name _ :: declarations =>
      let address := globalAddress context shape
      globalCollect { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address } declarations
  | _ :: declarations => globalCollect context declarations

def globalCompileDecls [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      .function { declaration with body := globalCompileProg context declaration.body } ::
        globalCompileDecls context declarations
  | .exnDecl exception shape :: declarations =>
      .exnDecl exception shape :: globalCompileDecls context declarations
  | _ :: declarations => globalCompileDecls context declarations

def globalCompileInitializers [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : List (Decl α) → List (Prog α)
  | [] => []
  | .decl shape _name value :: declarations =>
      /- `pan_globals$compile_decs` computes this declaration's address from
         the context before recursing.  In particular, duplicate names must
         retain the address of each declaration's own store; looking them up
         in the final map would incorrectly give every initializer the last
         declaration's address. -/
      let address := globalAddress context shape
      let nextContext := { context with
        globals := (_name, (shape, address)) :: context.globals
        globalsSize := address }
      let initializer :=
        .store (.op .sub [.topAddr, .const address])
          (globalCompileExp context value)
      initializer :: globalCompileInitializers nextContext declarations
  | _ :: declarations => globalCompileInitializers context declarations

/-! The four-result shape of Pancake's `pan_globals$compile_decs_def`
    (`pan_globalsScript.sml:160`).  Global declarations become initializer
    stores, while functions and exception declarations remain in their own
    source-order lists; the collected context carries the updated addresses. -/
structure GlobalCompileDecsResult (α : Type u) where
  initializers : List (Prog α)
  functions : List (Decl α)
  exceptions : List (Decl α)
  context : GlobalPassContext α

/-! Flapjack-specific context-threading counterpart of HOL
    `pan_globals$compile_decs_def` (`pan_globalsScript.sml:160-176`): each
    function body is compiled using the context at its position in the list.
    This declaration is not tagged as an exact port. Unlike HOL's fixed word
    operations, it accepts arbitrary `bytesInWord`/`fromNat` context fields,
    `[Add α]`/`[Mul α]`, and potentially non-lawful `[BEq String]`.
    Bead `flapjack-pxn.18.5.2.20.1.1` tracks the canonical-word-context port;
    production `globalCompileDecs` now calls this threaded implementation. -/
def globalCompileDecsThreaded [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) : List (Decl α) → GlobalCompileDecsResult α
  | [] => { initializers := [], functions := [], exceptions := [], context := context }
  | .function declaration :: declarations =>
      let rest := globalCompileDecsThreaded context declarations
      { initializers := rest.initializers
        functions := .function { declaration with
            body := globalCompileProg context declaration.body } :: rest.functions
        exceptions := rest.exceptions
        context := rest.context }
  | .exnDecl exception shape :: declarations =>
      let rest := globalCompileDecsThreaded context declarations
      { rest with exceptions := .exnDecl exception shape :: rest.exceptions }
  | .name _ _ :: declarations => globalCompileDecsThreaded context declarations
  | .decl shape name value :: declarations =>
      let address := globalAddress context shape
      let nextContext := { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address }
      let rest := globalCompileDecsThreaded nextContext declarations
      { initializers :=
          .store (.op .sub [.topAddr, .const address])
            (globalCompileExp context value) :: rest.initializers
        functions := rest.functions
        exceptions := rest.exceptions
        context := rest.context }

theorem globalCompileDecsThreaded_functions_all_isFunction [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    (globalCompileDecsThreaded context declarations).functions.all globalDeclIsFunction =
      true := by
  induction declarations generalizing context with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [globalCompileDecsThreaded, List.all_cons, globalDeclIsFunction,
            Bool.true_and]
          exact ih context
      | decl shape name value =>
          simp only [globalCompileDecsThreaded]
          exact ih _
      | exnDecl exception shape =>
          simp only [globalCompileDecsThreaded]
          exact ih context
      | name struct fields =>
          simp only [globalCompileDecsThreaded]
          exact ih context

theorem globalCompileDecsThreaded_functions_eq_nil_of_no_functions
    [BEq String] [Add α] [Mul α] (declarations : List (Decl α)) :
    ∀ context, declarations.all (fun declaration => !globalDeclIsFunction declaration) = true →
      (globalCompileDecsThreaded context declarations).functions = [] := by
  induction declarations with
  | nil => intro context _; rfl
  | cons declaration declarations ih =>
      intro context hnone
      cases declaration with
      | function function =>
          simp [List.all_cons, globalDeclIsFunction] at hnone
      | decl shape name value =>
          simp only [List.all_cons, Bool.and_eq_true] at hnone
          simp only [globalCompileDecsThreaded]
          exact ih _ hnone.2
      | exnDecl exception shape =>
          simp only [List.all_cons, Bool.and_eq_true] at hnone
          simp only [globalCompileDecsThreaded]
          exact ih _ hnone.2
      | name struct fields =>
          simp only [List.all_cons, Bool.and_eq_true] at hnone
          simp only [globalCompileDecsThreaded]
          exact ih _ hnone.2

/-- Flapjack-specific (untagged) append law for the context-threading pass:
    appending two declaration lists appends the three output lists and runs the
    second list under the context reached by the first. -/
theorem globalCompileDecsThreaded_append [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (decs rest : List (Decl α)) :
    globalCompileDecsThreaded context (decs ++ rest) =
      let first := globalCompileDecsThreaded context decs
      let second := globalCompileDecsThreaded first.context rest
      { initializers := first.initializers ++ second.initializers
        functions := first.functions ++ second.functions
        exceptions := first.exceptions ++ second.exceptions
        context := second.context } := by
  induction decs generalizing context with
  | nil => simp [globalCompileDecsThreaded]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [List.cons_append, globalCompileDecsThreaded]
          rw [ih context]
      | decl shape name value =>
          simp only [List.cons_append, globalCompileDecsThreaded]
          rw [ih _]
      | exnDecl exception shape =>
          simp only [List.cons_append, globalCompileDecsThreaded]
          rw [ih _]
      | name struct fields =>
          simp only [List.cons_append, globalCompileDecsThreaded]
          rw [ih context]

def globalCompileDecs [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    GlobalCompileDecsResult α :=
  let collected := globalCollect context declarations
  { initializers := globalCompileInitializers context declarations
    functions := (globalCompileDecsThreaded context declarations).functions
    exceptions := globalDeclsFilter globalDeclIsException
      (globalCompileDecls collected declarations)
    context := collected }

theorem globalCompileDecsThreaded_initializers [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    (globalCompileDecsThreaded context declarations).initializers =
      globalCompileInitializers context declarations := by
  induction declarations generalizing context with
  | nil => simp [globalCompileDecsThreaded, globalCompileInitializers]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp only [globalCompileDecsThreaded, globalCompileInitializers]
          exact ih context
      | decl shape name value =>
          simp only [globalCompileDecsThreaded, globalCompileInitializers]
          congr 1
          exact ih _
      | exnDecl exception shape =>
          simp only [globalCompileDecsThreaded, globalCompileInitializers]
          exact ih context
      | name struct fields =>
          simp only [globalCompileDecsThreaded, globalCompileInitializers]
          exact ih context

theorem globalCompileDecsThreaded_functions_names [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    (functions (globalCompileDecsThreaded context declarations).functions).map
        (fun entry => entry.1) =
      (functions declarations).map (fun entry => entry.1) := by
  induction declarations generalizing context with
  | nil => simp [globalCompileDecsThreaded, functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration with
      | function function =>
          simp [globalCompileDecsThreaded, functions, functionEntries, ih]
      | decl shape name value =>
          simp only [globalCompileDecsThreaded]
          exact ih _
      | exnDecl exception shape =>
          simp only [globalCompileDecsThreaded]
          exact ih context
      | name struct fields =>
          simp only [globalCompileDecsThreaded]
          exact ih context

theorem globalCompileDecsThreaded_functions_all_of_predicate [BEq String] [Add α] [Mul α]
    (declarations : List (Decl α)) (predicate : Decl α → Bool) :
    (∀ context, declarations.all
      (fun declaration => match declaration with
        | .function function =>
            predicate (.function { function with
              body := globalCompileProg context function.body })
        | _ => true) = true) →
    ∀ context, (globalCompileDecsThreaded context declarations).functions.all
      predicate = true := by
  induction declarations with
  | nil => intro _ context; simp [globalCompileDecsThreaded]
  | cons declaration declarations ih =>
      intro hsource context
      cases declaration with
      | function function =>
          have h := hsource context
          simp only [List.all_cons, Bool.and_eq_true] at h
          simp only [globalCompileDecsThreaded, List.all_cons, Bool.and_eq_true]
          exact ⟨h.1, ih (fun ctx => (by
            have h := hsource ctx
            simp only [List.all_cons, Bool.and_eq_true] at h
            exact h.2)) context⟩
      | decl shape name value =>
          simp only [globalCompileDecsThreaded]
          exact ih (fun ctx => (by
            have h := hsource ctx
            simp only [List.all_cons, Bool.and_eq_true] at h
            exact h.2)) _
      | exnDecl exception shape =>
          simp only [globalCompileDecsThreaded]
          exact ih (fun ctx => (by
            have h := hsource ctx
            simp only [List.all_cons, Bool.and_eq_true] at h
            exact h.2)) context
      | name struct fields =>
          simp only [globalCompileDecsThreaded]
          exact ih (fun ctx => (by
            have h := hsource ctx
            simp only [List.all_cons, Bool.and_eq_true] at h
            exact h.2)) context

theorem globalCompileDecsThreaded_exceptions_eq_filter [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (globalCompileDecsThreaded context code).exceptions =
      globalDeclsFilter globalDeclIsException code := by
  induction code generalizing context with
  | nil => simp [globalCompileDecsThreaded, globalDeclsFilter]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [globalCompileDecsThreaded, globalDeclsFilter, globalDeclIsException, ih]

theorem globalDeclsFilter_isDecl_all_not_function [BEq String] [Add α] [Mul α]
    (code : List (Decl α)) :
    (globalDeclsFilter isDecl code).all
      (fun declaration => !globalDeclIsFunction declaration) = true := by
  induction code with
  | nil => simp [globalDeclsFilter]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : isDecl declaration = true
      · rw [if_pos hpred]
        cases declaration <;> simp_all [isDecl, globalDeclIsFunction]
      · rw [if_neg hpred]
        exact ih

/-- HOL-shaped context for `pan_globals$compile_decs_def`
    (`pan_globalsScript.sml:8-14`): the three HOL fields
    `globals`/`globals_size`/`max_globals_size` over a `width`-bit word.

    HOL `globals` is an extensional finite map (`varname |-> shape # 'a word`).
    Here it is rendered by the repository's `FiniteMap` (`α → Option β`), whose
    Lean type also admits lookups with infinite support.  For `compile_exp` this
    is adequate without a finite-support invariant: the HOL `compile_exp` clauses
    consult `globals` only through `FLOOKUP`, and every HOL finite map embeds as
    one such lookup function; on those embedded (HOL-representable) contexts the
    Lean clauses agree clause-for-clause, so the extra infinite-support lookup
    functions do not alter the port.  No cross-system finite-map equivalence is
    claimed beyond that local use.

    HOL word types satisfy `dimindex > 0`; the Lean rendering therefore
    restricts these canonical word defs with `[NeZero width]` rather than
    admitting `width = 0`.  The canonical instances are `width = 8`, `32`, or
    `64`. -/
structure CakeContext (width : Nat) where
  globals : FiniteMap String (Shape × BitVec width)
  globalsSize : BitVec width
  maxGlobalsSize : BitVec width

/-- HOL `bytes_in_word` for `width`-bit words: `n2w (dimindex DIV 8)`. -/
def cakeBytesInWord (width : Nat) : BitVec width := BitVec.ofNat width (width / 8)

/-- The address HOL `compile_decs` assigns to a freshly declared global
    (`pan_globalsScript.sml:162`):
    `globals_size + bytes_in_word * n2w (size_of_shape sh)`. -/
def cakeAddress {width : Nat} (context : CakeContext width) (shape : Shape) :
    BitVec width :=
  context.globalsSize + cakeBytesInWord width * BitVec.ofNat width (Shape.shapeSize shape)

/-- HOL `shape_val` (`panLangScript.sml:190-196`). -/
def cakeShapeVal {width : Nat} (context : CakeContext width) : Shape → Exp (BitVec width)
  | .one => .const (BitVec.ofNat width 0)
  | .named _ => .const (BitVec.ofNat width 0)
  | .comb shapes => .rStruct (shapes.map (cakeShapeVal context))
termination_by shape => sizeOf shape

/-- Interpret a production `GlobalPassContext` over `BitVec width` as a
    canonical HOL-shaped `CakeContext`: the association-list `globals` become a
finite-map lookup through `lookupInfo`, keeping the size fields.  This is
    the production-to-canonical direction of the adapter required by
    `flapjack-pxn.18.5.2.20.2`. The fixed-width executed path calls the (currently untagged)
    `compileDecsCake`; equality of the context field's data representation
    remains to be proved. -/
def cakeContextOfPass [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) : CakeContext width :=
  { globals := fun key => lookupInfo key context.globals
    globalsSize := context.globalsSize
    maxGlobalsSize := context.maxGlobalsSize }

/-- Canonical-word hypothesis for the adapter: the production context uses
    HOL's fixed `bytes_in_word = n2w (dimindex DIV 8)` and `n2w`. -/
def GlobalPassContext.IsCakeCanonical {width : Nat}
    (context : GlobalPassContext (BitVec width)) : Prop :=
  context.bytesInWord = cakeBytesInWord width ∧
    ∀ value : Nat, context.fromNat value = BitVec.ofNat width value

/-- Under the canonical-word hypothesis the production global address
    (`GlobalPassContext`-based) agrees with the canonical HOL address. -/
theorem cakeAddress_ofPass [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width))
    (hcanonical : context.IsCakeCanonical) (shape : Shape) :
    cakeAddress (cakeContextOfPass context) shape = globalAddress context shape := by
  rcases hcanonical with ⟨hbytes, hfrom⟩
  simp [cakeAddress, cakeContextOfPass, globalAddress, hbytes, hfrom]

/-- `cakeContextOfPass` commutes with the `Decl` context update: prepending a
    global to the production association list is exactly `FUPDATE` on the
    extracted finite map. -/
theorem cakeContextOfPass_update [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) (name : String)
    (shape : Shape) (address : BitVec width) :
    cakeContextOfPass { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address }
      = { cakeContextOfPass context with
          globals := FUPDATE (cakeContextOfPass context).globals
            (name, (shape, address))
          globalsSize := address } := by
  simp only [cakeContextOfPass]
  rfl

/-- Explicit-field form of `cakeContextOfPass_update`, convenient for rewriting
    `rw [← ...]` in the full-record adapter. -/
theorem cakeContextOfPass_update_fields [BEq String] {width : Nat}
    (context : GlobalPassContext (BitVec width)) (name : String)
    (shape : Shape) (address : BitVec width) :
    cakeContextOfPass { context with
        globals := (name, (shape, address)) :: context.globals
        globalsSize := address }
      = { globals := FUPDATE (cakeContextOfPass context).globals (name, (shape, address))
          globalsSize := address
          maxGlobalsSize := (cakeContextOfPass context).maxGlobalsSize } := by
  simp only [cakeContextOfPass]
  rfl

/-- Adapter: production `shape_val` agrees with the canonical `cakeShapeVal`
    through `cakeContextOfPass`, under the canonical-word hypothesis. -/
theorem globalShapeVal_cakeShapeVal [BEq String] {width : Nat} [NeZero width]
    (context : GlobalPassContext (BitVec width)) (hcanonical : context.IsCakeCanonical)
    (shape : Shape) :
    globalShapeVal context shape = cakeShapeVal (cakeContextOfPass context) shape := by
  induction shape using cakeShapeVal.induct with
  | case1 => simp only [globalShapeVal, cakeShapeVal, hcanonical.2 0]
  | case2 name => simp only [globalShapeVal, cakeShapeVal, hcanonical.2 0]
  | case3 shapes ih =>
      simp only [globalShapeVal, cakeShapeVal]
      congr 1
      exact List.map_congr_left ih

/-- HOL-shaped output of `compile_decs`. -/
structure CakeCompileDecsResult (width : Nat) where
  initializers : List (Prog (BitVec width))
  functions : List (Decl (BitVec width))
  exceptions : List (Decl (BitVec width))
  context : CakeContext width

theorem globalCompileDecs_preserve_functions [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (functions (globalCompileDecs context code).functions).map
        (fun entry => entry.1) =
      (functions code).map (fun entry => entry.1) := by
  simp only [globalCompileDecs]
  exact globalCompileDecsThreaded_functions_names context code

/-! Counterpart of Cake's `compile_decs_EVERY_is_function`
    (`pan_globalsProofScript.sml:1977`): every declaration the compilation
    pass emits into the function table is itself a function declaration. -/
theorem globalCompileDecs_functions_all_isFunction [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (globalCompileDecs context code).functions.all globalDeclIsFunction = true := by
  simp only [globalCompileDecs]
  exact globalCompileDecsThreaded_functions_all_isFunction context code

/-! Counterpart of Cake's `compile_decs_decls_thm`
    (`pan_globalsProofScript.sml:1967`): a program whose declarations contain
    no functions compiles to an empty function table. -/
theorem globalCompileDecs_functions_eq_nil_of_no_functions [BEq String] [Add α]
    [Mul α] (context : GlobalPassContext α) (code : List (Decl α))
    (hnone : code.all (fun declaration => !globalDeclIsFunction declaration) = true) :
    (globalCompileDecs context code).functions = [] := by
  simp only [globalCompileDecs]
  exact globalCompileDecsThreaded_functions_eq_nil_of_no_functions code context hnone

theorem globalCompileDecs_functions_all_of_predicate [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α))
    (predicate : Decl α → Bool)
    (hsource : ∀ context, code.all
      (fun declaration => match declaration with
        | .function function =>
            predicate (.function { function with
              body := globalCompileProg context function.body })
        | _ => true) = true) :
    (globalCompileDecs context code).functions.all predicate = true := by
  simp only [globalCompileDecs]
  exact globalCompileDecsThreaded_functions_all_of_predicate code predicate
    hsource context

/-! Counterpart of Cake's `compile_decs_exns_are_exns`
    (`pan_globalsProofScript.sml:2448`): the exception table is exactly the
    exception declarations of the source program. -/
theorem globalDeclsFilter_isException_globalCompileDecls [BEq String] [Add α]
    [Mul α] (context : GlobalPassContext α) (declarations : List (Decl α)) :
    globalDeclsFilter globalDeclIsException
        (globalCompileDecls context declarations) =
      globalDeclsFilter globalDeclIsException declarations := by
  induction declarations with
  | nil => simp [globalCompileDecls, globalDeclsFilter]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [globalCompileDecls, globalDeclsFilter, globalDeclIsException, ih]

theorem globalCompileDecs_exceptions_eq_filter [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (globalCompileDecs context code).exceptions =
      globalDeclsFilter globalDeclIsException code := by
  simp only [globalCompileDecs]
  exact globalDeclsFilter_isException_globalCompileDecls
    (globalCollect context code) code

/-! Counterpart of Cake's `compile_decs_FILTER_decs`
    (`pan_globalsProofScript.sml:2822`): filtering the source program down to its
    global declarations leaves the collected context and the initializer stores
    unchanged, and empties the function and exception tables. -/
theorem globalCollect_filter_isDecl [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    globalCollect context (globalDeclsFilter isDecl declarations) =
      globalCollect context declarations := by
  induction declarations generalizing context with
  | nil => simp [globalDeclsFilter, globalCollect]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : isDecl declaration = true
      · rw [if_pos hpred]
        cases declaration with
        | decl shape name value => simp only [globalCollect, ih]
        | function function => simp [isDecl] at hpred
        | exnDecl exception shape => simp [isDecl] at hpred
        | name struct fields => simp [isDecl] at hpred
      · rw [if_neg hpred]
        cases declaration with
        | decl shape name value => simp [isDecl] at hpred
        | function function =>
            conv => rhs; rw [globalCollect.eq_def]
            exact ih context
        | exnDecl exception shape =>
            conv => rhs; rw [globalCollect.eq_def]
            exact ih context
        | name struct fields =>
            conv => rhs; rw [globalCollect.eq_def]
            exact ih context

theorem globalCompileInitializers_filter_isDecl [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    globalCompileInitializers context (globalDeclsFilter isDecl declarations) =
      globalCompileInitializers context declarations := by
  induction declarations generalizing context with
  | nil => simp [globalDeclsFilter, globalCompileInitializers]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : isDecl declaration = true
      · rw [if_pos hpred]
        cases declaration with
        | decl shape name value => simp only [globalCompileInitializers, ih]
        | function function => simp [isDecl] at hpred
        | exnDecl exception shape => simp [isDecl] at hpred
        | name struct fields => simp [isDecl] at hpred
      · rw [if_neg hpred]
        cases declaration with
        | decl shape name value => simp [isDecl] at hpred
        | function function =>
            conv => rhs; rw [globalCompileInitializers.eq_def]
            exact ih context
        | exnDecl exception shape =>
            conv => rhs; rw [globalCompileInitializers.eq_def]
            exact ih context
        | name struct fields =>
            conv => rhs; rw [globalCompileInitializers.eq_def]
            exact ih context

theorem globalCompileDecls_filter_isDecl [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (declarations : List (Decl α)) :
    globalCompileDecls context (globalDeclsFilter isDecl declarations) = [] := by
  induction declarations with
  | nil => simp [globalDeclsFilter, globalCompileDecls]
  | cons declaration declarations ih =>
      simp only [globalDeclsFilter]
      by_cases hpred : isDecl declaration = true
      · rw [if_pos hpred]
        cases declaration with
        | decl shape name value => simp [globalCompileDecls, ih]
        | function function => simp [isDecl] at hpred
        | exnDecl exception shape => simp [isDecl] at hpred
        | name struct fields => simp [isDecl] at hpred
      · rw [if_neg hpred]
        exact ih

theorem globalCompileDecs_filter_isDecl [BEq String] [Add α] [Mul α]
    (context : GlobalPassContext α) (code : List (Decl α)) :
    (globalCompileDecs context (globalDeclsFilter isDecl code)).initializers =
        (globalCompileDecs context code).initializers ∧
      (globalCompileDecs context (globalDeclsFilter isDecl code)).functions = [] ∧
      (globalCompileDecs context (globalDeclsFilter isDecl code)).exceptions = [] ∧
      (globalCompileDecs context (globalDeclsFilter isDecl code)).context =
        (globalCompileDecs context code).context := by
  simp only [globalCompileDecs]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact globalCompileInitializers_filter_isDecl context code
  · exact globalCompileDecsThreaded_functions_eq_nil_of_no_functions
      (globalDeclsFilter isDecl code) context
      (globalDeclsFilter_isDecl_all_not_function code)
  · rw [globalCollect_filter_isDecl, globalCompileDecls_filter_isDecl]
    simp [globalDeclsFilter]
  · exact globalCollect_filter_isDecl context code

theorem globalDecls_all_or_of_all_left (predicate other : Decl α → Bool)
    (declarations : List (Decl α))
    (hall : declarations.all other = true) :
    declarations.all
      (fun declaration => predicate declaration || other declaration) = true := by
  induction declarations with
  | nil => simp
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall ⊢
      obtain ⟨hhead, htail⟩ := hall
      exact ⟨by simp [hhead], ih htail⟩

theorem globalDecls_all_or_of_all_right (predicate other : Decl α → Bool)
    (declarations : List (Decl α))
    (hall : declarations.all predicate = true) :
    declarations.all
      (fun declaration => predicate declaration || other declaration) = true := by
  induction declarations with
  | nil => simp
  | cons declaration declarations ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall ⊢
      obtain ⟨hhead, htail⟩ := hall
      exact ⟨by simp [hhead], ih htail⟩

/-! Counterpart of Cake's `compile_top_only_functions_or_exns`
    (`pan_globalsProofScript.sml:2611`): the declaration list produced by the
    start-function entry point consists only of compiled functions and
    exception declarations. -/
theorem globalCompileDecs_result_all_function_or_exception [BEq String] [Add α]
    [Mul α] (context : GlobalPassContext α) (declarations : List (Decl α))
    (extra : Decl α) (hextra : globalDeclIsFunction extra = true) :
    ((globalCompileDecs context declarations).exceptions ++ [extra] ++
        (globalCompileDecs context declarations).functions).all
      (fun declaration => globalDeclIsFunction declaration ||
        globalDeclIsException declaration) = true := by
  simp only [globalCompileDecs]
  rw [List.all_append, List.all_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact globalDecls_all_or_of_all_left globalDeclIsFunction
      globalDeclIsException _ (globalDeclsFilter_all globalDeclIsException _)
  · simp [hextra]
  · exact globalDecls_all_or_of_all_right globalDeclIsFunction
      globalDeclIsException _
      (globalCompileDecsThreaded_functions_all_isFunction context declarations)


/-! ### Checked exact-carrier bridges for the `pan_globals` declaration-list ports

These `@[simp]` lemmas connect the reviewed exact declaration ports over
`List (DeclHOL width)` to the production predicate/function helpers over
`Decl (BitVec width)` on the exact `declOfHOL` image.  They are source-helper
bridges for the tagged exact twins. -/

section ResortShapeExactBridge

open Flapjack.Pancake.PanLang
  (MlS mlstrAppend DeclHOL declOfHOL funDeclOfHOL isDeclHOL isExnDeclHOL isNameHOL
    isFunctionHOL shapeOfHOL functionsHOL)
open Flapjack.Basis.Pure.MlString (ofString toStringOfBytes)

@[simp] theorem globalDeclIsName_declOfHOL {width : Nat} [NeZero width]
    (declaration : DeclHOL width) :
    globalDeclIsName (declOfHOL declaration) = isNameHOL declaration := by
  cases declaration <;> rfl

@[simp] theorem globalDeclIsException_declOfHOL {width : Nat} [NeZero width]
    (declaration : DeclHOL width) :
    globalDeclIsException (declOfHOL declaration) = isExnDeclHOL declaration := by
  cases declaration <;> rfl

@[simp] theorem globalDeclIsGlobal_declOfHOL {width : Nat} [NeZero width]
    (declaration : DeclHOL width) :
    globalDeclIsGlobal (declOfHOL declaration) = isDeclHOL declaration := by
  cases declaration <;> rfl

@[simp] theorem globalDeclIsFunction_declOfHOL {width : Nat} [NeZero width]
    (declaration : DeclHOL width) :
    globalDeclIsFunction (declOfHOL declaration) = isFunctionHOL declaration := by
  cases declaration <;> rfl

/-- Decoding commutes with `mlstring` concatenation: `toStringOfBytes` reads
    each byte as one character, so it distributes over `mlstrAppend` (`^`). -/
theorem toStringOfBytes_mlstrAppend (left right : MlS) :
    toStringOfBytes (mlstrAppend left right) =
      toStringOfBytes left ++ toStringOfBytes right := by
  cases left with
  | implode leftData =>
    cases right with
    | implode rightData =>
      simp only [mlstrAppend, toStringOfBytes,
        Flapjack.Basis.Pure.MlString.MlString.explode_implode,
        List.map_append, String.ofList_append]

/-- `toStringOfBytes` reflects list membership because it is injective. -/
theorem toStringOfBytes_mem_map_iff (name : MlS) (names : List MlS) :
    toStringOfBytes name ∈ names.map toStringOfBytes ↔ name ∈ names := by
  constructor
  · intro hmem
    obtain ⟨other, hother, heq⟩ := List.mem_map.mp hmem
    rw [← toStringOfBytes_injective heq]
    exact hother
  · intro hmem
    exact List.mem_map.mpr ⟨name, hmem, rfl⟩

/-- The apostrophe literal decodes exactly. -/
@[simp] theorem toStringOfBytes_ofString_quote :
    toStringOfBytes (ofString "'") = "'" :=
  Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes "'" (by decide)

/-- The `main` seed literal decodes exactly. -/
@[simp] theorem toStringOfBytes_ofString_main :
    toStringOfBytes (ofString "main") = "main" :=
  Flapjack.Basis.Pure.MlString.toStringOfBytes_ofString_of_bytes "main" (by decide)

/-- The `mlstring`-native `freshNameMlS` commutes with the byte codec: decoding
    its result is the String-backed `freshNameHOL` on the decoded names. -/
theorem toStringOfBytes_freshNameMlS (name : MlS) (names : List MlS) :
    toStringOfBytes (freshNameMlS name names) =
      freshNameHOL (toStringOfBytes name) (names.map toStringOfBytes) := by
  fun_induction freshNameMlS name names with
  | case1 name hmem ih =>
      rw [freshNameHOL.eq_1,
        if_pos ((toStringOfBytes_mem_map_iff name names).mpr hmem)]
      rw [ih, toStringOfBytes_mlstrAppend, toStringOfBytes_ofString_quote]
  | case2 name hnot =>
      rw [freshNameHOL.eq_1,
        if_neg (fun hmem' => hnot ((toStringOfBytes_mem_map_iff name names).mp hmem'))]

end ResortShapeExactBridge

end Flapjack
