module

public import Flapjack.Pancake.PanLang
public import Flapjack.Pancake.PanLang.Prog
public import Flapjack.Pancake.PanLang.Decl

@[expose] public section

/-!
The `pan_simp` pass from CakeML's Pancake development.

The pass associates sequences to the right while preserving declarations,
branches, loops, calls, and call handlers. It also recognizes the
`AssignCall`/`Return` shape as a tail call. In Pancake, `TailCall` is an
abbreviation for a call with no return information, so no extra AST
constructor is needed here.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-! ## Exact HOL `pan_simpScript.sml` ports

The declarations below are the exact word-indexed renderings of
`cakeml/pancake/pan_simpScript.sml` over the reviewed `ProgHOL`/`DeclHOL`
carriers (`MlS` identifiers, `ShapeHOL` shapes, `ExpHOL` expressions).  HOL
`SmartSeq` is written with an equality test (`if p = Skip`); over a datatype
with decidable equality the pattern-match rendering below is the same
function, clause for clause.  `TailCall trgt args` is `Call NONE trgt args`
and `AssignCall (Local,rv) NONE` is `Call (SOME (SOME (Local,rv), NONE))`. -/

/-- Exact port of HOL `pan_simp$SmartSeq_def` (`pan_simpScript.sml:13`):
`SmartSeq p q = if p = Skip then q else Seq p q`. -/
@[hol "cakeml/pancake/pan_simpScript.sml" "SmartSeq_def"]
def smartSeqHOL {width : Nat} [NeZero width] :
    ProgHOL width → ProgHOL width → ProgHOL width
  | .skip, program => program
  | pre, program => .seq pre program

/-- Exact port of HOL `pan_simp$seq_call_ret_def`
(`pan_simpScript.sml:42-49`): recognize `Seq (AssignCall (Local,rv1) NONE
trgt args) (Return (Var Local rv2))` and, when `rv1 = rv2`, rewrite it to the
tail call `TailCall trgt args`. -/
@[hol "cakeml/pancake/pan_simpScript.sml" "seq_call_ret_def"]
def seqCallRetHOL {width : Nat} [NeZero width] : ProgHOL width → ProgHOL width
  | .seq
      (.call (some (some (.local, returnName), none)) function arguments)
      (.return (.var .local returnedName)) =>
      if returnName = returnedName then
        .call none function arguments
      else
        .seq
          (.call (some (some (.local, returnName), none)) function arguments)
          (.return (.var .local returnedName))
  | program => program

/-- Exact port of HOL `pan_simp$seq_assoc_def` (`pan_simpScript.sml:18-40`):
right-associate sequences, threading the pending prefix `pre` through the
pass. -/
@[hol "cakeml/pancake/pan_simpScript.sml" "seq_assoc_def"]
def seqAssocHOL {width : Nat} [NeZero width] (pre : ProgHOL width) :
    ProgHOL width → ProgHOL width
  | .skip => pre
  | .dec name shape value body =>
      smartSeqHOL pre (.dec name shape value (seqAssocHOL .skip body))
  | .seq first second => seqAssocHOL (seqAssocHOL pre first) second
  | .ite condition thenBranch elseBranch =>
      smartSeqHOL pre (.ite condition (seqAssocHOL .skip thenBranch)
        (seqAssocHOL .skip elseBranch))
  | .while condition body =>
      smartSeqHOL pre (.while condition (seqAssocHOL .skip body))
  | .call info function arguments =>
      let info := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar, seqAssocHOL .skip handler))
      smartSeqHOL pre (.call info function arguments)
  | .decCall name shape function arguments body =>
      smartSeqHOL pre (.decCall name shape function arguments (seqAssocHOL .skip body))
  | .annot _ _ => pre
  | program => smartSeqHOL pre program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-- Exact port of HOL `pan_simp$ret_to_tail_def` (`pan_simpScript.sml:50-66`):
rewrite the `AssignCall`/`Return` tail-call shape throughout the program. -/
@[hol "cakeml/pancake/pan_simpScript.sml" "ret_to_tail_def"]
def retToTailHOL {width : Nat} [NeZero width] : ProgHOL width → ProgHOL width
  | .skip => .skip
  | .dec name shape value body => .dec name shape value (retToTailHOL body)
  | .seq first second =>
      seqCallRetHOL (.seq (retToTailHOL first) (retToTailHOL second))
  | .ite condition thenBranch elseBranch =>
      .ite condition (retToTailHOL thenBranch) (retToTailHOL elseBranch)
  | .while condition body => .while condition (retToTailHOL body)
  | .call info function arguments =>
      let info := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar, retToTailHOL handler))
      .call info function arguments
  | .decCall name shape function arguments body =>
      .decCall name shape function arguments (retToTailHOL body)
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-- Exact port of HOL `pan_simp$compile_def` (`pan_simpScript.sml:68-72`):
`compile p = ret_to_tail (seq_assoc Skip p)`. -/
@[hol "cakeml/pancake/pan_simpScript.sml" "compile_def"]
def panSimpCompileHOL {width : Nat} [NeZero width] (program : ProgHOL width) :
    ProgHOL width :=
  retToTailHOL (seqAssocHOL .skip program)

/-- Exact port of HOL `pan_simp$compile_prog_def` (`pan_simpScript.sml:74-81`):
compile the body of every `Function` declaration and leave all other
declarations unchanged. -/
@[hol "cakeml/pancake/pan_simpScript.sml" "compile_prog_def"]
def panSimpDeclsHOL {width : Nat} [NeZero width] :
    List (DeclHOL width) → List (DeclHOL width)
  | [] => []
  | .function declaration :: declarations =>
      .function { declaration with body := panSimpCompileHOL declaration.body } ::
        panSimpDeclsHOL declarations
  | declaration :: declarations => declaration :: panSimpDeclsHOL declarations
termination_by declarations => sizeOf declarations

def smartSeq : Prog α → Prog α → Prog α
  | .skip, program => program
  | pre, program => .seq pre program

def seqCallRet : Prog α → Prog α
  | .seq
      (.call (some (some (.local, returnName), none)) function arguments)
      (.return (.var .local returnedName)) =>
      if returnName = returnedName then
        .call none function arguments
      else
        .seq
          (.call (some (some (.local, returnName), none)) function arguments)
          (.return (.var .local returnedName))
  | program => program

def seqAssoc (pre : Prog α) : Prog α → Prog α
  | .skip => pre
  | .dec name shape value body =>
      smartSeq pre (.dec name shape value (seqAssoc .skip body))
  | .seq first second => seqAssoc (seqAssoc pre first) second
  | .ite condition thenBranch elseBranch =>
      smartSeq pre (.ite condition (seqAssoc .skip thenBranch)
        (seqAssoc .skip elseBranch))
  | .while condition body =>
      smartSeq pre (.while condition (seqAssoc .skip body))
  | .call info function arguments =>
      let info := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar, seqAssoc .skip handler))
      smartSeq pre (.call info function arguments)
  | .decCall name shape function arguments body =>
      smartSeq pre (.decCall name shape function arguments (seqAssoc .skip body))
  | .annot _ _ => pre
  | program => smartSeq pre program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def retToTail : Prog α → Prog α
  | .skip => .skip
  | .dec name shape value body => .dec name shape value (retToTail body)
  | .seq first second =>
      seqCallRet (.seq (retToTail first) (retToTail second))
  | .ite condition thenBranch elseBranch =>
      .ite condition (retToTail thenBranch) (retToTail elseBranch)
  | .while condition body => .while condition (retToTail body)
  | .call info function arguments =>
      let info := match info with
        | none => none
        | some (returns, none) => some (returns, none)
        | some (returns, some (exception, handlerVar, handler)) =>
            some (returns, some (exception, handlerVar, retToTail handler))
      .call info function arguments
  | .decCall name shape function arguments body =>
      .decCall name shape function arguments (retToTail body)
  | program => program
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

def panSimpProg (program : Prog α) : Prog α :=
  retToTail (seqAssoc .skip program)

def panSimpDecls : List (Decl α) → List (Decl α)
  | [] => []
  | .function declaration :: declarations =>
      .function { declaration with body := panSimpProg declaration.body } ::
        panSimpDecls declarations
  | declaration :: declarations => declaration :: panSimpDecls declarations
termination_by declarations => sizeOf declarations

def panSimpDecl : Decl α → Decl α
  | .function declaration =>
      .function { declaration with body := panSimpProg declaration.body }
  | declaration => declaration

/-! Cake's `functions` projection (`panLangScript.sml:319-326`): the function
    table as `(name, params, body, returnShape)` entries, with non-function
    declarations dropped.  This is an alias for the production `functionEntries`
    (`Flapjack/Pancake/PanLang.lean`); that mirror is deliberately untagged
    because its carriers are generic `Decl α` with String-backed names and
    monomorphic `Shape`/`Prog α`, not HOL's word-indexed `decl` with `mlstring`
    identifiers (bead `flapjack-pxn.18.3.5.8`).  The executable path and the
    production definition coincide. -/
abbrev functions :
    List (Decl α) → List (FunName × List (VarName × Shape) × Prog α × Shape) :=
  functionEntries

/-- Counterpart of Cake's `functions_eq_FILTER`
    (`cakeml/pancake/semantics/panPropsScript.sml:1487`): the function table is
    exactly the projection of the function declarations, with every other
    declaration contributing nothing.  Cake writes the projection as a `MAP`
    over `FILTER is_function` with an `ARB` default branch; `List.filterMap`
    states the same content without needing a default value.

    FLAPJACK-SPECIFIC (not an exact HOL port, so no `@[hol]` tag): beyond the
    identifier carrier (production `Decl α`/`Prog α` are generic in the word
    element type and use `FunName = String`, while HOL `decl` is word-indexed
    with `funname`/`varname`/`eid`/`stcname` = `mlstring`), the statement is
    not HOL's: HOL maps the tuple projection over `FILTER is_function` with an
    unspecified `ARB` fallback on non-function declarations, whereas
    `List.filterMap` drops those declarations via `none` instead of producing
    an `ARB` tuple.  Rendering `ARB` faithfully (and an exact `functions`
    over `List (DeclHOL width)`) is tracked by `flapjack-4ac.4.109`, itself
    gated on the exact MlString/width-indexed carriers of
    `flapjack-pxn.18.3.5.8`. -/
theorem functions_eq_filterMap (declarations : List (Decl α)) :
    functions declarations =
      declarations.filterMap (fun declaration =>
        match declaration with
        | .function function =>
            some (function.name, function.params, function.body,
              function.returnShape)
        | _ => none) := by
  induction declarations with
  | nil => rfl
  | cons declaration declarations ih =>
      cases declaration <;> simp [functions, functionEntries, ih]

/-! Source-shaped counterpart of Cake's `compile_prog_pmatch`: `compile_prog`
    maps `compile` over function declarations and leaves other declarations
    unchanged. -/
theorem panSimpDecls_eq_map (declarations : List (Decl α)) :
    panSimpDecls declarations = declarations.map panSimpDecl := by
  induction declarations with
  | nil => simp [panSimpDecls]
  | cons declaration declarations ih =>
      cases declaration <;> simp [panSimpDecls, panSimpDecl, ih]

/-! Counterpart of Cake's `functions_compile_prog`
    (`pan_simpProofScript.sml:1017-1022`): `pan_simp` rewrites each function
    body through `panSimpProg` and leaves the name, parameters, and return
    shape unchanged. -/
theorem functions_panSimpDecls (declarations : List (Decl α)) :
    functions (panSimpDecls declarations) =
      (functions declarations).map (fun entry =>
        (entry.1, entry.2.1, panSimpProg entry.2.2.1, entry.2.2.2)) := by
  induction declarations with
  | nil => simp [panSimpDecls, functions, functionEntries]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [panSimpDecls, functions, functionEntries, ih]

/-! Cake's `MEM_functions` (`pan_globalsProofScript.sml:2380`): every entry of
    the `functions` projection comes from a function declaration of the source
    list, with the entry being that declaration's name, parameters, body, and
    return shape. -/
theorem mem_functions {declarations : List (Decl α)}
    {entry : FunName × List (VarName × Shape) × Prog α × Shape}
    (hmem : entry ∈ functions declarations) :
    ∃ declaration : FunDecl α,
      (.function declaration : Decl α) ∈ declarations ∧
        entry = (declaration.name, declaration.params, declaration.body,
          declaration.returnShape) := by
  rw [functions_eq_filterMap] at hmem
  obtain ⟨declaration, hdecl, hentry⟩ := List.mem_filterMap.mp hmem
  cases declaration with
  | function declaration => exact ⟨declaration, hdecl, (Option.some.inj hentry).symm⟩
  | _ => contradiction

/-! Counterpart of Cake's `first_compile_prog_all_distinct`
    (`pan_simpProofScript.sml:1025-1041`): `pan_simp` preserves distinctness of
    the function-name table.  This is the invariant `state_rel_imp_semantics`
    needs for the compiled program. -/
theorem functions_panSimpDecls_names_nodup (declarations : List (Decl α))
    (hnames : ((functions declarations).map (fun entry => entry.1)).Nodup) :
    ((functions (panSimpDecls declarations)).map (fun entry => entry.1)).Nodup := by
  simpa only [functions_panSimpDecls, List.map_map, Function.comp_def] using hnames

/-! Counterpart of Cake's `compile_prog_distinct_params`
    (`pan_simpProofScript.sml:1064-1069`): rewriting function bodies does not
    alter the parameter names of any function declaration.  Flapjack keeps
    parameter shapes alongside names, so the invariant is stated for the
    projected name list. -/
theorem functions_panSimpDecls_params_nodup (declarations : List (Decl α))
    (hparams : ∀ entry ∈ functions declarations,
      (entry.2.1.map Prod.fst).Nodup) :
    ∀ entry ∈ functions (panSimpDecls declarations),
      (entry.2.1.map Prod.fst).Nodup := by
  rw [functions_panSimpDecls]
  intro entry hentry
  simp only [List.mem_map] at hentry
  obtain ⟨source, hsource, rfl⟩ := hentry
  exact hparams source hsource

/-- Counterpart of the original `ALOOKUP` on the function table
    (`panLangScript.sml:319-326`): first-occurrence lookup of a function name in
    the `(name, params, body, returnShape)` projection `functions` produces. -/
def lookupFunctionEntry (name : FunName) :
    List (FunName × List (VarName × Shape) × Prog α × Shape) →
      Option (List (VarName × Shape) × Prog α × Shape)
  | [] => none
  | entry :: functions =>
      if name == entry.1 then some (entry.2.1, entry.2.2.1, entry.2.2.2)
      else lookupFunctionEntry name functions

/-! Counterpart of the function-table lookup fact used by Cake's
    `state_rel_imp_semantics` (`pan_simpProofScript.sml:1073-1300`): a
    successful lookup in the source table succeeds at the same name,
    parameters, and return shape after `pan_simp`, with only the body
    transformed. -/
theorem lookupFunctionEntry_panSimpDecls
    (declarations : List (Decl α)) (name : FunName)
    {parameters : List (VarName × Shape)} {body : Prog α} {returnShape : Shape}
    (hlookup : lookupFunctionEntry name (functions declarations) =
      some (parameters, body, returnShape)) :
    lookupFunctionEntry name (functions (panSimpDecls declarations)) =
      some (parameters, panSimpProg body, returnShape) := by
  induction declarations with
  | nil => simp [functions, functionEntries, lookupFunctionEntry] at hlookup
  | cons declaration declarations ih =>
      cases declaration with
      | function declaration =>
          by_cases hname : name == declaration.name <;>
            simp_all [functions, functionEntries, panSimpDecls, lookupFunctionEntry]
      | _ => simpa only [panSimpDecls, functions, functionEntries] using ih hlookup

/-- `lookupFunctionEntry` returns the entry found at a given index whenever the
    function names are distinct. -/
theorem lookupFunctionEntry_of_getElem?
    (functions : List (FunName × List (VarName × Shape) × Prog α × Shape))
    (hnodup : (functions.map (fun entry => entry.1)).Nodup)
    {n : Nat} {entry : FunName × List (VarName × Shape) × Prog α × Shape}
    (hget : functions[n]? = some entry) :
    lookupFunctionEntry entry.1 functions =
      some (entry.2.1, entry.2.2.1, entry.2.2.2) := by
  induction functions generalizing n with
  | nil => simp at hget
  | cons head tail ih =>
      rw [List.map_cons, List.nodup_cons] at hnodup
      obtain ⟨hhead, htail⟩ := hnodup
      cases n with
      | zero =>
          rw [List.getElem?_cons_zero] at hget
          simp only [Option.some.injEq] at hget
          subst hget
          simp [lookupFunctionEntry]
      | succ n =>
          rw [List.getElem?_cons_succ] at hget
          have hentry_mem : entry.1 ∈ tail.map (fun entry => entry.1) := by
            obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hget
            rw [← heq]
            exact List.mem_map.mpr ⟨tail[n], List.getElem_mem hlt, rfl⟩
          have hne : entry.1 ≠ head.1 := fun h => hhead (h ▸ hentry_mem)
          simp only [lookupFunctionEntry]
          rw [ite_eq_right (by simpa [beq_iff_eq] using hne)]
          exact ih htail hget

/-- Counterpart of Cake's `el_compile_prog_el_prog_eq`
    (`pan_simpProofScript.sml:1047-1061`): the compiled function table only
    rewrites bodies, so an entry at a given index still comes from the source
    table. -/
theorem el_functions_panSimpDecls_eq {declarations : List (Decl α)} {n : Nat}
    {start : FunName} {pprog p : Prog α} {rshape : Shape}
    (hentry : (functions (panSimpDecls declarations))[n]? =
      some (start, [], pprog, rshape))
    (hnodup : ((functions declarations).map (fun entry => entry.1)).Nodup)
    (_hlen : n < (functions declarations).length)
    (hlookup : lookupFunctionEntry start (functions declarations) =
      some ([], p, rshape)) :
    (functions declarations)[n]? = some (start, [], p, rshape) := by
  rw [functions_panSimpDecls, List.getElem?_map] at hentry
  rcases hget : (functions declarations)[n]? with _ | ⟨name, params, body, shape⟩
  · simp [hget] at hentry
  · simp only [hget, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hentry
    obtain ⟨rfl, rfl, _, rfl⟩ := hentry
    have hp := lookupFunctionEntry_of_getElem? (functions declarations) hnodup hget
    simp only [hlookup, Option.some.injEq, Prod.mk.injEq, true_and, and_true] at hp
    simp [hp]

@[simp] theorem smartSeq_skip (program : Prog α) :
    smartSeq (.skip : Prog α) program = program := by
  cases program <;> rfl

theorem panSimpProg_skip : panSimpProg (.skip : Prog α) = .skip := by
  simp [panSimpProg, seqAssoc, retToTail]

/-! `pan_simp` preserves the exception identifiers collected by the source
    program. These are the two local preservation steps used by Cake's
    `exp_ids_ret_to_tail_eq` and `exp_ids_seq_assoc_eq` proofs. -/

theorem expIds_seqCallRet (program : Prog α) :
    expIds (seqCallRet program) = expIds program := by
  unfold seqCallRet
  split
  · split <;> simp [expIds]
  · rfl

theorem expIds_smartSeq (pre program : Prog α) :
    expIds (smartSeq pre program) = expIds pre ++ expIds program := by
  cases pre <;> simp [smartSeq, expIds]

/-! Functional induction exposes recursive handlers nested inside `Call`
    for the exception-identifier preservation proof. -/

theorem expIds_seqAssoc (pre program : Prog α) :
    expIds (seqAssoc pre program) = expIds pre ++ expIds program := by
  fun_induction expIds program generalizing pre with
  | case14 info _ _ noHandler =>
      rcases info with _ | ⟨returns, _ | ⟨exception, handlerVar, handler⟩⟩
      · simp [seqAssoc, expIds_smartSeq, expIds]
      · simp [seqAssoc, expIds_smartSeq, expIds]
      · exact (noHandler returns exception handlerVar handler rfl).elim
  | _ =>
      grind only [seqAssoc, expIds_smartSeq, expIds, List.append_assoc,
        List.nil_append, List.append_nil]

/-! The same functional induction covers the nested handler in `retToTail`. -/

theorem expIds_retToTail (program : Prog α) :
    expIds (retToTail program) = expIds program := by
  fun_induction expIds program with
  | case14 info _ _ noHandler =>
      rcases info with _ | ⟨returns, _ | ⟨exception, handlerVar, handler⟩⟩
      · simp [retToTail, expIds]
      · simp [retToTail, expIds]
      · exact (noHandler returns exception handlerVar handler rfl).elim
  | _ => grind only [retToTail, expIds_seqCallRet, expIds]

/-- The full `pan_simp` program transformation preserves the exception
    identifiers reachable from a program, mirroring Cake's
    `exp_ids_compile_eq`. -/
theorem expIds_panSimpProg (program : Prog α) :
    expIds (panSimpProg program) = expIds program := by
  simp only [panSimpProg]
  rw [expIds_retToTail, expIds_seqAssoc]
  simp [expIds]

/-- The exception identifiers reachable from the bodies of the function
    declarations in a declaration table: the projection that Cake's `get_eids`
    scans. -/
def declarationExceptionIds : List (Decl α) → List ExceptionId
  | [] => []
  | .function declaration :: declarations =>
      expIds declaration.body ++ declarationExceptionIds declarations
  | _ :: declarations => declarationExceptionIds declarations

/-- The declaration-table pass of `pan_simp` preserves the exception
    identifiers reachable from every function body.  This is the source-side
    companion of Cake's `get_eids_from_decls` invariance: the finite domain of
    the exception table cannot change when the bodies are simplified. -/
theorem declarationExceptionIds_panSimpDecls (declarations : List (Decl α)) :
    declarationExceptionIds (panSimpDecls declarations) =
      declarationExceptionIds declarations := by
  induction declarations with
  | nil => simp [panSimpDecls, declarationExceptionIds]
  | cons declaration declarations ih =>
      cases declaration <;>
        simp [panSimpDecls, declarationExceptionIds, expIds_panSimpProg, ih]

/-- The function-only projection of the declaration table is exactly the flat
    map of `expIds` over the function bodies, which is the list that Cake's
    `get_eids` numbers before removing repeats. -/
theorem declarationExceptionIds_map_function (functions : List (FunDecl α)) :
    declarationExceptionIds (functions.map (fun function => Decl.function function)) =
      functions.flatMap (fun function => expIds function.body) := by
  induction functions with
  | nil => simp [declarationExceptionIds]
  | cons function functions ih => simp [declarationExceptionIds, ih]

/-! ## A linear syntactic size bound for `seqAssoc`

`seqAssoc` only reassociates sequences and never duplicates syntax, so a
simple node-count measure grows by a constant factor.  This is the syntactic
ingredient needed to turn the clocked evaluator's per-constructor success
equations into a uniform `C(sizeOf program)` fuel adequacy statement. -/

def progSize : Prog α → Nat
  | .skip => 1
  | .dec _ _ _ body => 1 + progSize body
  | .seq first second => 1 + progSize first + progSize second
  | .ite _ thenBranch elseBranch => 1 + progSize thenBranch + progSize elseBranch
  | .while _ body => 1 + progSize body
  | .call info _ _ =>
      match info with
      | none => 1
      | some (_, none) => 1
      | some (_, some (_, _, handler)) => 1 + progSize handler
  | .decCall _ _ _ _ body => 1 + progSize body
  | .annot _ _ => 1
  | _ => 1
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-! `ret_to_tail` only removes the assign/return wrapper used for a tail call;
    it does not add program nodes.  This small syntactic fact is used by the
    evaluator-level `pan_simp` fuel bound. -/

theorem progSize_seqCallRet_le (program : Prog α) :
    progSize (seqCallRet program) ≤ progSize program := by
  fun_cases seqCallRet program with
  | case1 => simp only [progSize]; omega
  | case2 | case3 => exact Nat.le_refl _

theorem progSize_retToTail_le (program : Prog α) :
    progSize (retToTail program) ≤ progSize program := by
  fun_induction progSize program with
  | case3 =>
      simp only [retToTail]
      exact Nat.le_trans (progSize_seqCallRet_le _) (by simp only [progSize]; omega)
  | case11 => grind only [retToTail, progSize]
  | _ => simp_all only [retToTail, progSize] <;> omega

theorem progSize_pos (program : Prog α) : 1 ≤ progSize program := by
  fun_cases progSize program <;> omega

/-- A call-aware structural budget: `progSize` for the ordinary nodes, but each
    `Call`/`DecCall` node reserves a uniform `callBudget` for its callee (and
    `max` with the handler or continuation body where those run at the same
    fuel).  This is the budget the program-level adequacy statement needs, since
    `progSize` charges only one unit for a `Call` node and does not cover the
    callee or handler bodies. -/
def progCallFuel (callBudget : Nat) : Prog α → Nat
  | .skip => 1
  | .dec _ _ _ body => 1 + progCallFuel callBudget body
  | .seq first second =>
      1 + progCallFuel callBudget first + progCallFuel callBudget second
  | .ite _ thenBranch elseBranch =>
      1 + progCallFuel callBudget thenBranch + progCallFuel callBudget elseBranch
  | .while _ body => 1 + progCallFuel callBudget body
  | .call none _ _ => 1 + callBudget
  | .call (some (_, none)) _ _ => 1 + callBudget
  | .call (some (_, some (_, _, handler))) _ _ =>
      1 + max callBudget (progCallFuel callBudget handler)
  | .decCall _ _ _ _ body => 1 + max callBudget (progCallFuel callBudget body)
  | .annot _ _ => 1
  | _ => 1
termination_by program => sizeOf program
decreasing_by all_goals decreasing_trivial

/-- Flapjack-specific positivity helper for the structural fuel budget. -/
private theorem progCallFuel_pos (callBudget : Nat) (program : Prog α) :
    1 ≤ progCallFuel callBudget program := by
  fun_cases progCallFuel callBudget program <;> omega

/-- The call-aware budget dominates the plain structural size. -/
theorem progSize_le_progCallFuel (callBudget : Nat) (program : Prog α) :
    progSize program ≤ progCallFuel callBudget program := by
  fun_induction progSize program with
  | case11 => exact progCallFuel_pos _ _
  | _ => simp_all only [progCallFuel] <;> omega

theorem progSize_smartSeq_le (pre program : Prog α) :
    progSize (smartSeq pre program) ≤ progSize pre + progSize program + 1 := by
  unfold smartSeq
  split
  · simp only [progSize]
    omega
  · simp only [progSize]
    omega

theorem progSize_seqAssoc_le (pre program : Prog α) :
    progSize (seqAssoc pre program) ≤ progSize pre + 4 * progSize program := by
  fun_induction progSize program generalizing pre <;>
    grind only [seqAssoc, progSize, progSize_smartSeq_le]

theorem progSize_panSimpProg_le (program : Prog α) :
    progSize (panSimpProg program) ≤ 1 + 4 * progSize program := by
  simp only [panSimpProg]
  exact Nat.le_trans (progSize_retToTail_le (seqAssoc .skip program))
    (by simpa [progSize] using progSize_seqAssoc_le (.skip : Prog α) program)

end Flapjack
