module

public import Flapjack.HolRef
public import Flapjack.Pancake.PanGlobals
public import Flapjack.Pancake.PanLang.Decl
public import Flapjack.Pancake.Proofs.PanGlobals.ShapeInfrastructure
public import Flapjack.Pancake.Semantics.PanSem
public import Flapjack.Pancake.Semantics.PanSem.DecExact
public import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
public import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

@[expose] public section

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Exact HOL `good_res_def`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:164-170`):

    `good_res (SOME TimeOut) = F`, `good_res (SOME (Return v)) = F`,
    `good_res (SOME (Exception l v)) = F`, `good_res (SOME (FinalFFI ev)) = F`,
    and `good_res _ = T`.

    The five clauses match HOL clause-for-clause.  HOL's word-parametrized
    `('a) panSem$result` is the width-indexed inductive `PanSemResultExact width`
    (`DecExact.lean:58`, `[NeZero width]`), whose `word_lab` payloads are
    `ValueHOL width`; that is the standard `(words_as_type_indexed_bitvec)`
    translation, now accepted by the reference checker for reviewed
    width-indexed inductive carriers (formerly withdrawn under bead
    `flapjack-ikjm.2`).  No finite-map qualifier applies: no HOL `|->` field is
    named. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "good_res_def"
  (words_as_type_indexed_bitvec)]
def goodResHOL {width : Nat} [NeZero width] :
    Option (PanSemResultExact width) → Bool
  | some (.timeOut) => false
  | some (.returned _) => false
  | some (.exception _ _) => false
  | some (.finalFfi _) => false
  | _ => true


/-- Exact HOL port of Cake's `MEM_functions`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2380-2387`): every entry
    of `functions decs` comes from a `Function` declaration of `decs`, and is
    that declaration's `(name, params, body, return)`.

    This is the faithful word-indexed port and uses the exact carriers:
    `DeclHOL`/`FunDeclHOL`/`ProgHOL width` with `MlS` names and `ShapeHOL`
    shapes, and the exact `functions` projection `functionsHOL`.  The
    A former production analogue used Lean `String` identifiers and generic
    `Prog α`; it has been removed. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "MEM_functions"]
theorem MEM_functionsHOL {width : Nat} [NeZero width]
    {declarations : List (DeclHOL width)}
    {entry : MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL}
    (hmem : entry ∈ functionsHOL declarations) :
    ∃ declaration : FunDeclHOL width,
      (.function declaration : DeclHOL width) ∈ declarations ∧
        entry = (declaration.name, declaration.params, declaration.body,
          declaration.returnShape) := by
  induction declarations with
  | nil => simp [functionsHOL] at hmem
  | cons declaration declarations ih =>
      cases declaration with
      | function funDecl =>
          simp only [functionsHOL, List.mem_cons] at hmem
          rcases hmem with hentry | htail
          · exact ⟨funDecl, by simp, hentry⟩
          · rcases ih htail with ⟨fi, hmem, heq⟩
            exact ⟨fi, by simp [hmem], heq⟩
      | decl shape name value =>
          simp only [functionsHOL] at hmem
          rcases ih hmem with ⟨fi, hmem, heq⟩
          exact ⟨fi, by simp [hmem], heq⟩
      | exnDecl exceptionName shape =>
          simp only [functionsHOL] at hmem
          rcases ih hmem with ⟨fi, hmem, heq⟩
          exact ⟨fi, by simp [hmem], heq⟩
      | name struct fields =>
          simp only [functionsHOL] at hmem
          rcases ih hmem with ⟨fi, hmem, heq⟩
          exact ⟨fi, by simp [hmem], heq⟩

/-- Exact HOL port of Cake's `fperm_name_cancel`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1622-1626`):
    `fperm_name f g (fperm_name f g name) = name`.

    HOL's `fperm_name_cancel` carries no type annotation, so HOL states it
    polymorphically (`!f g name. fperm_name f g (fperm_name f g name) = name`
    at `'a -> 'a -> 'a -> 'a`).  The faithful Lean port is correspondingly
    generic in `α` with `[DecidableEq α]`, and uses the exact polymorphic
    `fpermName` (`Flapjack/Pancake/PanGlobals.lean`).  There is no side
    condition.  The production `String`-specialized `fperm_name_cancel` below
    is only an instance of this polymorphic original and is left untagged.
    Direct HOL/Lean edge-case fixtures:
    `scripts/hol-probes/pan_globals_fperm_name_probe.out`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_name_cancel"]
theorem fpermName_cancel {α : Type u} [DecidableEq α] (f g name : α) :
    fpermName f g (fpermName f g name) = name := by
  unfold fpermName
  repeat' split <;> simp_all

/-- Exact HOL port of Cake's `fperm_name_cong`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1629-1632`):
    `fperm_name f g x = fperm_name f g y ⇔ x = y`, i.e. the source/target
    renaming is injective.

    HOL's `fperm_name_cong` carries no type annotation, so HOL states it
    polymorphically; the faithful Lean port is correspondingly generic in `α`
    with `[DecidableEq α]` and uses the exact polymorphic `fpermName`.  There
    is no side condition.  The production `String`-specialized
    `fperm_name_cong` below is only an instance of this polymorphic original
    and is left untagged.  Direct HOL/Lean edge-case fixtures:
    `scripts/hol-probes/pan_globals_fperm_name_probe.out`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fperm_name_cong"]
theorem fpermName_cong {α : Type u} [DecidableEq α] (f g left right : α) :
    fpermName f g left = fpermName f g right ↔ left = right := by
  constructor
  · intro h
    have := congrArg (fpermName f g) h
    rw [fpermName_cancel, fpermName_cancel] at this
    exact this
  · intro h
    rw [h]


/-- Exact port of HOL `functions_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1701-1708`):
    `functions (fperm_decs x y code) =
     MAP (λ(a,b,c,d). (fperm_name x y a, b, fperm x y c, d)) (functions code)`.

    Over the reviewed word-indexed `DeclHOL width` carrier, `functionsHOL`,
    `fpermDecsHOL`, `fpermName`, and `fpermHOL` use native MlS identifiers
    and the source list/constructor structure. `[NeZero width]` matches HOL's
    positive word dimension.  Renaming a declaration list renames each function-table entry's
    name via `fpermName` and its body via `fpermHOL`, leaving the parameter
    shapes and return shape untouched, exactly as in HOL. The
    `words_as_type_indexed_bitvec` qualifier records only HOL's positive
    type-indexed word dimension as Lean's positive `width`; the native MlS,
    list, declaration and program constructor structure is unchanged. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "functions_fperm_decs"
  (words_as_type_indexed_bitvec)]
theorem functionsFpermDecsHOL {width : Nat} [NeZero width] (x y : MlS)
    (code : List (DeclHOL width)) :
    functionsHOL (fpermDecsHOL x y code) =
      (functionsHOL code).map (fun entry =>
        (fpermName x y entry.1, entry.2.1,
          fpermHOL x y entry.2.2.1, entry.2.2.2)) := by
  induction code with
  | nil => simp [fpermDecsHOL, functionsHOL]
  | cons d ds ih =>
      cases d with
      | function fi => simp [fpermDecsHOL, functionsHOL, ih]
      | decl shape name value => simp [fpermDecsHOL, functionsHOL, ih]
      | exnDecl exceptionName shape => simp [fpermDecsHOL, functionsHOL, ih]
      | name struct fields => simp [fpermDecsHOL, functionsHOL, ih]


/-! Exact-shaped port of Cake's `map_pick_up_first`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2995`): projecting the
    first component of a quadruple map recovers the mapped first components.
    HOL `MAP` is Lean `List.map` and `FST` is `Prod.fst`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "map_pick_up_first"]
theorem map_pick_up_first {α β γ δ ε ζ η θ : Type}
    (l : List (α × β × γ × δ)) (f1 : α → ε) (f2 : β → ζ) (f3 : γ → η)
    (f4 : δ → θ) :
    ((l.map (fun p => (f1 p.1, f2 p.2.1, f3 p.2.2.1, f4 p.2.2.2))).map Prod.fst) =
      (l.map Prod.fst).map f1 := by
  rw [List.map_map, List.map_map]
  rfl

/-! Exact-shaped port of Cake's `tuple_4_o`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:3003`): composing two
    quadruple projections composes the four component functions pointwise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "tuple_4_o"]
theorem tuple_4_o {α β γ δ ε ζ η θ ι κ ℓ μ : Type}
    (f1 : α → ε) (f2 : β → ζ) (f3 : γ → η) (f4 : δ → θ)
    (g1 : ι → α) (g2 : κ → β) (g3 : ℓ → γ) (g4 : μ → δ) :
    ((fun q : α × β × γ × δ => (f1 q.1, f2 q.2.1, f3 q.2.2.1, f4 q.2.2.2)) ∘
        (fun p : ι × κ × ℓ × μ =>
          (g1 p.1, g2 p.2.1, g3 p.2.2.1, g4 p.2.2.2))) =
      (fun p : ι × κ × ℓ × μ =>
        (f1 (g1 p.1), f2 (g2 p.2.1), f3 (g3 p.2.2.1), f4 (g4 p.2.2.2))) := by
  funext p
  obtain ⟨x, y, z, t⟩ := p
  rfl


/-- `@[hol]`-tagged exact source-shaped port of Cake's `fresh_name_correct`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:993`): a name returned by
    the fresh-name search is not a member of the search list. HOL
    `MEM (fresh_name name names) names ⇒ F` becomes the equivalent
    `freshNameHOL name names ∉ names`. Statement, quantifiers, and body are
    exact apart from the HOL `mlstring`/Lean `String` carrier of `name` and the
    membership-only `names` list: `name` is byte-observable (the generated name
    crosses the compiler boundary and the same-module witness
    `holMlStringWitness_freshNameHOL_not_mem_hol` establishes
    `NameRanged (freshNameHOL name names)` from the input premise
    `NameRanged name`), while `names` is used only for membership equality.
    Delegates to the untagged helper `freshNameHOL_not_mem` in the definitional
    counterpart `Flapjack.Pancake.PanGlobals`, so the executed search runs the
    same recursion. Direct HOL rows are in
    `scripts/hol-probes/pan_globals_fresh_name_probe.out`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fresh_name_correct"
  (names_as_string := [name, names]) (names_as_string_boundary := [name])]
theorem freshNameHOL_not_mem_hol (name : String) (names : List String) :
    freshNameHOL name names ∉ names :=
  freshNameHOL_not_mem name names

/-- Same-module byte-rangedness witness for the tagged `fresh_name_correct`
    port `freshNameHOL_not_mem_hol`: the generated name is byte-ranged. -/
theorem holMlStringWitness_freshNameHOL_not_mem_hol (name : String)
    (names : List String) (h : Flapjack.Pancake.PanLang.NameRanged name) :
    Flapjack.Pancake.PanLang.NameRanged (freshNameHOL name names) :=
  holMlStringWitness_freshNameHOL name names h

/-- `@[hol]`-tagged exact source-shaped port of Cake's `fresh_name_correct'`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1003`): if every member
    of `names'` lies in `names`, then a name fresh for `names` is also fresh for
    `names'`. HOL `set names' ⊆ set names` is stated pointwise, as HOL itself
    uses it (`SUBSET_DEF`), and as HOL does, the proof goes through
    `fresh_name_correct`. Statement, hypotheses, and proof are exact apart from
    the HOL `mlstring`/Lean `String` carrier of `name` (byte-observable, witness
    `holMlStringWitness_freshNameHOL_not_mem_of_subset_hol`) and of the
    membership-only lists `names`/`names'`. Direct HOL rows are in
    `scripts/hol-probes/pan_globals_fresh_name_probe.out`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "fresh_name_correct'"
  (names_as_string := [name, names, names']) (names_as_string_boundary := [name])]
theorem freshNameHOL_not_mem_of_subset_hol (name : String)
    (names names' : List String)
    (hmem : freshNameHOL name names ∈ names')
    (hsubset : ∀ candidate, candidate ∈ names' → candidate ∈ names) :
    False :=
  freshNameHOL_not_mem_hol name names (hsubset _ hmem)

/-- Same-module byte-rangedness witness for the tagged `fresh_name_correct'`
    port `freshNameHOL_not_mem_of_subset_hol`: the generated name is
    byte-ranged. -/
theorem holMlStringWitness_freshNameHOL_not_mem_of_subset_hol (name : String)
    (names : List String) (h : Flapjack.Pancake.PanLang.NameRanged name) :
    Flapjack.Pancake.PanLang.NameRanged (freshNameHOL name names) :=
  holMlStringWitness_freshNameHOL name names h


/-- Exact port of HOL `EVERY_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2436-2442`) over the
    reviewed word-indexed `DeclHOL width` carrier.

    HOL states, for a Prop-valued predicate `P`:
    `EVERY (λd. ¬ is_function d ⇒ P d) decs ∧
     EVERY (λd. ∀fi. d = Function fi ⇒
       P (Function (fi with <|name := fperm_name f g fi.name;
                              body := fperm f g fi.body|>))) decs
     ⇒ EVERY P (fperm_decs f g decs)`.
    The two `EVERY` hypotheses are membership-quantified `Prop` predicates
    over `DeclHOL width` (`∀ d ∈ decs, ...`, HOL's `EVERY` at `Prop`), the
    renamed-function hypothesis destructures exactly as HOL's `Function fi`
    (the renamed declaration uses the exact `fpermName`/`fpermHOL`), and the
    conclusion is `∀ d ∈ fpermDecsHOL f g decs, P d`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "EVERY_fperm_decs"]
theorem EVERY_fperm_decsHOL {width : Nat} [NeZero width] (f g : MlS)
    (P : DeclHOL width → Prop) (decs : List (DeclHOL width))
    (hother : ∀ d ∈ decs, isFunctionHOL d = false → P d)
    (hfunction : ∀ d ∈ decs, ∀ fi : FunDeclHOL width, d = .function fi →
        P (.function { fi with
          name := fpermName f g fi.name
          body := fpermHOL f g fi.body })) :
    ∀ d ∈ fpermDecsHOL f g decs, P d := by
  revert hother hfunction
  induction decs with
  | nil => intro _ _ d hd; simp [fpermDecsHOL] at hd
  | cons d ds ih =>
      intro hother hfunction e he
      cases d with
      | function fi =>
          simp only [fpermDecsHOL, List.mem_cons] at he
          rcases he with heq | hmem
          · subst heq
            exact hfunction (.function fi) (by simp) fi rfl
          · exact ih (fun x hx => hother x (by simp [hx]))
              (fun x hx fj hj => hfunction x (by simp [hx]) fj hj) e hmem
      | decl shape name value =>
          simp only [fpermDecsHOL, List.mem_cons] at he
          rcases he with heq | hmem
          · subst heq; exact hother (.decl shape name value) (by simp) rfl
          · exact ih (fun x hx => hother x (by simp [hx]))
              (fun x hx fj hj => hfunction x (by simp [hx]) fj hj) e hmem
      | exnDecl exceptionName shape =>
          simp only [fpermDecsHOL, List.mem_cons] at he
          rcases he with heq | hmem
          · subst heq; exact hother (.exnDecl exceptionName shape) (by simp) rfl
          · exact ih (fun x hx => hother x (by simp [hx]))
              (fun x hx fj hj => hfunction x (by simp [hx]) fj hj) e hmem
      | name struct fields =>
          simp only [fpermDecsHOL, List.mem_cons] at he
          rcases he with heq | hmem
          · subst heq; exact hother (.name struct fields) (by simp) rfl
          · exact ih (fun x hx => hother x (by simp [hx]))
              (fun x hx fj hj => hfunction x (by simp [hx]) fj hj) e hmem

/-- Exact port of HOL `FILTER_decs_fperm_decs`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2832-2838`) over the
    reviewed word-indexed `DeclHOL width` carrier: removing the function
    declarations commutes with `fpermDecsHOL`.  HOL's `$¬ ∘ is_function` is
    `fun d => !isFunctionHOL d` and HOL's `FILTER` is `List.filter`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "FILTER_decs_fperm_decs"]
theorem FILTER_decs_fperm_decsHOL {width : Nat} [NeZero width] (f g : MlS)
    (code : List (DeclHOL width)) :
    (fpermDecsHOL f g code).filter (fun d => !isFunctionHOL d) =
      code.filter (fun d => !isFunctionHOL d) := by
  induction code with
  | nil => simp [fpermDecsHOL]
  | cons d ds ih =>
      cases d with
      | function fi =>
          simp only [fpermDecsHOL, List.filter_cons]
          rw [if_neg (by simp [isFunctionHOL]), if_neg (by simp [isFunctionHOL])]
          exact ih
      | decl shape name value =>
          simp only [fpermDecsHOL, List.filter_cons]
          rw [if_pos (by simp [isFunctionHOL]), if_pos (by simp [isFunctionHOL]), ih]
      | exnDecl exceptionName shape =>
          simp only [fpermDecsHOL, List.filter_cons]
          rw [if_pos (by simp [isFunctionHOL]), if_pos (by simp [isFunctionHOL]), ih]
      | name struct fields =>
          simp only [fpermDecsHOL, List.filter_cons]
          rw [if_pos (by simp [isFunctionHOL]), if_pos (by simp [isFunctionHOL]), ih]



/-! HOL `ALOOKUP_MAP3` and `ALOOKUP_MAP4` remain to be ported without the
    additional Boolean equality assumptions of their former analogues. -/

/-! ## Exact ports of `pan_globals` declaration resorting

These are the three HOL declarations of
`cakeml/pancake/proofs/pan_globalsProofScript.sml:1854-1950` that justify the
`resort_decls` pass: moving a function declaration to the end of a list of
`Decl`/`ExnDecl` declarations, and reordering a mixed declaration list by
`resort_decls`, both preserve the result of `evaluate_decls`.  The evaluator is
the reviewed canonical finite-support `PanSemStateFiniteExact.evaluateDeclsHOLFinite`
and the resorting function is the reviewed `resortDeclsHOL`; the carrier's four
`|->` fields (`locals`, `globals`, `code`, `eshapes`) are recorded by the
`fmap_as_finite_support` qualifier.  The supporting commutation lemmas below are
Flapjack-specific infrastructure with no separate HOL declaration: HOL proves
the same facts inline (`eval_upd_eshapes_eq`, `eval_upd_code_eq`, the
`evaluate_decls_append`/`evaluate_decl_commute` rewrites). -/

namespace PanGlobalsResortDeclsWitnesses

/-- Same-module canonical finite-map witness for the `fmap_as_finite_support`
    qualifier on the imported `PanSemStateFiniteExact` carrier.  It re-exports
    the canonical `toExact`/`ofExact` roundtrip from the carrier's own module so
    that the `@[hol]` tags in this module have the checked witness beside them. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} {σ : Type} [NeZero width] :
    (∀ (state : PanSemStateExact width σ) (h : state.FiniteSupport),
        (PanSemStateFiniteExact.ofExact state h).toExact = state) ∧
    (∀ state : PanSemStateFiniteExact width σ,
        PanSemStateFiniteExact.ofExact state.toExact state.toExact_finiteSupport = state) :=
  PanSemStateFiniteExact.holFmapAsFiniteSupportWitness

end PanGlobalsResortDeclsWitnesses

/-- Function-extensional code-update invariant. HOL obtains this equation by
swapping the expression/code quantifiers of `eval_upd_code_eq` and rewriting
with function equality and eta conversion (pan_globalsProofScript:1697-1699).
The canonical state, four finite-map fields, native expression carrier and
positive word dimension are the same as the reviewed pointwise invariant.
The decidable memory-domain instance is computation evidence, not a semantic
premise; updating code preserves that domain. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "eval_upd_code_eta"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evalHOL_upd_code_eta {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    @PanSemStateFiniteExact.evalHOLFinite width σ _ { state with code := code } h =
      @PanSemStateFiniteExact.evalHOLFinite width σ _ state h := by
  funext expression
  exact @PanSemStateFiniteExact.evalHOLFinite_upd_code_eq width σ _ state h code expression


section
open Classical

/-- Finite-support counterpart of HOL `panProps$evaluate_decls_append`
    (`cakeml/pancake/semantics/panPropsScript.sml:1540`): evaluating `ds1 ++ ds2`
    is the monadic bind of evaluating `ds1` and then `ds2` in the resulting
    state.  Untagged support lemma (the PanProps-tagged port lives in
    `PanProps.EvalInvariant`); it is the local append fact the commutation and
    resort proofs need over `PanSemStateFiniteExact`. -/
theorem evaluateDeclsHOLFinite_append {width : Nat} {σ : Type} [NeZero width] :
    ∀ (state : PanSemStateFiniteExact width σ) [_hdec : DecidablePred state.memaddrs]
      (ds1 ds2 : List (DeclHOL width)),
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state (ds1 ++ ds2) =
        Option.bind (PanSemStateFiniteExact.evaluateDeclsHOLFinite state ds1)
          (fun state' => PanSemStateFiniteExact.evaluateDeclsHOLFinite state' ds2) := by
  intro state _hdec ds1
  induction ds1 generalizing state with
  | nil =>
      intro ds2
      simp only [List.nil_append, PanSemStateFiniteExact.evaluateDeclsHOLFinite]
      have hdecEq : _hdec = (fun address => Classical.propDecidable (state.memaddrs address)) :=
        Subsingleton.elim _ _
      rw [hdecEq]
      rfl
  | cons declaration rest ih =>
      intro ds2
      cases declaration with
      | name name fields =>
          simpa [List.cons_append, PanSemStateFiniteExact.evaluateDeclsHOLFinite]
            using ih state ds2
      | decl shape name expression =>
          letI : DecidablePred
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state).memaddrs := by
            simpa [PanSemStateFiniteExact.emptyLocalsHOLFinite] using _hdec
          simp only [List.cons_append, PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          cases heval : PanSemStateFiniteExact.evalHOLFinite
              (PanSemStateFiniteExact.emptyLocalsHOLFinite state) expression with
          | none => simp
          | some value =>
              by_cases hshape : shapeEqHOL shape (shapeOfHOLExact value)
              · simp only [if_pos hshape]
                exact ih (PanSemStateFiniteExact.setGlobalHOLFinite name value state)
                  (_hdec := _hdec) ds2
              · simp [hshape]
      | function declaration =>
          simp only [List.cons_append, PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          let condition := declaration.params.all
              (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
            isWfShapeExactHOL state.structs declaration.returnShape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos]
            exact ih
              { state with code := state.code.update (declaration.name,
                (declaration.params, declaration.body, declaration.returnShape)) }
              (_hdec := _hdec) ds2
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse]
      | exnDecl exceptionName shape =>
          simp only [List.cons_append, PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          let condition := (state.eshapes.lookup exceptionName).isNone &&
            isWfShapeExactHOL state.structs shape
          by_cases hcondition : condition = true
          · simp only [condition, hcondition, if_pos]
            exact ih
              { state with eshapes := state.eshapes.update (exceptionName, shape) }
              (_hdec := _hdec) ds2
          · have hconditionFalse : condition = false := by
              cases hcond : condition with
              | false => rfl
              | true => exact False.elim (hcondition hcond)
            simp [condition, hconditionFalse]

/-- Flapjack-specific: expression evaluation under `emptyLocalsHOLFinite` is
    unchanged when only the `eshapes` field of the source state changes
    (`evalHOLFinite_upd_eshapes_eq` under `emptyLocalsHOLFinite`).  Support for
    the `ExnDecl`/`Decl` commutation; not a separate HOL declaration. -/
private theorem evalHOLFinite_emptyLocals_eshapes {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (es : HolFiniteMapExact MlS ShapeHOL) (e : ExpHOL width) :
    @PanSemStateFiniteExact.evalHOLFinite width σ _
        (PanSemStateFiniteExact.emptyLocalsHOLFinite { state with eshapes := es }) h e
      = @PanSemStateFiniteExact.evalHOLFinite width σ _
          (PanSemStateFiniteExact.emptyLocalsHOLFinite state) h e :=
  @PanSemStateFiniteExact.evalHOLFinite_upd_eshapes_eq width σ _
    (PanSemStateFiniteExact.emptyLocalsHOLFinite state) h es e

/-- Flapjack-specific commutation used by `resort_decls_evaluate`: swapping an
    adjacent `ExnDecl` and `Decl` leaves the evaluator unchanged, because the
    exception table and the global table are updated independently and the
    `Decl` initialiser is evaluated under cleared locals without reading
    `eshapes`.  HOL proves the analogous `Function`/`Decl` case inline as
    `evaluate_decl_commute`; this `ExnDecl`/`Decl` case has no standalone HOL
    declaration. -/
private theorem evaluateDeclsHOLFinite_exnDeclDeclCommute {width : Nat} {σ : Type}
    [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (eid : MlS) (shape : ShapeHOL) (sh : ShapeHOL) (v' : MlS) (e : ExpHOL width)
    (ds : List (DeclHOL width)) :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite state (.exnDecl eid shape :: .decl sh v' e :: ds)
      = PanSemStateFiniteExact.evaluateDeclsHOLFinite state
          (.decl sh v' e :: .exnDecl eid shape :: ds) := by
  simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
  rw [evalHOLFinite_emptyLocals_eshapes]
  letI : DecidablePred state.emptyLocalsHOLFinite.memaddrs := h
  by_cases hcond : ((state.eshapes.lookup eid).isNone && isWfShapeExactHOL state.structs shape) = true
  · rw [if_pos hcond]
    cases hev : state.emptyLocalsHOLFinite.evalHOLFinite e with
    | none => simp
    | some value =>
        by_cases hshape : shapeEqHOL sh (shapeOfHOLExact value) = true
        · simp [hshape, hcond, PanSemStateFiniteExact.setGlobalHOLFinite]
        · simp [hshape]
  · rw [if_neg hcond]
    cases hev : state.emptyLocalsHOLFinite.evalHOLFinite e with
    | none => simp
    | some value =>
        by_cases hshape : shapeEqHOL sh (shapeOfHOLExact value) = true
        · simp [hshape, hcond, PanSemStateFiniteExact.setGlobalHOLFinite]
        · simp [hshape]

/-- Flapjack-specific commutation used when moving a `Function` past an
    `ExnDecl`: the function update touches only `code` and the exception check
    touches only `eshapes`/`structs`, so the two updates commute.  No standalone
    HOL declaration. -/
private theorem evaluateDeclsHOLFinite_functionExnDeclCommute {width : Nat} {σ : Type}
    [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (f : FunDeclHOL width) (eid : MlS) (shape : ShapeHOL) (ds : List (DeclHOL width)) :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite state (.function f :: .exnDecl eid shape :: ds)
      = PanSemStateFiniteExact.evaluateDeclsHOLFinite state
          (.exnDecl eid shape :: .function f :: ds) := by
  simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
  by_cases hwf : (f.params.all (fun parameter => isWfShapeExactHOL state.structs parameter.snd) &&
      isWfShapeExactHOL state.structs f.returnShape) = true
  <;> by_cases hfresh : ((state.eshapes.lookup eid).isNone &&
      isWfShapeExactHOL state.structs shape) = true
  <;> simp [hwf, hfresh]

/-- Flapjack-specific list support: a filtered list satisfies its own predicate. -/
private theorem filter_all_self {width : Nat} [NeZero width]
    (p : DeclHOL width → Bool) (l : List (DeclHOL width)) :
    (l.filter p).all p = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.filter_cons]
      by_cases ha : p a = true
      · simp [ha, ih]
      · simp [ha]

/-- Flapjack-specific list support: every `ExnDecl` satisfies the resort
    disjunction. -/
private theorem filter_exn_all_or {width : Nat} [NeZero width]
    (l : List (DeclHOL width)) :
    (l.filter isExnDeclHOL).all (fun d => isDeclHOL d || isExnDeclHOL d) = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.filter_cons]
      by_cases ha : isExnDeclHOL a = true
      · simp [ha, ih]
      · rw [if_neg ha]
        exact ih

/-- Flapjack-specific list support: every `Decl` satisfies the resort
    disjunction. -/
private theorem filter_decl_all_or {width : Nat} [NeZero width]
    (l : List (DeclHOL width)) :
    (l.filter isDeclHOL).all (fun d => isDeclHOL d || isExnDeclHOL d) = true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.filter_cons]
      by_cases ha : isDeclHOL a = true
      · simp [ha, ih]
      · rw [if_neg ha]
        exact ih

/-- Flapjack-specific list support: under the resort admissibility predicate no
    declaration is a `Name`, so `filter is_name` is empty. -/
private theorem filter_isName_eq_nil {width : Nat} [NeZero width]
    {l : List (DeclHOL width)}
    (h : l.all (fun d => isFunctionHOL d || isDeclHOL d || isExnDeclHOL d) = true) :
    l.filter isNameHOL = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.all_cons, Bool.and_eq_true] at h
      obtain ⟨ha, hl⟩ := h
      rw [List.filter_cons]
      have hname : isNameHOL a = false := by
        cases a <;> simp_all [isNameHOL, isFunctionHOL, isDeclHOL, isExnDeclHOL]
      simp [hname, ih hl]

/-- Flapjack-specific: a `Decl` commutes leftwards past a run of `ExnDecl`s,
    used in the `Decl` case of `resort_decls_evaluate`. -/
private theorem evaluateDeclsHOLFinite_moveDeclLeft {width : Nat} {σ : Type} [NeZero width] :
    ∀ (exns : List (DeclHOL width)),
      exns.all isExnDeclHOL = true →
      ∀ (sh : ShapeHOL) (v' : MlS) (e : ExpHOL width) (rest : List (DeclHOL width))
        (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs],
        PanSemStateFiniteExact.evaluateDeclsHOLFinite state (exns ++ (.decl sh v' e :: rest))
          = PanSemStateFiniteExact.evaluateDeclsHOLFinite state
              (.decl sh v' e :: (exns ++ rest)) := by
  intro exns
  induction exns with
  | nil => intro _ sh v' e rest state _; rfl
  | cons a exns ih =>
      intro hall sh v' e rest state hdec
      rw [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨ha, hExns⟩ := hall
      cases a with
      | exnDecl eid shp =>
          simp only [List.cons_append]
          rw [← evaluateDeclsHOLFinite_exnDeclDeclCommute state eid shp sh v' e (exns ++ rest)]
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          by_cases hcond : ((state.eshapes.lookup eid).isNone &&
              isWfShapeExactHOL state.structs shp) = true
          · rw [if_pos hcond, if_pos hcond]
            exact ih hExns sh v' e rest { state with eshapes := state.eshapes.update (eid, shp) }
          · rw [if_neg hcond, if_neg hcond]
      | name _ _ => simp [isExnDeclHOL] at ha
      | decl _ _ _ => simp [isExnDeclHOL] at ha
      | function _ => simp [isExnDeclHOL] at ha

/-- Flapjack-specific: a `Function` commutes rightwards past a run of
    `Decl`/`ExnDecl` declarations, the content of `evaluate_decls_one_fun_last`
    in tail form. -/
private theorem evaluateDeclsHOLFinite_moveFunctionRight {width : Nat} {σ : Type} [NeZero width] :
    ∀ (X : List (DeclHOL width)),
      X.all (fun d => isDeclHOL d || isExnDeclHOL d) = true →
      ∀ (f : FunDeclHOL width) (rest : List (DeclHOL width))
        (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs],
        PanSemStateFiniteExact.evaluateDeclsHOLFinite state (.function f :: (X ++ rest))
          = PanSemStateFiniteExact.evaluateDeclsHOLFinite state (X ++ (.function f :: rest)) := by
  intro X
  induction X with
  | nil => intro _ f rest state _; rfl
  | cons a X ih =>
      intro hall f rest state hdec
      rw [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨ha, hX⟩ := hall
      cases a with
      | decl sh v' e =>
          simp only [List.cons_append]
          rw [PanSemStateFiniteExact.evaluateDeclsHOLFinite_declCommute state f sh v' e (X ++ rest)]
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          letI : DecidablePred state.emptyLocalsHOLFinite.memaddrs := hdec
          cases heval : state.emptyLocalsHOLFinite.evalHOLFinite e with
          | none => simp
          | some value =>
              letI : DecidablePred
                  (PanSemStateFiniteExact.setGlobalHOLFinite v' value state).memaddrs := hdec
              by_cases hshape : shapeEqHOL sh (shapeOfHOLExact value) = true
              · simp only [hshape, if_pos]
                exact ih hX f rest (PanSemStateFiniteExact.setGlobalHOLFinite v' value state)
              · simp [hshape]
      | exnDecl eid shp =>
          simp only [List.cons_append]
          rw [evaluateDeclsHOLFinite_functionExnDeclCommute state f eid shp (X ++ rest)]
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          by_cases hcond : ((state.eshapes.lookup eid).isNone &&
              isWfShapeExactHOL state.structs shp) = true
          · rw [if_pos hcond, if_pos hcond]
            exact ih hX f rest { state with eshapes := state.eshapes.update (eid, shp) }
          · rw [if_neg hcond, if_neg hcond]
      | name _ _ => simp [isDeclHOL, isExnDeclHOL] at ha
      | function _ => simp [isDeclHOL, isExnDeclHOL] at ha

/-- Flapjack-specific normal-form lemma: under the resort admissibility
    predicate, evaluating `filter is_exn_decl ++ filter is_decl ++ filter
    is_function` agrees with evaluating the original list.  This is the
    inductive core of `resort_decls_evaluate`. -/
private theorem evaluateDeclsHOLFinite_nf {width : Nat} {σ : Type} [NeZero width] :
    ∀ (decs : List (DeclHOL width)),
      decs.all (fun d => isFunctionHOL d || isDeclHOL d || isExnDeclHOL d) = true →
      ∀ (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs],
      PanSemStateFiniteExact.evaluateDeclsHOLFinite state
          ((decs.filter isExnDeclHOL) ++ (decs.filter isDeclHOL) ++ (decs.filter isFunctionHOL))
        = PanSemStateFiniteExact.evaluateDeclsHOLFinite state decs := by
  intro decs
  induction decs with
  | nil => intro _ state _; rfl
  | cons x decs ih =>
      intro hall state hdec
      rw [List.all_cons, Bool.and_eq_true] at hall
      obtain ⟨hx, hdecs⟩ := hall
      cases x with
      | exnDecl eid shp =>
          rw [List.filter_cons_of_pos (by simp [isExnDeclHOL]),
              List.filter_cons_of_neg (by simp [isDeclHOL]),
              List.filter_cons_of_neg (by simp [isFunctionHOL])]
          simp only [List.cons_append]
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          by_cases hcond : ((state.eshapes.lookup eid).isNone &&
              isWfShapeExactHOL state.structs shp) = true
          · rw [if_pos hcond, if_pos hcond]
            exact ih hdecs { state with eshapes := state.eshapes.update (eid, shp) }
          · rw [if_neg hcond, if_neg hcond]
      | decl sh v' e =>
          rw [List.filter_cons_of_neg (by simp [isExnDeclHOL]),
              List.filter_cons_of_pos (by simp [isDeclHOL]),
              List.filter_cons_of_neg (by simp [isFunctionHOL])]
          rw [List.append_assoc, List.cons_append]
          rw [evaluateDeclsHOLFinite_moveDeclLeft (decs.filter isExnDeclHOL)
            (filter_all_self isExnDeclHOL decs) sh v' e
            ((decs.filter isDeclHOL) ++ (decs.filter isFunctionHOL)) state]
          rw [← List.append_assoc]
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          letI : DecidablePred state.emptyLocalsHOLFinite.memaddrs := hdec
          cases heval : state.emptyLocalsHOLFinite.evalHOLFinite e with
          | none => simp
          | some value =>
              letI : DecidablePred
                  (PanSemStateFiniteExact.setGlobalHOLFinite v' value state).memaddrs := hdec
              by_cases hshape : shapeEqHOL sh (shapeOfHOLExact value) = true
              · simp only [hshape, if_pos]
                exact ih hdecs (PanSemStateFiniteExact.setGlobalHOLFinite v' value state)
              · simp [hshape]
      | function f =>
          rw [List.filter_cons_of_neg (by simp [isExnDeclHOL]),
              List.filter_cons_of_neg (by simp [isDeclHOL]),
              List.filter_cons_of_pos (by simp [isFunctionHOL])]
          have hX : ((decs.filter isExnDeclHOL) ++ (decs.filter isDeclHOL)).all
              (fun d => isDeclHOL d || isExnDeclHOL d) = true := by
            rw [List.all_append, filter_exn_all_or, filter_decl_all_or]
            rfl
          rw [← evaluateDeclsHOLFinite_moveFunctionRight
            ((decs.filter isExnDeclHOL) ++ (decs.filter isDeclHOL)) hX f
            (decs.filter isFunctionHOL) state]
          simp only [PanSemStateFiniteExact.evaluateDeclsHOLFinite]
          by_cases hcond : (f.params.all (fun parameter => isWfShapeExactHOL state.structs parameter.snd) &&
              isWfShapeExactHOL state.structs f.returnShape) = true
          · rw [if_pos hcond, if_pos hcond]
            exact ih hdecs
              { state with code := state.code.update (f.name, (f.params, f.body, f.returnShape)) }
          · rw [if_neg hcond, if_neg hcond]
      | name _ _ => simp [isFunctionHOL, isDeclHOL, isExnDeclHOL] at hx

end

/-- Flapjack-specific: `resortDeclsHOL` under the resort admissibility
    predicate is the normal form `filter is_exn_decl ++ filter is_decl ++
    filter is_function`, because no declaration is a `Name` and the leading
    `filter is_name` is empty. -/
theorem resortDeclsHOL_eq_filter {width : Nat} [NeZero width] (decs : List (DeclHOL width))
    (h : decs.all (fun d => isFunctionHOL d || isDeclHOL d || isExnDeclHOL d) = true) :
    resortDeclsHOL decs =
      (decs.filter isExnDeclHOL) ++ (decs.filter isDeclHOL) ++ (decs.filter isFunctionHOL) := by
  unfold resortDeclsHOL
  rw [filter_isName_eq_nil h, List.nil_append]

/-- Exact port of HOL `evaluate_decls_one_fun_last[local]`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1854-1872`): when `y` is a
    `Function` and `xs` consists only of `Decl`/`ExnDecl` declarations, moving
    `y` from the end to the front of the declaration list leaves
    `evaluate_decls` unchanged.  HOL's `EVERY` over the `Decl`/`ExnDecl` case
    split is rendered as `xs.all (fun d => is_decl d || is_exn_decl d) = true`.

    The finite-support evaluator is called with the classical `DecidablePred
    state.memaddrs` instance supplied internally, so the statement quantifies only
    over the state (and declarations) exactly as the HOL statement does and carries
    no decidability-instance parameter. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_decls_one_fun_last"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateDeclsOneFunLast {width : Nat} {σ : Type} [NeZero width]
    (y : DeclHOL width) (xs : List (DeclHOL width))
    (state : PanSemStateFiniteExact width σ) :
    isFunctionHOL y = true →
    xs.all (fun d => isDeclHOL d || isExnDeclHOL d) = true →
    PanSemStateFiniteExact.evaluateDeclsHOLFinite
        (h := (fun a => Classical.propDecidable (state.memaddrs a))) state (xs ++ [y]) =
      PanSemStateFiniteExact.evaluateDeclsHOLFinite
        (h := (fun a => Classical.propDecidable (state.memaddrs a))) state (y :: xs) := by
  intro hy hxs
  letI : DecidablePred state.memaddrs := (fun a => Classical.propDecidable (state.memaddrs a))
  cases y with
  | function f =>
      have h := evaluateDeclsHOLFinite_moveFunctionRight xs hxs f [] state
      simpa using h.symm
  | name _ _ => simp [isFunctionHOL] at hy
  | decl _ _ _ => simp [isFunctionHOL] at hy
  | exnDecl _ _ => simp [isFunctionHOL] at hy

/-- Exact port of HOL `resort_decls_evaluate`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1874-1941`): if every
    declaration of `decs` is a `Function`, `Decl`, or `ExnDecl`, then evaluating
    the resorted list and the original list agree.

    The finite-support evaluator is called with the classical `DecidablePred
    state.memaddrs` instance supplied internally, so the statement quantifies only
    over the state (and declarations) exactly as the HOL statement does and carries
    no decidability-instance parameter. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "resort_decls_evaluate"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem resortDeclsEvaluate {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (decs : List (DeclHOL width)) :
    decs.all (fun d => isFunctionHOL d || isDeclHOL d || isExnDeclHOL d) = true →
    PanSemStateFiniteExact.evaluateDeclsHOLFinite
        (h := (fun a => Classical.propDecidable (state.memaddrs a))) state (resortDeclsHOL decs) =
      PanSemStateFiniteExact.evaluateDeclsHOLFinite
        (h := (fun a => Classical.propDecidable (state.memaddrs a))) state decs := by
  intro h
  letI : DecidablePred state.memaddrs := (fun a => Classical.propDecidable (state.memaddrs a))
  rw [resortDeclsHOL_eq_filter decs h]
  exact evaluateDeclsHOLFinite_nf decs h state

/-- Exact port of HOL `resort_decls_evaluate_IMP[local]`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:1943-1950`): a successful
    evaluation of `decs` and the resort admissibility predicate imply a
    successful evaluation of `resort_decls decs` to the same state.

    The finite-support evaluator is called with the classical `DecidablePred
    state.memaddrs` instance supplied internally, so the statement quantifies only
    over the state (and declarations) exactly as the HOL statement does and carries
    no decidability-instance parameter. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "resort_decls_evaluate_IMP"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem resortDeclsEvaluateImp {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ)
    (decs : List (DeclHOL width)) (state' : PanSemStateFiniteExact width σ) :
    PanSemStateFiniteExact.evaluateDeclsHOLFinite
        (h := (fun a => Classical.propDecidable (state.memaddrs a))) state decs = some state' →
    decs.all (fun d => isFunctionHOL d || isDeclHOL d || isExnDeclHOL d) = true →
    PanSemStateFiniteExact.evaluateDeclsHOLFinite
        (h := (fun a => Classical.propDecidable (state.memaddrs a))) state (resortDeclsHOL decs) = some state' := by
  intro hdecs hresort
  rw [resortDeclsEvaluate state decs hresort]
  exact hdecs

/-! ## Exact ports of the `pan_globals` pure-clock and counting helpers

`evaluate_two[local]` and `num_cases_lemma[local]`
(`cakeml/pancake/proofs/pan_globalsProofScript.sml:2631-2657`) are the two
elementary helpers used by HOL's `semantics_init_call` proof.  `evaluate_two`
needs only the tagged `panProps$evaluate_add_clock_eq`
(`panPropsEvaluateAddClockEq`) and no LUB, `semantics`, or `evaluate_invariants`
machinery; `num_cases_lemma` is pure logic.  They are therefore ported here
independently of the still-blocked `LUB_IMAGE_SUC`/`semantics_init_call` slice
(bead `flapjack-pxn.18.5.2.22.3.2`). -/

/-- Exact port of HOL `evaluate_two[local]`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2631-2652`): two
    clock-bounded runs of the same program that both finish without `TimeOut`
    produce the same result and the same FFI event history.  The program is the
    exact `ProgHOL` and the state the reviewed finite-support carrier; the only
    carrier difference is the finite-map/word translation recorded by the
    qualifiers, and no premise is added.  HOL's `evaluate` is
    `evaluateHOLFiniteState`, and the proof is clock arithmetic through
    `panPropsEvaluateAddClockEq`. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "evaluate_two"
  (fmap_as_finite_support := [locals, globals, code, eshapes])
  (words_as_type_indexed_bitvec)]
theorem evaluateTwo {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (t : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (st : PanSemStateFiniteExact width σ)
    (res' : Option (PanSemResultExact width)) (st' : PanSemStateFiniteExact width σ)
    (k k' : Nat) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState { t with clock := k } p = (res, st) ∧
      PanSemStateFiniteExact.evaluateHOLFiniteState { t with clock := k' } p = (res', st') ∧
      res ≠ some .timeOut ∧ res' ≠ some .timeOut) →
    res = res' ∧ st.ffi = st'.ffi := by
  rintro ⟨h, h', hnt, hnt'⟩
  rcases Nat.le_total k k' with hle | hle
  · obtain ⟨kk, hkk⟩ := Nat.le.dest hle
    have step := panPropsEvaluateAddClockEq p { t with clock := k } res st kk ⟨h, hnt⟩
    have hstate : ({ { t with clock := k } with clock := k + kk } :
        PanSemStateFiniteExact width σ) = { t with clock := k' } := by rw [hkk]
    rw [hstate] at step
    have heq : (res, { st with clock := st.clock + kk }) = (res', st') :=
      step.symm.trans h'
    obtain ⟨hr, hs⟩ := Prod.mk.inj heq
    exact ⟨hr, by rw [← hs]⟩
  · obtain ⟨kk, hkk⟩ := Nat.le.dest hle
    have step := panPropsEvaluateAddClockEq p { t with clock := k' } res' st' kk ⟨h', hnt'⟩
    have hstate : ({ { t with clock := k' } with clock := k' + kk } :
        PanSemStateFiniteExact width σ) = { t with clock := k } := by rw [hkk]
    rw [hstate] at step
    have heq : (res', { st' with clock := st'.clock + kk }) = (res, st) :=
      step.symm.trans h
    obtain ⟨hr, hs⟩ := Prod.mk.inj heq
    exact ⟨hr.symm, by rw [← hs]⟩

/-- Exact port of HOL `num_cases_lemma[local]`
    (`cakeml/pancake/proofs/pan_globalsProofScript.sml:2654-2657`):
    `(!P. (!x. P x) ==> P 0 /\ !x. P (SUC x))`.  The predicate is Lean
    `Nat → Prop` (HOL `num -> bool` with the standard `bool`/`Prop`
    translation), and the statement binds the same universally quantified
    predicate and conclusion with no extra premise. -/
@[hol "cakeml/pancake/proofs/pan_globalsProofScript.sml" "num_cases_lemma"]
theorem numCasesLemma (P : Nat → Prop) :
    (∀ x, P x) → P 0 ∧ ∀ x, P (Nat.succ x) :=
  fun h => ⟨h 0, fun x => h (Nat.succ x)⟩

end Flapjack
