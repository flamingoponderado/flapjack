import Flapjack.Compiler.Backend.BvlToBvi.Proofs.TmcNames
import Flapjack.Compiler.Backend.BviTailrec.Proofs.RewriteCorrespondence

/-! Absence of TMC's mutable-block primitive before the TMC pass. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BviTmc (noMutcons noMutconsOp)

/-- Replacing a propagated variable by zero cannot introduce mutable-block
allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bvi_let_delete_var_no_mutcons"]
theorem deleteVar_noMutcons (expression : Bvi.Exp) (safe : noMutcons expression) :
    noMutcons (BviLet.deleteVar expression) := by
  cases expression <;> simp_all [BviLet.deleteVar, noMutcons, noMutconsOp, Subtype.forall]

private theorem let_compileList_eq_map (env : List Nat) (d : Nat) (xs : List Bvi.Exp) :
    BviLet.compileList env d xs = xs.map (BviLet.compileSing env d) := by
  induction xs with
  | nil => simp [BviLet.compileList]
  | cons x xs ih => simp [BviLet.compileList, ih]

private theorem memberBudget (xs : List Bvi.Exp) (e : Bvi.Exp) (member : e ∈ xs) :
    Bvi.expBudget e < Bvi.listBudget xs := by
  induction xs with
  | nil => simp at member
  | cons x xs ih =>
    simp only [List.mem_cons] at member
    simp only [Bvi.listBudget]
    rcases member with rfl | member
    · omega
    · have := ih member; omega

/-- Let propagation preserves the absence of mutable-block allocation. -/
theorem let_compileSing_noMutcons (env : List Nat) (d : Nat) (expression : Bvi.Exp)
    (safe : noMutcons expression) : noMutcons (BviLet.compileSing env d expression) := by
  cases expression with
  | var v => simp [BviLet.compileSing, noMutcons]
  | force l v => simp [BviLet.compileSing, noMutcons]
  | ifThenElse x y z =>
    have parts : noMutcons x ∧ noMutcons y ∧ noMutcons z := by simpa [noMutcons] using safe
    simp [BviLet.compileSing, noMutcons, let_compileSing_noMutcons env d x parts.1,
      let_compileSing_noMutcons env d y parts.2.1, let_compileSing_noMutcons env d z parts.2.2]
  | raise x =>
    simpa [BviLet.compileSing, noMutcons] using
      let_compileSing_noMutcons env d x (by simpa [noMutcons] using safe)
  | tick x =>
    simpa [BviLet.compileSing, noMutcons] using
      let_compileSing_noMutcons env d x (by simpa [noMutcons] using safe)
  | op op xs =>
    have parts : noMutconsOp op ∧ ∀ e ∈ xs, noMutcons e := by simpa [noMutcons, Subtype.forall] using safe
    simp only [BviLet.compileSing, noMutcons, Subtype.forall, let_compileList_eq_map, List.mem_map]
    refine ⟨parts.1, ?_⟩
    rintro _ ⟨e, member, rfl⟩
    exact let_compileSing_noMutcons env d e (parts.2 e member)
  | «return» xs =>
    have parts : ∀ e ∈ xs, noMutcons e := by simpa [noMutcons, Subtype.forall] using safe
    simp only [BviLet.compileSing, noMutcons, Subtype.forall, let_compileList_eq_map, List.mem_map]
    rintro _ ⟨e, member, rfl⟩
    exact let_compileSing_noMutcons env d e (parts e member)
  | call ticks dest xs handler =>
    cases handler with
    | none =>
      have parts : ∀ e ∈ xs, noMutcons e := by simpa [noMutcons, Subtype.forall] using safe
      simp only [BviLet.compileSing, noMutcons, Subtype.forall, let_compileList_eq_map, List.mem_map]
      constructor
      · rintro _ ⟨e, member, rfl⟩
        exact let_compileSing_noMutcons env d e (parts e member)
      · trivial
    | some handler =>
      have parts : (∀ e ∈ xs, noMutcons e) ∧ noMutcons handler := by
        simpa [noMutcons, Subtype.forall] using safe
      simp only [BviLet.compileSing, noMutcons, Subtype.forall, let_compileList_eq_map, List.mem_map]
      constructor
      · rintro _ ⟨e, member, rfl⟩
        exact let_compileSing_noMutcons env d e (parts.1 e member)
      · exact let_compileSing_noMutcons (0 :: env) d handler parts.2
  | letCall rets ticks dest xs body =>
    have parts : (∀ e ∈ xs, noMutcons e) ∧ noMutcons body := by
      simpa [noMutcons, Subtype.forall] using safe
    simp only [BviLet.compileSing, noMutcons, Subtype.forall, let_compileList_eq_map, List.mem_map]
    constructor
    · rintro _ ⟨e, member, rfl⟩
      exact let_compileSing_noMutcons env d e (parts.1 e member)
    · exact let_compileSing_noMutcons (List.replicate rets 0 ++ env) d body parts.2
  | «let» xs body =>
    cases xs with
    | nil =>
      simpa [BviLet.compileSing, noMutcons] using
        let_compileSing_noMutcons env d body (by simpa [noMutcons, Subtype.forall] using safe)
    | cons x xs =>
      have parts : (∀ e ∈ x :: xs, noMutcons e) ∧ noMutcons body := by
        simpa [noMutcons, Subtype.forall] using safe
      have bindingsSafe : ∀ e ∈ BviLet.compileList env d (x :: xs), noMutcons e := by
        simp only [let_compileList_eq_map, List.mem_map]
        rintro _ ⟨e, member, rfl⟩
        exact let_compileSing_noMutcons env d e (parts.1 e member)
      have mappedSafe : ∀ e ∈ (BviLet.compileList env d (x :: xs)).map BviLet.deleteVar, noMutcons e := by
        simp only [List.mem_map]
        rintro _ ⟨e, member, rfl⟩
        exact deleteVar_noMutcons e (bindingsSafe e member)
      have bodySafe (env' : List Nat) : noMutcons (BviLet.compileSing env' d body) :=
        let_compileSing_noMutcons env' d body parts.2
      cases body with
      | var v =>
        by_cases equal : v = xs.length
        · have lastMem := List.getLast_mem (show x :: xs ≠ [] by simp)
          have lastSafe := let_compileSing_noMutcons (env.map (xs.length + ·)) (d + xs.length)
            ((x :: xs).getLast (by simp)) (parts.1 _ lastMem)
          have frontSafe : ∀ e ∈ BviLet.compileList env d (x :: xs).dropLast, noMutcons e := by
            simp only [let_compileList_eq_map, List.mem_map]
            rintro _ ⟨e, member, rfl⟩
            exact let_compileSing_noMutcons env d e (parts.1 e (List.dropLast_subset _ member))
          simpa [BviLet.compileSing, equal, noMutcons, Subtype.forall] using And.intro frontSafe lastSafe
        · simpa [BviLet.compileSing, equal, noMutcons, Subtype.forall] using
            And.intro mappedSafe (bodySafe (BviLet.extractList (BviLet.compileList env d (x :: xs)) ++ env))
      | _ =>
        all_goals simpa [BviLet.compileSing, noMutcons, Subtype.forall] using
          And.intro mappedSafe (bodySafe (BviLet.extractList (BviLet.compileList env d (x :: xs)) ++ env))
termination_by Bvi.expBudget expression
decreasing_by
  all_goals try (have member' := List.dropLast_subset (x :: xs) member; have := memberBudget (x :: xs) e member')
  all_goals try (have := memberBudget _ _ member)
  all_goals try (have := memberBudget (x :: xs) ((x :: xs).getLast (by simp)) (List.getLast_mem (by simp)))
  all_goals simp_all [Bvi.expBudget, Bvi.listBudget]
  all_goals omega

/-- The paired single-expression and list preservation property used by
the original lowering proof. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bvi_let_compile_no_mutcons"]
theorem let_compile_noMutcons :
    (∀ env d expression, noMutcons expression → noMutcons (BviLet.compileSing env d expression)) ∧
    (∀ env d expressions, (∀ e ∈ expressions, noMutcons e) →
      ∀ e ∈ BviLet.compileList env d expressions, noMutcons e) := by
  constructor
  · exact let_compileSing_noMutcons
  · intro env d expressions safe
    simp only [let_compileList_eq_map, List.mem_map]
    rintro _ ⟨e, member, rfl⟩
    exact let_compileSing_noMutcons env d e (safe e member)

/-- The source entry point to let propagation preserves the invariant;
`compile_exp_eq` identifies it with the singleton compiler at empty environment. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bvi_let_compile_exp_no_mutcons"]
theorem let_compileExp_noMutcons (expression : Bvi.Exp) (safe : noMutcons expression) :
    noMutcons (BviLet.compileSing [] 0 expression) :=
  let_compileSing_noMutcons [] 0 expression safe

/-- Every successful run of the executable let pass preserves the invariant. -/
theorem let_compileBounded_noMutcons (fuel : Nat) (env : List Nat) (d : Nat)
    (expression result : Bvi.Exp) (safe : noMutcons expression)
    (run : BviLet.compileBounded fuel env d expression = some result) : noMutcons result := by
  rw [BviLet.compileBounded_eq_compileSing] at run
  have eq := Option.some.inj run
  rw [← eq]
  exact let_compileSing_noMutcons env d expression safe

/-- Integer literal lowering never emits mutable-block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_int_no_mutcons"]
theorem compileInt_noMutcons (value : Int) : noMutcons (compileInt value) := by
  simp [compileInt, noMutcons, noMutconsOp, Subtype.forall]
  split <;> simp

/-- Lowering an operation cannot introduce mutable-block allocation when
its already lowered operands do not contain it. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_op_no_mutcons"]
theorem compileOp_noMutcons (op : ClosLang.Op) (args : List Bvi.Exp)
    (safe : ∀ e ∈ args, noMutcons e) : noMutcons (compileOp op args) := by
  have zeroSafe : noMutcons (.op (.intOp (.const 0)) []) := by simp [noMutcons, noMutconsOp, Subtype.forall]
  have lengthSafe (v : Nat) : noMutcons (.call 0 (some listLengthLocation)
      [.var v, .op (.intOp (.const 0)) []] none) := by simp [noMutcons, noMutconsOp, Subtype.forall]
  have argsSafe : ∀ e ∈ (if args.isEmpty then [.op (.intOp (.const 0)) []] else args), noMutcons e := by
    split <;> simp_all
  cases op <;> simp only [compileOp]
  all_goals repeat' first | split | simp [noMutcons, noMutconsOp, Subtype.forall, compileInt_noMutcons]
  all_goals repeat' first
    | exact safe
    | exact zeroSafe
    | exact lengthSafe _
    | exact argsSafe
    | constructor
    | simp_all
  intro e member
  rcases member with member | rfl
  · exact safe e member
  · exact zeroSafe

private def auxNoMutcons (aux : AppList (Nat × Nat × Bvi.Exp)) : Prop :=
  ∀ entry ∈ appListAppend aux, noMutcons entry.2.2

private theorem auxNoMutcons_append {a b : AppList (Nat × Nat × Bvi.Exp)}
    (ha : auxNoMutcons a) (hb : auxNoMutcons b) : auxNoMutcons (smartAppend a b) := by
  simp only [auxNoMutcons, appListAppend_smartAppend, List.mem_append] at *
  intro entry member
  rcases member with member | member
  · exact ha entry member
  · exact hb entry member

private theorem auxNoMutcons_fresh (n arity : Nat) (body : Bvi.Exp) (safe : noMutcons body) :
    auxNoMutcons (compileAuxSource (n, arity, body)) := by
  simp [auxNoMutcons, compileAuxSource, appListAppend, appendAux, let_compileExp_noMutcons body safe]

private theorem destLetBudget' (exp : Bvl.Exp) :
    listBudget (destLet exp).1 ≤ expBudget exp ∧ expBudget (destLet exp).2 ≤ expBudget exp := by
  cases exp <;> simp [destLet, expBudget, listBudget] <;> omega

mutual
/-- The source-shaped expression lowering emits a safe expression and safe
auxiliary functions. -/
theorem compileSingSource_noMutcons (start : Nat) (exp : Bvl.Exp) :
    noMutcons (compileSingSource start exp).1 ∧ auxNoMutcons (compileSingSource start exp).2.1 := by
  cases exp with
  | var v => simp [compileSingSource, noMutcons, auxNoMutcons, appListAppend, appendAux]
  | force loc v => simp [compileSingSource, noMutcons, auxNoMutcons, appListAppend, appendAux]
  | raise x =>
    rcases h : compileSingSource start x with ⟨converted, aux, next⟩
    have ih := compileSingSource_noMutcons start x
    simpa [compileSingSource, h, noMutcons] using ih
  | tick x =>
    rcases h : compileSingSource start x with ⟨converted, aux, next⟩
    have ih := compileSingSource_noMutcons start x
    simpa [compileSingSource, h, noMutcons] using ih
  | op op xs =>
    rcases h : compileListSource start xs with ⟨converted, aux, next⟩
    have ih := compileListSource_noMutcons start xs
    simp only [h] at ih
    simpa [compileSingSource, h] using And.intro (compileOp_noMutcons op converted ih.1) ih.2
  | call ticks dest xs =>
    rcases h : compileListSource start xs with ⟨converted, aux, next⟩
    have ih := compileListSource_noMutcons start xs
    simpa [compileSingSource, h, noMutcons, Subtype.forall] using ih
  | ifThenElse x y z =>
    rcases hx : compileSingSource start x with ⟨x', a, n1⟩
    rcases hy : compileSingSource n1 y with ⟨y', b, n2⟩
    rcases hz : compileSingSource n2 z with ⟨z', c, n3⟩
    have ix := compileSingSource_noMutcons start x
    have iy := compileSingSource_noMutcons n1 y
    have iz := compileSingSource_noMutcons n2 z
    simp only [hx] at ix
    simp only [hy] at iy
    simp only [hz] at iz
    simpa [compileSingSource, hx, hy, hz, noMutcons] using
      And.intro (And.intro ix.1 (And.intro iy.1 iz.1))
        (auxNoMutcons_append (auxNoMutcons_append ix.2 iy.2) iz.2)
  | «let» xs body =>
    by_cases empty : xs.isEmpty
    · rcases ha : compileListSource start (destLet body).1 with ⟨args, a, n1⟩
      rcases hb : compileSingSource n1 (destLet body).2 with ⟨inner, b, n2⟩
      have ia := compileListSource_noMutcons start (destLet body).1
      have ib := compileSingSource_noMutcons n1 (destLet body).2
      simp only [ha] at ia
      simp only [hb] at ib
      simpa [compileSingSource, empty, ha, hb, noMutcons, Subtype.forall] using
        And.intro ia.1 (auxNoMutcons_append (auxNoMutcons_append ia.2 ib.2)
          (auxNoMutcons_fresh n2 (destLet body).1.length inner ib.1))
    · rcases ha : compileListSource start xs with ⟨args, a, n1⟩
      rcases hb : compileSingSource n1 body with ⟨body', b, n2⟩
      have ia := compileListSource_noMutcons start xs
      have ib := compileSingSource_noMutcons n1 body
      simp only [ha] at ia
      simp only [hb] at ib
      simpa [compileSingSource, empty, ha, hb, noMutcons, Subtype.forall] using
        And.intro (And.intro ia.1 ib.1) (auxNoMutcons_append ia.2 ib.2)
  | handle body handler =>
    rcases ha : compileListSource start (destLet body).1 with ⟨args, a, n1⟩
    rcases hb : compileSingSource n1 (destLet body).2 with ⟨inner, b, n2⟩
    rcases hc : compileSingSource n2 handler with ⟨handler', c, n3⟩
    have ia := compileListSource_noMutcons start (destLet body).1
    have ib := compileSingSource_noMutcons n1 (destLet body).2
    have ic := compileSingSource_noMutcons n2 handler
    simp only [ha] at ia
    simp only [hb] at ib
    simp only [hc] at ic
    simpa [compileSingSource, ha, hb, hc, noMutcons, Subtype.forall] using
      And.intro (And.intro ia.1 ic.1)
        (auxNoMutcons_append (auxNoMutcons_append (auxNoMutcons_append ia.2 ib.2) ic.2)
          (auxNoMutcons_fresh n3 (destLet body).1.length inner ib.1))
termination_by expBudget exp
decreasing_by
  all_goals try simp only [expBudget]
  all_goals try (have := destLetBudget' body)
  all_goals omega

/-- The source-shaped list lowering emits safe expressions and auxiliaries. -/
theorem compileListSource_noMutcons (start : Nat) (xs : List Bvl.Exp) :
    (∀ e ∈ (compileListSource start xs).1, noMutcons e) ∧
      auxNoMutcons (compileListSource start xs).2.1 := by
  cases xs with
  | nil => simp [compileListSource, auxNoMutcons, appListAppend, appendAux]
  | cons x xs =>
    rcases hx : compileSingSource start x with ⟨converted, a, n1⟩
    rcases ht : compileListSource n1 xs with ⟨rest, b, n2⟩
    have ix := compileSingSource_noMutcons start x
    have it := compileListSource_noMutcons n1 xs
    simp only [hx] at ix
    simp only [ht] at it
    simpa [compileListSource, hx, ht] using
      And.intro (by simpa using And.intro ix.1 it.1) (auxNoMutcons_append ix.2 it.2)
termination_by listBudget xs
decreasing_by all_goals simp only [listBudget]; omega
end

/-- The single-expression and list lowering clauses emit safe results and
auxiliaries. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_exps_sing_no_mutcons"]
theorem compile_exps_sing_noMutcons :
    (∀ n e c aux n1, compileSingSource n e = (c, aux, n1) →
      noMutcons c ∧ auxNoMutcons aux) ∧
    (∀ n es c aux n1, compileListSource n es = (c, aux, n1) →
      (∀ e ∈ c, noMutcons e) ∧ auxNoMutcons aux) := by
  constructor
  · intro n e c aux n1 run
    simpa only [run] using compileSingSource_noMutcons n e
  · intro n es c aux n1 run
    simpa only [run] using compileListSource_noMutcons n es

/-- Each lowered labeled function and its auxiliaries are safe. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_single_no_mutcons"]
theorem compileSingleSource_noMutcons (n : Nat) (program : Nat × Nat × Bvl.Exp)
    (code : AppList (Nat × Nat × Bvi.Exp)) (next : Nat)
    (run : compileSingleSource n program = (code, next)) : auxNoMutcons code := by
  obtain ⟨name, arity, body⟩ := program
  rcases h : compileSingSource n body with ⟨converted, aux, final⟩
  have safe := compileSingSource_noMutcons n body
  simp only [h] at safe
  have main : auxNoMutcons (.list [(bvlNumStubs + bvlToBviNamespaces * name, arity,
      BviLet.compileSing [] 0 converted)]) := by
    simp [auxNoMutcons, appListAppend, appendAux, let_compileExp_noMutcons converted safe.1]
  have both := auxNoMutcons_append main safe.2
  simp [compileSingleSource, h] at run
  obtain ⟨rfl, _⟩ := run
  exact both

/-- The list of lowered functions and auxiliaries is safe. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_list_no_mutcons"]
theorem compileProgramsSource_noMutcons (n : Nat) (program : List (Nat × Nat × Bvl.Exp))
    (code : AppList (Nat × Nat × Bvi.Exp)) (next : Nat)
    (run : compileProgramsSource n program = (code, next)) : auxNoMutcons code := by
  induction program generalizing n code next with
  | nil =>
    simp [compileProgramsSource] at run
    obtain ⟨rfl, _⟩ := run
    simp [auxNoMutcons, appListAppend, appendAux]
  | cons entry rest ih =>
    rcases h : compileSingleSource n entry with ⟨first, middle⟩
    rcases ht : compileProgramsSource middle rest with ⟨tail, final⟩
    have firstSafe := compileSingleSource_noMutcons n entry first middle h
    have tailSafe := ih middle tail final ht
    have combined := auxNoMutcons_append firstSafe tailSafe
    simp [compileProgramsSource, h, ht] at run
    obtain ⟨rfl, _⟩ := run
    exact combined

/-- Incremental BVL-to-BVI compilation emits only safe function bodies. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "compile_inc_no_mutcons"]
theorem compileIncSource_noMutcons (n next : Nat) (program : List (Nat × Nat × Bvl.Exp))
    (code : List (Nat × Nat × Bvi.Exp)) (run : compileIncSource n program = (next, code)) :
    ∀ entry ∈ code, noMutcons entry.2.2 := by
  rcases h : compileProgramsSource n program with ⟨tree, final⟩
  have safe := compileProgramsSource_noMutcons n program tree final h
  simp [compileIncSource, h] at run
  obtain ⟨_, rfl⟩ := run
  exact safe

/-- Every accumulator operator used by tail-recursion rewriting is safe. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "to_op_no_mutcons"]
theorem tailrec_toOp_noMutcons (op : BviTailrec.AssocOp) : noMutconsOp (BviTailrec.toOp op) := by
  cases op <;> simp [BviTailrec.toOp, noMutconsOp]

/-- Applying an accumulator operator introduces no mutable allocation of
its own, so safety is exactly safety of both operands. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "apply_op_no_mutcons"]
theorem tailrec_applyOp_noMutcons (op : BviTailrec.AssocOp) (first second : Bvi.Exp) :
    noMutcons (BviTailrec.applyOp op first second) ↔ noMutcons first ∧ noMutcons second := by
  simp [BviTailrec.applyOp, noMutcons, Subtype.forall, tailrec_toOp_noMutcons]

/-- Accumulator identities do not allocate mutable blocks. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "id_from_op_no_mutcons"]
theorem tailrec_identity_noMutcons (op : BviTailrec.AssocOp) : noMutcons (BviTailrec.identity op) := by
  cases op <;> simp [BviTailrec.identity, noMutcons, noMutconsOp, Subtype.forall]

/-- The tail-recursion wrapper adds only variable bindings. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "let_wrap_no_mutcons"]
theorem tailrec_letWrap_noMutcons (arity : Nat) (identity body : Bvi.Exp) :
    noMutcons (BviTailrec.letWrap arity identity body) ↔ noMutcons identity ∧ noMutcons body := by
  simp only [BviTailrec.letWrap, noMutcons, Subtype.forall, List.mem_append, List.mem_map,
    List.mem_singleton, List.mem_range]
  constructor
  · rintro ⟨bindings, bodySafe⟩
    exact ⟨bindings identity (Or.inr rfl), bodySafe⟩
  · rintro ⟨identitySafe, bodySafe⟩
    refine ⟨?_, bodySafe⟩
    intro expression member
    rcases member with ⟨index, _, rfl⟩ | rfl
    · simp [noMutcons]
    · exact identitySafe

/-- Extracting a binary operation preserves safety of both operands. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "get_bin_args_no_mutcons"]
theorem tailrec_getBinArgs_noMutcons (expression first second : Bvi.Exp)
    (found : BviTailrec.getBinArgs expression = some (first, second)) (safe : noMutcons expression) :
    noMutcons first ∧ noMutcons second := by
  cases expression with
  | op op args =>
    cases args with
    | nil => simp [BviTailrec.getBinArgs] at found
    | cons x xs =>
      cases xs with
      | nil => simp [BviTailrec.getBinArgs] at found
      | cons y rest =>
        cases rest with
        | nil =>
          simp [BviTailrec.getBinArgs] at found
          obtain ⟨rfl, rfl⟩ := found
          simp [noMutcons, Subtype.forall] at safe
          exact safe.2
        | cons z rest => simp [BviTailrec.getBinArgs] at found
  | _ => simp [BviTailrec.getBinArgs] at found

/-- An operator-checked binary extraction likewise preserves operand safety. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "opbinargs_no_mutcons"]
theorem tailrec_opBinArgs_noMutcons (op : BviTailrec.AssocOp) (expression first second : Bvi.Exp)
    (found : BviTailrec.opBinArgs op expression = some (first, second)) (safe : noMutcons expression) :
    noMutcons first ∧ noMutcons second := by
  unfold BviTailrec.opBinArgs at found
  split at found
  · exact tailrec_getBinArgs_noMutcons expression first second found safe
  · simp at found

/-- Swapping the operands of an accepted accumulator operation preserves
the absence of mutable-block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "try_swap_no_mutcons"]
theorem tailrec_trySwap_noMutcons (loc : Nat) (op : BviTailrec.AssocOp) (expression : Bvi.Exp)
    (safe : noMutcons expression) : noMutcons (BviTailrec.trySwap loc op expression) := by
  unfold BviTailrec.trySwap
  split
  · exact safe
  · cases found : BviTailrec.opBinArgs op expression with
    | none => simpa only [found] using safe
    | some pair =>
      obtain ⟨first, second⟩ := pair
      have operands := tailrec_opBinArgs_noMutcons op expression first second found safe
      dsimp only
      split
      · exact (tailrec_applyOp_noMutcons op second first).mpr ⟨operands.2, operands.1⟩
      · exact safe

/-- A successful tail-recursion candidate check does not introduce mutable
block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "check_op_no_mutcons"]
theorem tailrec_checkOp_noMutcons (ctx : List BviTailrec.ValueType) (op : BviTailrec.AssocOp)
    (loc : Nat) (expression checked : Bvi.Exp)
    (found : BviTailrec.checkOp ctx op loc expression = some checked) (safe : noMutcons expression) :
    noMutcons checked := by
  have swapped := tailrec_trySwap_noMutcons loc op expression safe
  unfold BviTailrec.checkOp at found
  cases operands : BviTailrec.opBinArgs op (BviTailrec.trySwap loc op expression) with
  | none => simp [operands] at found
  | some pair =>
    obtain ⟨first, second⟩ := pair
    have pairSafe := tailrec_opBinArgs_noMutcons op _ first second operands swapped
    rw [operands] at found
    dsimp only at found
    split at found
    · simp only [Option.some.injEq] at found
      subst checked
      exact (tailrec_applyOp_noMutcons op first second).mpr pairSafe
    · simp at found

/-- Extracted call arguments and handler inherit safety from the call. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "args_from_no_mutcons"]
theorem tailrec_argsFrom_noMutcons (expression : Bvi.Exp) (ticks loc : Nat)
    (args : List Bvi.Exp) (handler : Option Bvi.Exp)
    (found : BviTailrec.argsFrom expression = some (ticks, loc, args, handler))
    (safe : noMutcons expression) :
    (∀ e ∈ args, noMutcons e) ∧ (match handler with | none => True | some e => noMutcons e) := by
  cases expression with
  | call ticks' dest args' handler' =>
    cases dest with
    | none => simp [BviTailrec.argsFrom] at found
    | some loc' =>
      simp [BviTailrec.argsFrom] at found
      obtain ⟨rfl, rfl, rfl, rfl⟩ := found
      cases handler' <;> simpa [noMutcons, Subtype.forall] using safe
  | _ => simp [BviTailrec.argsFrom] at found

/-- Building an accumulator worker call preserves safety of its inputs. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "push_call_no_mutcons"]
theorem tailrec_pushCall_noMutcons (next : Nat) (op : BviTailrec.AssocOp) (acc : Nat)
    (value expression : Bvi.Exp) (valueSafe : noMutcons value) (safe : noMutcons expression) :
    noMutcons (BviTailrec.pushCall next op acc value (BviTailrec.argsFrom expression)) := by
  cases found : BviTailrec.argsFrom expression with
  | none => simp [BviTailrec.pushCall, noMutcons]
  | some data =>
    obtain ⟨ticks, loc, args, handler⟩ := data
    obtain ⟨argsSafe, handlerSafe⟩ := tailrec_argsFrom_noMutcons expression ticks loc args handler found safe
    cases handler <;> simp_all [BviTailrec.pushCall, noMutcons, Subtype.forall]
    all_goals
      intro e member
      rcases member with member | rfl
      · exact argsSafe e member
      · exact (tailrec_applyOp_noMutcons op _ _).mpr ⟨by simp [noMutcons], valueSafe⟩

/-- The source rewrite's candidate-dispatch branch preserves the absence of
mutable-block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "rewrite_catchall_no_mutcons"]
theorem tailrec_dispatch_noMutcons (ctx : List BviTailrec.ValueType)
    (op : BviTailrec.AssocOp) (loc next acc : Nat) (expression : Bvi.Exp)
    (flag : Bool) (output : Bvi.Exp)
    (result : BviTailrec.sourceDispatch loc next op acc ctx expression = (flag, output))
    (safe : noMutcons expression) : noMutcons output := by
  unfold BviTailrec.sourceDispatch at result
  cases checked : BviTailrec.checkOp ctx op loc expression with
  | none =>
    simp [checked] at result
    obtain ⟨_, rfl⟩ := result
    exact (tailrec_applyOp_noMutcons op _ _).mpr ⟨by simp [noMutcons], safe⟩
  | some candidate =>
    have candidateSafe := tailrec_checkOp_noMutcons ctx op loc expression candidate checked safe
    cases operands : BviTailrec.opBinArgs op candidate with
    | none =>
      simp [checked, operands] at result
      obtain ⟨_, rfl⟩ := result
      exact (tailrec_applyOp_noMutcons op _ _).mpr ⟨by simp [noMutcons], candidateSafe⟩
    | some pair =>
      obtain ⟨value, call⟩ := pair
      have pairSafe := tailrec_opBinArgs_noMutcons op candidate value call operands candidateSafe
      simp [checked, operands] at result
      obtain ⟨_, rfl⟩ := result
      exact tailrec_pushCall_noMutcons next op acc value call pairSafe.1 pairSafe.2

/-- The source-shaped tail-recursion rewrite preserves absence of mutable
allocation. The executed bounded rewrite agrees with this definition. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "rewrite_no_mutcons"]
theorem tailrec_rewrite_noMutcons (loc next : Nat) (op : BviTailrec.AssocOp)
    (acc : Nat) (ctx : List BviTailrec.ValueType) (expression : Bvi.Exp)
    (flag : Bool) (output : Bvi.Exp)
    (result : BviTailrec.rewriteSource loc next op acc ctx expression = (flag, output))
    (safe : noMutcons expression) : noMutcons output := by
  cases expression with
  | var n =>
    simp [BviTailrec.rewriteSource.eq_def] at result
    obtain ⟨_, rfl⟩ := result
    simp [noMutcons]
  | force l n =>
    simp [BviTailrec.rewriteSource.eq_def] at result
    obtain ⟨_, rfl⟩ := result
    simp [noMutcons]
  | ifThenElse cond yes no =>
    have parts : noMutcons cond ∧ noMutcons yes ∧ noMutcons no := by simpa [noMutcons] using safe
    rw [BviTailrec.rewriteSource.eq_def] at result
    dsimp only at result
    generalize hy : BviTailrec.rewriteSource loc next op acc _ yes = y at result
    generalize hn : BviTailrec.rewriteSource loc next op acc _ no = n at result
    obtain ⟨yf, ye⟩ := y
    obtain ⟨nf, ne⟩ := n
    have ys := tailrec_rewrite_noMutcons loc next op acc _ yes yf ye hy parts.2.1
    have ns := tailrec_rewrite_noMutcons loc next op acc _ no nf ne hn parts.2.2
    simp only [Prod.mk.injEq] at result
    obtain ⟨_, rfl⟩ := result
    simp only [noMutcons]
    refine ⟨parts.1, ?_, ?_⟩
    · cases yf <;> simp_all [tailrec_applyOp_noMutcons, noMutcons]
    · cases nf <;> simp_all [tailrec_applyOp_noMutcons, noMutcons]
  | «let» xs body =>
    have parts : (∀ e ∈ xs, noMutcons e) ∧ noMutcons body := by
      simpa [noMutcons, Subtype.forall] using safe
    rw [BviTailrec.rewriteSource.eq_def] at result
    dsimp only at result
    generalize hr : BviTailrec.rewriteSource loc next op (acc + xs.length) _ body = r at result
    obtain ⟨rf, re⟩ := r
    have rs := tailrec_rewrite_noMutcons loc next op (acc + xs.length) _ body rf re hr parts.2
    simp only [Prod.mk.injEq] at result
    obtain ⟨_, rfl⟩ := result
    simpa [noMutcons, Subtype.forall] using And.intro parts.1 rs
  | tick body =>
    rw [BviTailrec.rewriteSource.eq_def] at result
    dsimp only at result
    generalize hr : BviTailrec.rewriteSource loc next op acc ctx body = r at result
    obtain ⟨rf, re⟩ := r
    have rs := tailrec_rewrite_noMutcons loc next op acc ctx body rf re hr (by simpa [noMutcons] using safe)
    simp only [Prod.mk.injEq] at result
    obtain ⟨_, rfl⟩ := result
    simpa [noMutcons] using rs
  | raise body => exact tailrec_dispatch_noMutcons ctx op loc next acc _ flag output (by simpa [BviTailrec.rewriteSource.eq_def] using result) safe
  | call ticks dest args handler => exact tailrec_dispatch_noMutcons ctx op loc next acc _ flag output (by simpa [BviTailrec.rewriteSource.eq_def] using result) safe
  | op actual args => exact tailrec_dispatch_noMutcons ctx op loc next acc _ flag output (by simpa [BviTailrec.rewriteSource.eq_def] using result) safe
  | letCall ticks dest arity args body => exact tailrec_dispatch_noMutcons ctx op loc next acc _ flag output (by simpa [BviTailrec.rewriteSource.eq_def] using result) safe
  | «return» args => exact tailrec_dispatch_noMutcons ctx op loc next acc _ flag output (by simpa [BviTailrec.rewriteSource.eq_def] using result) safe
termination_by sizeOf expression

/-- Both bodies generated by the source expression pass remain free of
mutable-block allocation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "tailrec_compile_exp_no_mutcons"]
theorem tailrec_compileExp_noMutcons (loc next arity : Nat) (expression aux opt : Bvi.Exp)
    (result : BviTailrec.compileExpSource loc next arity expression = some (aux, opt))
    (safe : noMutcons expression) : noMutcons aux ∧ noMutcons opt := by
  unfold BviTailrec.compileExpSource at result
  cases checked : BviTailrec.checkExpOriginal loc arity expression with
  | none => simp [checked] at result
  | some op =>
    simp only [checked, Option.some.injEq, Prod.mk.injEq] at result
    obtain ⟨rfl, rfl⟩ := result
    let context : List BviTailrec.ValueType := List.replicate arity .any
    let rewritten := BviTailrec.rewriteSource loc next op arity context expression
    have workerSafe := tailrec_rewrite_noMutcons loc next op arity context expression
      rewritten.1 rewritten.2 (Prod.eta rewritten) safe
    exact ⟨(tailrec_letWrap_noMutcons arity _ _).mpr ⟨tailrec_identity_noMutcons op, workerSafe⟩,
      workerSafe⟩

/-- Tail-recursion compilation preserves the invariant over every function
body in the source-shaped function list. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bvi_tailrec_compile_each_no_mutcons"]
theorem tailrec_compileEach_noMutcons (next : Nat) (program : List (Nat × Nat × Bvi.Exp))
    (next' : Nat) (result : List (Nat × Nat × Bvi.Exp))
    (compiled : BviTailrec.compileEachSource next program = (next', result))
    (safe : ∀ entry ∈ program, noMutcons entry.2.2) :
    ∀ entry ∈ result, noMutcons entry.2.2 := by
  induction program generalizing next next' result with
  | nil =>
    simp [BviTailrec.compileEachSource] at compiled
    obtain ⟨_, rfl⟩ := compiled
    simp
  | cons entry rest ih =>
    obtain ⟨loc, arity, body⟩ := entry
    have bodySafe : noMutcons body := safe (loc, arity, body) (by simp)
    have restSafe : ∀ entry ∈ rest, noMutcons entry.2.2 := by
      intro entry member
      exact safe entry (by simp [member])
    cases decision : BviTailrec.compileExpSource loc next arity body with
    | none =>
      cases comp : BviTailrec.compileEachSource next rest with
      | mk last output =>
        simp [BviTailrec.compileEachSource, decision, comp] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        simpa using And.intro bodySafe (ih next last output comp restSafe)
    | some pair =>
      obtain ⟨aux, opt⟩ := pair
      have generated := tailrec_compileExp_noMutcons loc next arity body aux opt decision bodySafe
      cases comp : BviTailrec.compileEachSource (next + Flapjack.bvlToBviNamespaces) rest with
      | mk last output =>
        simp [BviTailrec.compileEachSource, decision, comp] at compiled
        obtain ⟨rfl, rfl⟩ := compiled
        simpa using And.intro generated.1 (And.intro generated.2
          (ih _ last output comp restSafe))

/-- Enabling or disabling the source program pass preserves the invariant. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "bvi_tailrec_compile_prog_no_mutcons"]
theorem tailrec_compileProg_noMutcons (enabled : Bool) (next next' : Nat)
    (program result : List (Nat × Nat × Bvi.Exp))
    (compiled : BviTailrec.compileProgSource enabled next program = (next', result))
    (safe : ∀ entry ∈ program, noMutcons entry.2.2) :
    ∀ entry ∈ result, noMutcons entry.2.2 := by
  cases enabled with
  | false =>
    simp [BviTailrec.compileProgSource] at compiled
    obtain ⟨_, rfl⟩ := compiled
    exact safe
  | true =>
    exact tailrec_compileEach_noMutcons next program next' result
      (by simpa [BviTailrec.compileProgSource] using compiled) safe

/-- The production bounded pass has the same preservation property. -/
theorem tailrec_compileProgFuel_noMutcons (fuel : Nat) (enabled : Bool) (next next' : Nat)
    (program result : List (Nat × Nat × Bvi.Exp))
    (compiled : BviTailrec.compileProgFuel fuel enabled next program = some (next', result))
    (safe : ∀ entry ∈ program, noMutcons entry.2.2) :
    ∀ entry ∈ result, noMutcons entry.2.2 := by
  rw [BviTailrec.compileProgFuel_eq_source] at compiled
  exact tailrec_compileProg_noMutcons enabled next next' program result (Option.some.inj compiled) safe

/-- The TMC precondition follows from safety of the tail-recursion input;
the pass itself preserves that safety. -/
theorem tailrec_output_tmc_inputCondition_of_input_noMutcons
    (fuel : Nat) (enabled : Bool) (next last tmcNext : Nat)
    (program output : List (Nat × Nat × Bvi.Exp)) (condition : BviTailrec.inputCondition next program)
    (outside : ∀ name ∈ program.map Prod.fst, bvlNumStubs ≤ name → ¬BviTmc.inWorkerNamespace name)
    (safe : ∀ entry ∈ program, noMutcons entry.2.2)
    (tmcBound : bvlNumStubs ≤ tmcNext) (tmcWorker : BviTmc.inWorkerNamespace tmcNext)
    (run : BviTailrec.compileProgFuel fuel enabled next program = some (last, output)) :
    BviTmc.inputCondition tmcNext output := by
  exact tailrec_output_tmc_inputCondition fuel enabled next last tmcNext program output condition outside
    (tailrec_compileProgFuel_noMutcons fuel enabled next last program output run safe) tmcBound tmcWorker run

private theorem noMutcons_binary (op : ClosLang.Op) (x y : Bvi.Exp)
    (safe : noMutconsOp op) (hx : noMutcons x) (hy : noMutcons y) :
    noMutcons (.op op [x, y]) := by
  simp [noMutcons, Subtype.forall, safe, hx, hy]

private theorem noMutcons_nullary (op : ClosLang.Op) (safe : noMutconsOp op) :
    noMutcons (.op op []) := by
  simp [noMutcons, Subtype.forall, safe]

/-- Every runtime stub is free of mutable-block allocation. This is the
initial-code portion of the source no-mutcons argument. -/
@[hol "cakeml/compiler/backend/proofs/bvl_to_bviProofScript.sml" "stubs_no_mutcons"]
theorem stubs_noMutcons (start count : Nat) :
    ∀ entry ∈ stubs start count, noMutcons entry.2.2 := by
  intro entry member
  simp [stubs] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [allocGlobalCode, copyGlobalsCode, initGlobalsCode, listLengthCode,
      fromListByteCode, toListByteCode, sumListLengthCode, concatByteCode,
      noMutcons, noMutconsOp, Subtype.forall]
  all_goals repeat' first
    | constructor
    | apply noMutcons_binary
    | apply noMutcons_nullary
    | simp [noMutcons, noMutconsOp, Subtype.forall]

/-- The production whole-program lowering emits safe stubs and functions. -/
theorem compileProgFuel_noMutcons (fuel optFuel start counter targetStart targetCounter : Nat)
    (program : List (Nat × Nat × Bvl.Exp)) (compiled : List (Nat × Nat × Bvi.Exp))
    (run : compileProgFuel fuel optFuel start counter program = some (targetStart, compiled, targetCounter)) :
    ∀ entry ∈ compiled, noMutcons entry.2.2 := by
  have equal := (compileProgFuel_eq_source fuel optFuel start counter program).symm.trans run
  have codeEq : stubs (bvlNumStubs + bvlToBviNamespaces * start)
      (globalCountList (program.map (fun (_, _, body) => body))) ++ (compileIncSource counter program).2 = compiled :=
    congrArg (fun p => p.2.1) (Option.some.inj equal)
  have lowered := compileIncSource_noMutcons counter (compileIncSource counter program).1 program
    (compileIncSource counter program).2 (Prod.eta _).symm
  intro entry member
  rw [← codeEq, List.mem_append] at member
  rcases member with stub | body
  · exact stubs_noMutcons _ _ entry stub
  · exact lowered entry body

/-- Production lowering followed by tail-recursion satisfies the complete
syntactic input condition required by TMC. -/
theorem lowered_tailrec_tmc_inputCondition_complete
    (fuel optFuel start counter targetStart targetCounter : Nat) (enabled : Bool)
    (program : List (Nat × Nat × Bvl.Exp)) (lowered output : List (Nat × Nat × Bvi.Exp))
    (last : Nat) (distinct : (program.map Prod.fst).Nodup)
    (lowerRun : compileProgFuel fuel optFuel start counter program = some (targetStart, lowered, targetCounter))
    (tailRun : BviTailrec.compileProgFuel fuel enabled (bvlNumStubs + 2) lowered = some (last, output)) :
    BviTmc.inputCondition (bvlNumStubs + 3) output := by
  apply lowered_tailrec_tmc_inputCondition fuel optFuel start counter targetStart targetCounter enabled
    program lowered output last distinct lowerRun tailRun
  exact tailrec_compileProgFuel_noMutcons fuel enabled _ last lowered output tailRun
    (compileProgFuel_noMutcons fuel optFuel start counter targetStart targetCounter program lowered lowerRun)

end Flapjack.Compiler.Backend.BvlToBvi.Proofs
