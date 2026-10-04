import Flapjack.Pancake.PanToTarget
import Flapjack.Pancake.Semantics.PanSem.Semantics

/-! Main-first reordering preserves Pancake declaration semantics.

HOL `compile_prog` (`pan_to_targetScript.sml:21-34`), and the CLI that compiles
`mainFirstHOL` of the parsed declarations, move the first `main` function to the front.
When the program contains a `main` function this does not change `semantics_decls`:
`decs_stcnames` ignores functions (`panSemScript.sml:855-856`), `evaluate_decls` checks a
function against the fixed struct context, expression evaluation does not read the code
map, and code updates for distinct names commute. Flapjack source-normalization
infrastructure; no HOL declaration states this. -/

namespace Flapjack.Pancake.PanToTarget
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.PanSemStateFiniteExact
set_option autoImplicit false

/-- Finite-map updates at distinct keys commute (Flapjack infrastructure). -/
theorem holFiniteMapExact_update_comm {α β : Type} [BEq α] [LawfulBEq α]
    (map : HolFiniteMapExact α β) (first second : α × β) (distinct : first.1 ≠ second.1) :
    (map.update first).update second = (map.update second).update first := by
  cases map
  simp only [HolFiniteMapExact.update, HolFiniteMapExact.mk.injEq]
  funext key
  simp only [FUPDATE]
  by_cases h1 : first.1 = key <;> by_cases h2 : second.1 = key <;> simp_all

variable {width : Nat} {σ : Type} [NeZero width]

/-- A function declaration commutes with an adjacent struct-name declaration. -/
theorem evaluateDeclsHOLFinite_nameCommute (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (fi : FunDeclHOL width) (struct : MlS)
    (fields : List (MlS × ShapeHOL)) (ds : List (DeclHOL width)) :
    evaluateDeclsHOLFinite state (.function fi :: .name struct fields :: ds) =
      evaluateDeclsHOLFinite state (.name struct fields :: .function fi :: ds) := by
  simp only [evaluateDeclsHOLFinite]

/-- A function declaration commutes with an adjacent exception declaration. -/
theorem evaluateDeclsHOLFinite_exnCommute (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (fi : FunDeclHOL width) (exception : MlS)
    (shape : ShapeHOL) (ds : List (DeclHOL width)) :
    evaluateDeclsHOLFinite state (.function fi :: .exnDecl exception shape :: ds) =
      evaluateDeclsHOLFinite state (.exnDecl exception shape :: .function fi :: ds) := by
  simp only [evaluateDeclsHOLFinite]
  by_cases hfun : (fi.params.all (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
      isWfShapeExactHOL state.structs fi.returnShape) = true <;>
    by_cases hexn : ((state.eshapes.lookup exception).isNone &&
      isWfShapeExactHOL state.structs shape) = true <;>
    simp only [hfun, hexn, if_true, if_false, Bool.false_eq_true]

/-- Function declarations with distinct names commute. -/
theorem evaluateDeclsHOLFinite_functionCommute (state : PanSemStateFiniteExact width σ)
    [DecidablePred state.memaddrs] (fi gi : FunDeclHOL width) (distinct : gi.name ≠ fi.name)
    (ds : List (DeclHOL width)) :
    evaluateDeclsHOLFinite state (.function fi :: .function gi :: ds) =
      evaluateDeclsHOLFinite state (.function gi :: .function fi :: ds) := by
  simp only [evaluateDeclsHOLFinite]
  by_cases hf : (fi.params.all (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
      isWfShapeExactHOL state.structs fi.returnShape) = true <;>
    by_cases hg : (gi.params.all (fun parameter => isWfShapeExactHOL state.structs parameter.2) &&
      isWfShapeExactHOL state.structs gi.returnShape) = true <;>
    simp only [hf, hg, if_true, if_false, Bool.false_eq_true]
  rw [holFiniteMapExact_update_comm _ _ _ (fun h => distinct h.symm)]

/-- Evaluation of a declaration list prefixed by one declaration respects extensional
equality of the tails (Flapjack infrastructure). -/
theorem evaluateDeclsHOLFinite_cons_congr (xs ys : List (DeclHOL width))
    (same : ∀ (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs],
      evaluateDeclsHOLFinite state xs = evaluateDeclsHOLFinite state ys)
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs]
    (d : DeclHOL width) :
    evaluateDeclsHOLFinite state (d :: xs) = evaluateDeclsHOLFinite state (d :: ys) := by
  cases d <;> simp only [evaluateDeclsHOLFinite]
  all_goals (repeat' split)
  all_goals first
    | rfl
    | (refine @same _ ?_ <;> exact h)

/-- Moving a function declaration to the front of a prefix containing no function of the
same name leaves declaration evaluation unchanged (Flapjack infrastructure). -/
theorem evaluateDeclsHOLFinite_moveFunction (fi : FunDeclHOL width)
    (rest : List (DeclHOL width)) :
    ∀ (before : List (DeclHOL width)),
      (∀ d ∈ before, ∀ gi : FunDeclHOL width, d = .function gi → gi.name ≠ fi.name) →
      ∀ (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs],
        evaluateDeclsHOLFinite state (before ++ .function fi :: rest) =
          evaluateDeclsHOLFinite state (.function fi :: (before ++ rest))
  | [], _, _, _ => rfl
  | d :: before, distinct, state, h => by
    have ih := evaluateDeclsHOLFinite_moveFunction fi rest before
      (fun d' member => distinct d' (List.mem_cons_of_mem _ member))
    simp only [List.cons_append]
    rw [evaluateDeclsHOLFinite_cons_congr _ _ (fun s inst => @ih s inst) state d]
    cases d with
    | name struct fields =>
      exact (evaluateDeclsHOLFinite_nameCommute state fi struct fields _).symm
    | decl shape name expression =>
      exact (evaluateDeclsHOLFinite_declCommute state fi shape name expression _).symm
    | function gi =>
      exact (evaluateDeclsHOLFinite_functionCommute state fi gi
        (distinct _ List.mem_cons_self gi rfl) _).symm
    | exnDecl exception shape =>
      exact (evaluateDeclsHOLFinite_exnCommute state fi exception shape _).symm

/-- `decs_stcnames` ignores function declarations, so moving one does not change the
struct context (Flapjack infrastructure). -/
theorem decsStcnamesHOLExact_dropFunction (fi : FunDeclHOL width)
    (rest : List (DeclHOL width)) :
    ∀ (before : List (DeclHOL width)) (context : StructContextExact),
      decsStcnamesHOLExact (width := width) context (before ++ .function fi :: rest) =
        decsStcnamesHOLExact (width := width) context (before ++ rest)
  | [], context => by simp only [List.nil_append, decsStcnamesHOLExact]
  | d :: before, context => by
    have ih := decsStcnamesHOLExact_dropFunction fi rest before
    cases d <;> simp only [List.cons_append, decsStcnamesHOLExact, ih]
    all_goals (repeat' split) <;> simp only [ih]

/-! List facts for `mainFirstHOL`'s `List.span` (Flapjack infrastructure). -/

theorem spanLoop_eq_takeWhile_dropWhile {α : Type} (p : α → Bool) :
    ∀ (l acc : List α), List.span.loop p l acc = (acc.reverse ++ l.takeWhile p, l.dropWhile p)
  | [], acc => by simp [List.span.loop]
  | a :: l, acc => by
    unfold List.span.loop
    cases h : p a <;>
      simp [h, List.takeWhile, List.dropWhile, spanLoop_eq_takeWhile_dropWhile p l]

theorem span_eq_takeWhile_dropWhile {α : Type} (p : α → Bool) (l : List α) :
    l.span p = (l.takeWhile p, l.dropWhile p) := by
  simp [List.span, spanLoop_eq_takeWhile_dropWhile]

theorem mem_takeWhile_pred {α : Type} (p : α → Bool) :
    ∀ (l : List α) (x : α), x ∈ l.takeWhile p → p x = true
  | [], x, h => by simp at h
  | a :: l, x, h => by
    unfold List.takeWhile at h
    cases ha : p a <;> simp [ha] at h
    rcases h with rfl | h
    · exact ha
    · exact mem_takeWhile_pred p l x h

theorem dropWhile_eq_nil_pred {α : Type} (p : α → Bool) :
    ∀ (l : List α), l.dropWhile p = [] → ∀ x ∈ l, p x = true
  | [], _, x, hx => by simp at hx
  | a :: l, h, x, hx => by
    unfold List.dropWhile at h
    cases ha : p a <;> simp [ha] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact dropWhile_eq_nil_pred p l h x hx

/-- The first `main` function exists: the program splits around it with no `main`
function before it, and `mainFirstHOL` moves it to the front (Flapjack infrastructure). -/
theorem mainFirstHOL_of_main (program : List (DeclHOL width))
    (hasMain : ∃ fi : FunDeclHOL width, .function fi ∈ program ∧ fi.name = ofString "main") :
    ∃ (before : List (DeclHOL width)) (fi : FunDeclHOL width) (rest : List (DeclHOL width)),
      program = before ++ .function fi :: rest ∧
      (∀ d ∈ before, ∀ gi : FunDeclHOL width, d = .function gi → gi.name ≠ fi.name) ∧
      mainFirstHOL program = .function fi :: (before ++ rest) := by
  let notMain : DeclHOL width → Bool := fun declaration =>
    match declaration with
    | .function entry => decide (entry.name ≠ ofString "main")
    | _ => true
  have split : program = program.takeWhile notMain ++ program.dropWhile notMain :=
    (List.takeWhile_append_dropWhile).symm
  cases dropped : program.dropWhile notMain with
  | nil =>
    obtain ⟨fi, member, named⟩ := hasMain
    have all := dropWhile_eq_nil_pred notMain program dropped _ member
    simp [notMain, named] at all
  | cons main rest =>
    have stops : notMain main = false := by
      have := List.head_dropWhile_not notMain (l := program) (by simp [dropped])
      simpa [dropped] using this
    cases main with
    | function fi =>
      have named : fi.name = ofString "main" := by simpa [notMain] using stops
      refine ⟨program.takeWhile notMain, fi, rest, by rw [← dropped]; exact split, ?_, ?_⟩
      · intro d member gi same
        subst same
        have := mem_takeWhile_pred notMain program _ member
        simp only [notMain, decide_eq_true_eq] at this
        rw [named]
        exact this
      · unfold mainFirstHOL
        rw [span_eq_takeWhile_dropWhile]
        split
        next _ before after heq =>
          obtain ⟨hT, hD⟩ := Prod.mk.inj heq
          have hT' : before = program.takeWhile notMain := hT.symm
          have hD' : after = .function fi :: rest := hD.symm.trans dropped
          subst hD'
          rw [← hT']
          cases before <;> rfl
    | name _ _ => simp [notMain] at stops
    | decl _ _ _ => simp [notMain] at stops
    | exnDecl _ _ => simp [notMain] at stops

/-- Main-first reordering preserves `semantics_decls` whenever the program contains a
`main` function (Flapjack source-normalization theorem; no HOL original). Without a `main`
function `mainFirstHOL` inserts a default `main`, which genuinely changes the semantics. -/
theorem semanticsDecls_mainFirstHOL (s : PanSemStateFiniteExact width σ) (start : MlS)
    (program : List (DeclHOL width))
    (hasMain : ∃ fi : FunDeclHOL width, .function fi ∈ program ∧ fi.name = ofString "main") :
    semanticsDecls s start (mainFirstHOL program) = semanticsDecls s start program := by
  obtain ⟨before, fi, rest, rfl, distinct, moved⟩ := mainFirstHOL_of_main program hasMain
  rw [moved]
  unfold semanticsDecls
  have structsSame : decsStcnamesHOLExact (width := width) [] (.function fi :: (before ++ rest)) =
      decsStcnamesHOLExact [] (before ++ .function fi :: rest) := by
    rw [decsStcnamesHOLExact_dropFunction]
    simp only [decsStcnamesHOLExact]
  rw [structsSame]
  split
  · rfl
  · rw [evaluateDeclsHOLFinite_moveFunction fi rest before distinct]

end Flapjack.Pancake.PanToTarget
