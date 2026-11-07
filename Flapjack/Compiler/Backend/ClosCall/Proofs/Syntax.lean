import Flapjack.Compiler.Backend.ClosCall.Proofs.CodeList
import Flapjack.Compiler.Backend.ClosCall.Proofs.IncrementalOracle
import Flapjack.Compiler.Backend.Semantics.ClosProps.FnAnnotations

/-! Syntax invariants for direct-call generated code. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack ClosLang ClosProps

/-- A closure expression retains numbered functions and no free-variable
annotations. This is Flapjack-specific proof infrastructure. -/
def CallSyntax (e : ClosLang.Exp) : Prop := fnLocationSomeExp e ∧ fnVarsNoneExp e

/-- All auxiliary function bodies satisfy the source closure syntax.
This is Flapjack-specific proof infrastructure. -/
def AuxSyntax (state : State) : Prop :=
  ∀ name arity body, (name, arity, body) ∈ state.2 → CallSyntax body

/-- Generated argument variables have no closure annotations or locations. -/
theorem variables_callSyntax (trace : BackendCommon.Tra) (arity : Nat) :
    everyFnLocationSome (ClosCall.variables trace arity) ∧ everyFnVarsNone (ClosCall.variables trace arity) := by
  have helper : ∀ values : List Nat,
      everyFnLocationSome (values.map (.var trace)) ∧ everyFnVarsNone (values.map (.var trace)) := by
    intro values
    induction values with
    | nil => simp [everyFnLocationSome, everyFnVarsNone]
    | cons head tail ih => simp [everyFnLocationSome, everyFnVarsNone, fnLocationSomeExp, fnVarsNoneExp, ih]
  exact helper (List.range arity)

/-- Generated direct-call stubs have the required closure syntax. -/
theorem callsList_callSyntax (loc : Nat) (fns : List (Nat × ClosLang.Exp)) :
    fnLocationSomeFuns (callsList loc fns) ∧ fnVarsNoneFuns (callsList loc fns) := by
  have helper : ∀ pairs : List ((Nat × ClosLang.Exp) × Nat),
      fnLocationSomeFuns (pairs.map (fun ((arity, _), i) =>
        (arity, .call .none 0 (loc + 2 * i + 1) (ClosCall.variables .none arity)))) ∧
      fnVarsNoneFuns (pairs.map (fun ((arity, _), i) =>
        (arity, .call .none 0 (loc + 2 * i + 1) (ClosCall.variables .none arity)))) := by
    intro pairs
    induction pairs with
    | nil => simp [fnLocationSomeFuns, fnVarsNoneFuns]
    | cons pair rest ih =>
      obtain ⟨⟨arity, body⟩, i⟩ := pair
      simpa [fnLocationSomeFuns, fnVarsNoneFuns, fnLocationSomeExp, fnVarsNoneExp,
        (variables_callSyntax .none arity).1, (variables_callSyntax .none arity).2] using ih
  exact helper (fns.zip (List.range fns.length))

/-- Adding a sequence of safe bodies to the source-shaped auxiliary list
preserves auxiliary syntax safety. -/
theorem codeListSource_auxSyntax (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (state : State)
    (oldSafe : AuxSyntax state) (newSafe : ∀ p ∈ fns, CallSyntax p.2) :
    AuxSyntax (codeListSource loc fns state) := by
  induction fns generalizing loc state with
  | nil => simpa [codeListSource] using oldSafe
  | cons p rest ih =>
    obtain ⟨arity, body⟩ := p
    have headSafe : CallSyntax body := newSafe (arity, body) (by simp)
    have tailSafe : ∀ p ∈ rest, CallSyntax p.2 := by
      intro p member
      exact newSafe p (by simp [member])
    have extended : AuxSyntax (state.1, (loc + 1, arity, body) :: state.2) := by
      intro name arity' body' member
      simp only [List.mem_cons, Prod.mk.injEq] at member
      rcases member with ⟨rfl, rfl, rfl⟩ | old
      · exact headSafe
      · exact oldSafe name arity' body' old
    simpa [codeListSource] using ih (loc + 2) _ extended tailSafe

/-- The executed auxiliary-code builder preserves syntax safety. -/
theorem codeList_auxSyntax (loc : Nat) (fns : List (Nat × ClosLang.Exp)) (state : State)
    (oldSafe : AuxSyntax state) (newSafe : ∀ p ∈ fns, CallSyntax p.2) :
    AuxSyntax (codeList loc fns state) := by
  rw [codeList_eq_source]
  exact codeListSource_auxSyntax loc fns state oldSafe newSafe


/-- Safety of every expression in a closure list. -/
def ListCallSyntax (es : List ClosLang.Exp) : Prop := everyFnLocationSome es ∧ everyFnVarsNone es

/-- Appending safe expression lists preserves their syntax. -/
theorem listCallSyntax_append (xs ys : List ClosLang.Exp) (x : ListCallSyntax xs) (y : ListCallSyntax ys) :
    ListCallSyntax (xs ++ ys) := by
  induction xs with
  | nil => simpa using y
  | cons e es ih =>
    simp only [ListCallSyntax, everyFnLocationSome, everyFnVarsNone] at x ⊢
    have tail := ih ⟨x.1.2, x.2.2⟩
    simpa [everyFnLocationSome, everyFnVarsNone] using And.intro (And.intro x.1.1 tail.1) (And.intro x.2.1 tail.2)

/-- A safe body list gives safe bodies to any zipped arity list. -/
theorem zip_bodies_callSyntax (arities : List Nat) (bodies : List ClosLang.Exp) (safe : ListCallSyntax bodies) :
    ∀ p ∈ arities.zip bodies, CallSyntax p.2 := by
  induction arities generalizing bodies with
  | nil => simp
  | cons arity rest ih =>
    cases bodies with
    | nil => simp
    | cons body bodies =>
      simp only [ListCallSyntax, everyFnLocationSome, everyFnVarsNone] at safe
      intro p member
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨safe.1.1, safe.2.1⟩
      · exact ih bodies ⟨safe.1.2, safe.2.2⟩ p member

/-- A list of individually safe recursive bodies satisfies both group
syntax predicates. -/
theorem funs_callSyntax_of_forall (fns : List (Nat × ClosLang.Exp)) (safe : ∀ p ∈ fns, CallSyntax p.2) :
    fnLocationSomeFuns fns ∧ fnVarsNoneFuns fns := by
  induction fns with
  | nil => simp [fnLocationSomeFuns, fnVarsNoneFuns]
  | cons p rest ih =>
    obtain ⟨arity, body⟩ := p
    have head := safe (arity, body) (by simp)
    have tail := ih (by intro p member; exact safe p (by simp [member]))
    simpa [fnLocationSomeFuns, fnVarsNoneFuns] using
      And.intro (And.intro head.1 tail.1) (And.intro head.2 tail.2)

mutual
/-- A successful direct-call expression traversal preserves syntax of its
output and auxiliary bodies. This is Flapjack-specific infrastructure. -/
theorem callsFuel_callSyntax (fuel : Nat) (e out : ClosLang.Exp) (initial final : State)
    (run : callsFuel fuel e initial = some (out, final)) (safe : CallSyntax e) (aux : AuxSyntax initial) :
    CallSyntax out ∧ AuxSyntax final := by
  cases fuel with
  | zero => simp [callsFuel] at run
  | succ fuel =>
    cases e with
    | var trace index =>
      simp [callsFuel] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨safe, aux⟩
    | ifThenElse trace x y z =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨x', s1⟩, hx, ⟨y', s2⟩, hy, ⟨z', s3⟩, hz, rfl, rfl⟩ := run
      simp only [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] at safe ⊢
      obtain ⟨sx, a1⟩ := callsFuel_callSyntax fuel x x' initial s1 hx ⟨safe.1.1, safe.2.1⟩ aux
      obtain ⟨sy, a2⟩ := callsFuel_callSyntax fuel y y' s1 s2 hy ⟨safe.1.2.1, safe.2.2.1⟩ a1
      obtain ⟨sz, a3⟩ := callsFuel_callSyntax fuel z z' s2 s3 hz ⟨safe.1.2.2, safe.2.2.2⟩ a2
      exact ⟨⟨⟨sx.1, sy.1, sz.1⟩, ⟨sx.2, sy.2, sz.2⟩⟩, a3⟩
    | «let» trace xs body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨body', s2⟩, hb, rfl, rfl⟩ := run
      simp only [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] at safe ⊢
      obtain ⟨sx, a1⟩ := callsListFuel_callSyntax fuel xs xs' initial s1 hx ⟨safe.1.2, safe.2.2⟩ aux
      obtain ⟨sb, a2⟩ := callsFuel_callSyntax fuel body body' s1 s2 hb ⟨safe.1.1, safe.2.1⟩ a1
      exact ⟨⟨⟨sb.1, sx.1⟩, ⟨sb.2, sx.2⟩⟩, a2⟩
    | raise trace body | tick trace body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨body', s1⟩, hb, rfl, rfl⟩ := run
      simpa [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] using
        callsFuel_callSyntax fuel body body' initial s1 hb (by simpa [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] using safe) aux
    | handle trace body handler =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨body', s1⟩, hb, ⟨handler', s2⟩, hh, rfl, rfl⟩ := run
      simp only [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] at safe ⊢
      obtain ⟨sb, a1⟩ := callsFuel_callSyntax fuel body body' initial s1 hb ⟨safe.1.1, safe.2.1⟩ aux
      obtain ⟨sh, a2⟩ := callsFuel_callSyntax fuel handler handler' s1 s2 hh ⟨safe.1.2, safe.2.2⟩ a1
      exact ⟨⟨⟨sb.1, sh.1⟩, ⟨sb.2, sh.2⟩⟩, a2⟩
    | call trace ticks dest xs | op trace dest xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨xs', s1⟩, hx, rfl, rfl⟩ := run
      simpa [CallSyntax, ListCallSyntax, fnLocationSomeExp, fnVarsNoneExp] using
        callsListFuel_callSyntax fuel xs xs' initial s1 hx (by simpa [CallSyntax, ListCallSyntax, fnLocationSomeExp, fnVarsNoneExp] using safe) aux
    | app trace loc fn xs =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨xs', s1⟩, hx, ⟨fn', s2⟩, hf, rest⟩ := run
      simp only [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] at safe
      obtain ⟨sx, a1⟩ := callsListFuel_callSyntax fuel xs xs' initial s1 hx ⟨safe.1.2, safe.2.2⟩ aux
      obtain ⟨sf, a2⟩ := callsFuel_callSyntax fuel fn fn' s1 s2 hf ⟨safe.1.1, safe.2.1⟩ a1
      cases loc <;> simp only at rest
      all_goals repeat' split at rest
      all_goals simp only [Option.some.injEq, Prod.mk.injEq] at rest
      all_goals obtain ⟨rfl, rfl⟩ := rest
      all_goals have vs := variables_callSyntax .none xs'.length
      all_goals have combined := listCallSyntax_append xs' [fn'] sx ⟨by simpa [everyFnLocationSome] using sf.1, by simpa [everyFnVarsNone] using sf.2⟩
      all_goals simp only [CallSyntax, ListCallSyntax, fnLocationSomeExp, fnVarsNoneExp] at *
      all_goals aesop

    | fn name loc vars arity body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨body', s1⟩, hb, closed, _, rest⟩ := run
      simp only [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] at safe
      have bodySafe : CallSyntax body := ⟨safe.1.2, safe.2.2⟩
      have inserted : AuxSyntax (insertEach (loc.getD 0) 1 initial) := by simpa [AuxSyntax, insertEach] using aux
      obtain ⟨bodySafe', aux1⟩ := callsFuel_callSyntax fuel body body' _ s1 hb bodySafe inserted
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body'', s2⟩, hb', rfl, rfl⟩ := rest
        obtain ⟨bodySafe'', aux2⟩ := callsFuel_callSyntax fuel body body'' initial s2 hb' bodySafe aux
        simpa [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] using
          And.intro (And.intro (And.intro safe.1.1 bodySafe''.1) (And.intro safe.2.1 bodySafe''.2)) aux2
      | true =>
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨rfl, rfl⟩ := rest
        have generated : AuxSyntax (s1.1, (loc.getD 0 + 1, arity, body') :: s1.2) := by
          intro n a b member
          simp only [List.mem_cons, Prod.mk.injEq] at member
          rcases member with ⟨rfl, rfl, rfl⟩ | old
          · exact bodySafe'
          · exact aux1 n a b old
        have vs := variables_callSyntax .none arity
        simpa [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] using
          And.intro (And.intro (And.intro safe.1.1 vs.1) (And.intro safe.2.1 vs.2)) generated
    | letrec names loc vars fns body =>
      simp only [callsFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure] at run
      obtain ⟨⟨bodies, s1⟩, hb, closed, _, rest⟩ := run
      simp only [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] at safe
      have groupSafe : ListCallSyntax (fns.map Prod.snd) :=
        ⟨(fnLocationSomeFuns_eq_map fns).1 safe.1.2.1, (fnVarsNoneFuns_eq_map fns).1 safe.2.2.1⟩
      have bodySafe : CallSyntax body := ⟨safe.1.2.2, safe.2.2.2⟩
      have inserted : AuxSyntax (insertEach (loc.getD 0) fns.length initial) := by simpa [AuxSyntax, insertEach] using aux
      obtain ⟨bodiesSafe, aux1⟩ := callsListFuel_callSyntax fuel (fns.map Prod.snd) bodies _ s1 hb groupSafe inserted
      cases closed with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨bodies', s2⟩, hb', ⟨body', s3⟩, he, rfl, rfl⟩ := rest
        obtain ⟨bodiesSafe', aux2⟩ := callsListFuel_callSyntax fuel (fns.map Prod.snd) bodies' initial s2 hb' groupSafe aux
        obtain ⟨bodySafe', aux3⟩ := callsFuel_callSyntax fuel body body' s2 s3 he bodySafe aux2
        have groups := funs_callSyntax_of_forall ((fns.map Prod.fst).zip bodies') (zip_bodies_callSyntax _ _ bodiesSafe')
        simpa [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] using
          And.intro (And.intro (And.intro safe.1.1 (And.intro groups.1 bodySafe'.1))
            (And.intro safe.2.1 (And.intro groups.2 bodySafe'.2))) aux3
      | true =>
        simp only [↓reduceIte, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at rest
        obtain ⟨⟨body', s2⟩, he, rfl, rfl⟩ := rest
        have auxGenerated := codeList_auxSyntax (loc.getD 0) ((fns.map Prod.fst).zip bodies) s1 aux1
          (zip_bodies_callSyntax _ _ bodiesSafe)
        obtain ⟨bodySafe', aux2⟩ := callsFuel_callSyntax fuel body body' _ s2 he bodySafe auxGenerated
        have groups := callsList_callSyntax (loc.getD 0) fns
        simpa [CallSyntax, fnLocationSomeExp, fnVarsNoneExp] using
          And.intro (And.intro (And.intro safe.1.1 (And.intro groups.1 bodySafe'.1))
            (And.intro safe.2.1 (And.intro groups.2 bodySafe'.2))) aux2
termination_by fuel

/-- A successful direct-call list traversal preserves list and auxiliary
syntax. This is Flapjack-specific infrastructure. -/
theorem callsListFuel_callSyntax (fuel : Nat) (es out : List ClosLang.Exp) (initial final : State)
    (run : callsListFuel fuel es initial = some (out, final)) (safe : ListCallSyntax es) (aux : AuxSyntax initial) :
    ListCallSyntax out ∧ AuxSyntax final := by
  cases es with
  | nil =>
    simp [callsListFuel] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨safe, aux⟩
  | cons e es =>
    cases fuel with
    | zero => simp [callsListFuel] at run
    | succ fuel =>
      simp only [callsListFuel, Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨⟨e', s1⟩, he, ⟨es', s2⟩, hs, rfl, rfl⟩ := run
      simp only [ListCallSyntax, everyFnLocationSome, everyFnVarsNone] at safe ⊢
      obtain ⟨se, a1⟩ := callsFuel_callSyntax fuel e e' initial s1 he ⟨safe.1.1, safe.2.1⟩ aux
      obtain ⟨ss, a2⟩ := callsListFuel_callSyntax fuel es es' s1 s2 hs ⟨safe.1.2, safe.2.2⟩ a1
      exact ⟨⟨⟨se.1, ss.1⟩, ⟨se.2, ss.2⟩⟩, a2⟩
termination_by fuel
end


/-- The production retry traversal preserves source syntax and auxiliary
syntax for either the initial attempt or its structural retry. -/
theorem callsListBounded_callSyntax (fuel : Nat) (es out : List ClosLang.Exp) (initial final : State)
    (run : callsListBounded fuel es initial = some (out, final))
    (safe : ListCallSyntax es) (aux : AuxSyntax initial) : ListCallSyntax out ∧ AuxSyntax final := by
  unfold callsListBounded at run
  cases first : callsListFuel fuel es initial with
  | none =>
    exact callsListFuel_callSyntax _ es out initial final (by simpa [first] using run) safe aux
  | some result =>
    have eq : result = (out, final) := by simpa [first] using run
    subst result
    exact callsListFuel_callSyntax fuel es out initial final first safe aux

/-- The enabled production pass preserves syntax for both its output and
its generated auxiliary functions. -/
theorem compileFuel_callSyntax (fuel : Nat) (es out : List ClosLang.Exp) (final : State)
    (run : compileFuel fuel true es = some (out, final)) (safe : ListCallSyntax es) :
    ListCallSyntax out ∧ AuxSyntax final := by
  have emptyAux : AuxSyntax ((.ln, []) : State) := by simp [AuxSyntax]
  apply callsListBounded_callSyntax fuel es out (.ln, []) final ?_ safe emptyAux
  simpa [compileFuel] using run

/-- Incremental direct-call compilation preserves syntax for both output
expressions and generated auxiliary functions. -/
theorem compileIncFuel_callSyntax (fuel : Nat) (known nextKnown : NumSet)
    (program converted : ClosSem.Program)
    (run : compileIncFuel? fuel known program = some (nextKnown, converted))
    (safe : ListCallSyntax program.1) :
    ListCallSyntax converted.1 ∧ AuxSyntax (nextKnown, converted.2) := by
  simp only [compileIncFuel?, Bind.bind, Option.bind_eq_some_iff, Pure.pure,
    Option.some.injEq, Prod.mk.injEq] at run
  obtain ⟨⟨output, state⟩, traversal, knownEq, outputEq, auxEq⟩ := run
  subst nextKnown
  simpa using callsListBounded_callSyntax fuel program.1 output (known, []) state traversal safe (by simp [AuxSyntax])

/-- Every entry in the transformed incremental oracle carries numbered,
unannotated closure expressions and auxiliary functions when the source
oracle does. -/
theorem compileIncFuelOracle_callSyntax {C : Type} (fuel : Nat)
    (oracle : ClosSem.CompileOracle (NumSet × C))
    (safe : ∀ index, ListCallSyntax (oracle index).2.1) :
    ∀ index, ListCallSyntax (compileIncFuelOracle fuel oracle index).2.1 ∧
      AuxSyntax ((compileIncFuelTotal fuel (oracle index).1.1 (oracle index).2).1,
        (compileIncFuelOracle fuel oracle index).2.2) := by
  intro index
  obtain ⟨nextKnown, run, _⟩ := compileIncFuelOracle_entry fuel oracle index
  have result := compileIncFuel_callSyntax fuel (oracle index).1.1 nextKnown (oracle index).2
    (compileIncFuelOracle fuel oracle index).2 run (safe index)
  have nextEq : nextKnown = (compileIncFuelTotal fuel (oracle index).1.1 (oracle index).2).1 := by
    have total := compileIncFuel_eq_total fuel (oracle index).1.1 (oracle index).2
    rw [run] at total
    exact congrArg Prod.fst (Option.some.inj total)
  simpa [nextEq] using result


/-- Auxiliary syntax safety implies list syntax safety for the extracted
bodies. -/
theorem auxSyntax_bodies (state : State) (safe : AuxSyntax state) :
    ListCallSyntax (state.2.map (fun (_, _, body) => body)) := by
  have helper : ∀ entries : List (Nat × Nat × ClosLang.Exp),
      (∀ name arity body, (name, arity, body) ∈ entries → CallSyntax body) →
      ListCallSyntax (entries.map (fun (_, _, body) => body)) := by
    intro entries
    induction entries with
    | nil => simp [ListCallSyntax, everyFnLocationSome, everyFnVarsNone]
    | cons entry rest ih =>
      obtain ⟨name, arity, body⟩ := entry
      intro all
      have head := all name arity body (by simp)
      have tail := ih (by intro n a b member; exact all n a b (by simp [member]))
      simpa [ListCallSyntax, everyFnLocationSome, everyFnVarsNone] using
        And.intro (And.intro head.1 tail.1) (And.intro head.2 tail.2)
  exact helper state.2 safe

end Flapjack.Compiler.Backend.ClosCall
