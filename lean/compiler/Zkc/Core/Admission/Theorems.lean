module

public import Zkc.Core.Admission.Programs
public import Zkc.Core.Meaning.Stops

@[expose] public section

/-!
The statements of `Statements.lean` about functions, proved of `admit`, `check` and
`elaborateFunctions`.

Admission checks one definition at a time, each against the headers before it: so what it
returns is the elaboration of what was given (`admitsWhatWasGiven`), and the check of each
definition in order gives its headers (`checkAgrees`). Every definition that it accepts is a
function whose body the check of facts accepts, so the program is `Defs.Accepted` with its
annotation, and the theorem of the check of facts for a program gives `functionsSafe`,
`functionsKeepValidity` and `annotationHolds`. A function whose header says that it cannot stop
stops only `undefined` (`Defs.fnTable_stops_undefined`), and never that, so it does not stop
(`headersSayWhoStops`).
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-! ## What a step gives -/

theorem ok_of_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : x.bind f = .ok y) : ∃ v, x = .ok v ∧ f v = .ok y := by
  cases x with
  | error _ => cases h
  | ok v => exact ⟨v, rfl, h⟩

theorem ok_of_map {ε α β : Type} {x : Except ε α} {f : α → β} {y : β}
    (h : x.map f = .ok y) : ∃ v, x = .ok v ∧ f v = y := by
  cases x with
  | error _ => cases h
  | ok v => exact ⟨v, rfl, Except.ok.inj h⟩

/-- A definition that the check accepts is elaborated, and is a function whose body the check of
facts accepts with the bounds given. -/
theorem checkDefinition_fn {hs : Headers V} {definition : Definition V} {e : Elaborated V hs}
    {bounds : List (Place × Nat)} (h : checkDefinition hs definition = .ok (e, bounds)) :
    elaborateDefinition hs definition = .ok e ∧ ∃ hdr body ok fresh, e = .fn hdr body ok fresh ∧
      checkFacts (localFactRules V hs.fns) hdr.key none body = .ok bounds := by
  obtain ⟨e', elaborated, checked⟩ := ok_of_bind h
  obtain ⟨b, facts, same⟩ := ok_of_map checked
  cases same
  refine ⟨elaborated, ?_⟩
  cases e with
  | fn hdr body ok fresh => exact ⟨hdr, body, ok, fresh, rfl, facts⟩
  | protocol => cases facts

/-- The headers of a program with a definition are the definition's. -/
theorem Typed.add_headers (p : Typed V) (e : Elaborated V p.headers) :
    (p.add e).headers = e.headers := by
  cases e <;> rfl

/-- What admission gives: the program that its checks give, its bounds and the association
resolved in it. -/
theorem admit_ok {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (h : admit named assoc = .ok a) :
    ∃ q bounds resolved, admitFrom .empty [] named.definitions = .ok (q, bounds) ∧
      resolve q assoc = .ok resolved ∧ a = ⟨q, ⟨bounds⟩, resolved⟩ := by
  obtain ⟨⟨q, bounds⟩, admitted, resolvedOk⟩ := ok_of_bind h
  obtain ⟨resolved, found, same⟩ := ok_of_map resolvedOk
  exact ⟨q, bounds, resolved, admitted, found, same.symm⟩

/-! ## What the checks in order give -/

/-- The checks in order elaborate the definitions in order. -/
theorem admitFrom_elaborates : ∀ (p : Typed V) (bounds : List (Place × Nat))
    (definitions : List (Definition V)) (q : Typed V) (bounds' : List (Place × Nat)),
    admitFrom p bounds definitions = .ok (q, bounds') → elaborateFrom p definitions = .ok q
  | p, bounds, [], q, bounds', h => by
      cases h
      rfl
  | p, bounds, definition :: rest, q, bounds', h => by
      obtain ⟨⟨e, mine⟩, checked, later⟩ := ok_of_bind h
      have elaborated := (checkDefinition_fn checked).1
      simp only [elaborateFrom, elaborated]
      exact admitFrom_elaborates (p.add e) (mine ++ bounds) rest q bounds' later

/-- The checks in order give the headers of the program, one definition at a time. -/
theorem admitFrom_checkAll : ∀ (p : Typed V) (bounds : List (Place × Nat))
    (definitions : List (Definition V)) (q : Typed V) (bounds' : List (Place × Nat)),
    admitFrom p bounds definitions = .ok (q, bounds') →
      checkAll check p.headers definitions = .ok q.headers
  | p, bounds, [], q, bounds', h => by
      cases h
      rfl
  | p, bounds, definition :: rest, q, bounds', h => by
      obtain ⟨⟨e, mine⟩, checked, later⟩ := ok_of_bind h
      have one : check p.headers definition = .ok e.headers := by
        simp only [check, checked, Except.map]
      simp only [checkAll, one, Except.bind]
      rw [← Typed.add_headers p e]
      exact admitFrom_checkAll (p.add e) (mine ++ bounds) rest q bounds' later

/-- The checks in order keep the program accepted by the check of facts, with the bounds that
they gather. -/
theorem admitFrom_accepted : ∀ (p : Typed V) (bounds : List (Place × Nat))
    (definitions : List (Definition V)) (q : Typed V) (bounds' : List (Place × Nat)),
    Defs.Accepted p.defs bounds → admitFrom p bounds definitions = .ok (q, bounds') →
      Defs.Accepted q.defs bounds'
  | p, bounds, [], q, bounds', accepted, h => by
      cases h
      exact accepted
  | p, bounds, definition :: rest, q, bounds', accepted, h => by
      obtain ⟨⟨e, mine⟩, checked, later⟩ := ok_of_bind h
      obtain ⟨hdr, body, ok, fresh, same, facts⟩ := (checkDefinition_fn checked).2
      subst same
      exact admitFrom_accepted (p.add (.fn hdr body ok fresh)) (mine ++ bounds) rest q bounds'
        ⟨mine, bounds, facts, accepted, rfl⟩ later

/-- The checks in order add no protocol. -/
theorem admitFrom_functions : ∀ (p : Typed V) (bounds : List (Place × Nat))
    (definitions : List (Definition V)) (q : Typed V) (bounds' : List (Place × Nat)),
    p.headers.protocols = [] → admitFrom p bounds definitions = .ok (q, bounds') →
      q.headers.protocols = []
  | p, bounds, [], q, bounds', noProtocols, h => by
      cases h
      exact noProtocols
  | p, bounds, definition :: rest, q, bounds', noProtocols, h => by
      obtain ⟨⟨e, mine⟩, checked, later⟩ := ok_of_bind h
      obtain ⟨hdr, body, ok, fresh, same, _⟩ := (checkDefinition_fn checked).2
      subst same
      exact admitFrom_functions (p.add (.fn hdr body ok fresh)) (mine ++ bounds) rest q bounds'
        noProtocols later

/-- An admitted program is accepted by the check of facts, with its annotation. -/
theorem admit_accepted {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (h : admit named assoc = .ok a) : Defs.Accepted a.program.defs a.annotation.bounds := by
  obtain ⟨q, bounds, resolved, admitted, _, rfl⟩ := admit_ok h
  exact admitFrom_accepted .empty [] named.definitions q bounds rfl admitted

/-! ## The statements -/

/-- Execution and state: an admitted program is the elaboration of what was given, and its
association is the resolution in it of the association given. -/
theorem admitsWhatWasGiven : ∀ named assoc (a : Admitted V), admit named assoc = .ok a →
    elaborateFunctions named = .ok a.program ∧ resolve a.program assoc = .ok a.association := by
  intro named assoc a h
  obtain ⟨q, bounds, resolved, admitted, found, rfl⟩ := admit_ok h
  exact ⟨admitFrom_elaborates .empty [] named.definitions q bounds admitted, found⟩

/-- A view: what `admit` accepts as a program, `check` accepts one definition at a time, and
the headers that it gives, which are what an application sees of each definition, are the
program's. -/
theorem checkAgrees : ∀ named assoc (a : Admitted V), admit named assoc = .ok a →
    checkAll check ⟨[], []⟩ named.definitions = .ok a.program.headers := by
  intro named assoc a h
  obtain ⟨q, bounds, resolved, admitted, _, rfl⟩ := admit_ok h
  exact admitFrom_checkAll .empty [] named.definitions q bounds admitted

/-- Validity: a function of an admitted program never stops `undefined`, on any valid
inputs. -/
theorem functionsSafe : ∀ named assoc (a : Admitted V), admit named assoc = .ok a →
    ∀ (M : Model V) (hdr : FnHeader V) (f : Var a.program.headers.fns hdr)
      (ins : HList M.Val hdr.ins), ins.All M.Valid →
      (fnMeaning M a.program f ins).Stops (· ≠ .undefined) := by
  intro named assoc a h M
  exact (typed_functions_sound a.program (admit_accepted h) M).1

/-- Validity: a function returns valid values. -/
theorem functionsKeepValidity : ∀ named assoc (a : Admitted V), admit named assoc = .ok a →
    ∀ (M : Model V) (hdr : FnHeader V) (f : Var a.program.headers.fns hdr)
      (ins : HList M.Val hdr.ins) (outs : HList M.Val hdr.outs), ins.All M.Valid →
      fnMeaning M a.program f ins = .done outs → outs.All M.Valid := by
  intro named assoc a h M
  exact (typed_functions_sound a.program (admit_accepted h) M).2.1

/-- A view: a function that its header says cannot stop does not stop. -/
theorem headersSayWhoStops : ∀ named assoc (a : Admitted V), admit named assoc = .ok a →
    ∀ (M : Model V) (hdr : FnHeader V) (f : Var a.program.headers.fns hdr)
      (ins : HList M.Val hdr.ins), ins.All M.Valid → hdr.canStop = false →
      (fnMeaning M a.program f ins).Stops fun _ => False := by
  intro named assoc a h M hdr f ins valid quiet
  exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ both => both.1 both.2)
    (Process.every_and _ _ (functionsSafe named assoc a h M hdr f ins valid)
      (Defs.fnTable_stops_undefined M a.program.defs hdr f ins quiet))

/-- Validity: what the annotation of an admitted program knows holds, and no loop runs more
often than its bound. -/
theorem annotationHolds : ∀ named assoc (a : Admitted V), admit named assoc = .ok a →
    ∀ M : Model V, Respects M a.annotation a.program := by
  intro named assoc a h M
  obtain ⟨q, bounds, resolved, admitted, _, rfl⟩ := admit_ok h
  exact Respects.of_functions q
    (admitFrom_functions .empty [] named.definitions q bounds rfl admitted)
    (typed_functions_sound q (admitFrom_accepted .empty [] named.definitions q bounds rfl admitted)
      M).2.2

end

end Zkc.Core

#print axioms Zkc.Core.admitsWhatWasGiven
#print axioms Zkc.Core.checkAgrees
#print axioms Zkc.Core.functionsSafe
#print axioms Zkc.Core.functionsKeepValidity
#print axioms Zkc.Core.headersSayWhoStops
#print axioms Zkc.Core.annotationHolds
