module

public import Zkc.Core.Admission.Programs
public import Zkc.Core.Program.Library
public import Zkc.Core.Meaning.Stops
public import Zkc.Core.Statements

@[expose] public section

/-!
The statements of `Statements.lean` about functions, proved for every record of functions whose
`admit`, `check` and `elaborate` are `admit`, `check` and `elaborateFunctions`: each theorem has
the statement as its type, except the round trip from a typed program, which holds of the typed
programs without protocols (`roundTrip`), since `elaborateFunctions` refuses a protocol.

A program that elaboration gives erases to what was elaborated (`eraseOfElaborated`), and the
erased form of a typed program of functions elaborates as the program (`roundTrip`), by the
round trip of `Admission/Elaboration.lean`.

Admission checks one definition at a time, each against the headers before it: so what it
returns is the elaboration of what was given (`admitsWhatWasGiven`), and the check of each
definition in order gives its headers (`checkAgrees`). Every definition that it accepts is a
function whose body the check of facts accepts, so the program is `Defs.Accepted` with its
annotation, and the theorem of the check of facts for a program gives `functionsSafe`,
`functionsKeepValidity` and `annotationHolds`. A function whose header says that it cannot stop
stops only `undefined` (`Defs.fnTable_stops_undefined`), and never that, so it does not stop
(`headersSayWhoStops`). Two accepted functions of which the second follows the skeleton of the
first mean the same (`functionsSame`): it is the theorem `functions_follow_same` of
`Transform/Local.lean`. A transformation that the step accepts relates functions with the same
meaning (`transformSound`, the theorem `transform_sound` of `Transform/StepSound.lean`), and
every function of a program whose functions follow those of another means what the function of
the other with its header means (`replacedFunctionsSame`, the theorem
`Defs.functionsFollow_sound` of `Admission/Programs.lean`).
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-! ## What a step gives -/

/-- A definition that the check accepts is elaborated, and is a function whose body the check of
facts accepts with the bounds given. -/
theorem checkDefinition_fn {hs : Headers V} {definition : Definition V} {e : Elaborated V hs}
    {bounds : List (Place × Nat)} (h : checkDefinition hs definition = .ok (e, bounds)) :
    elaborateDefinition hs definition = .ok e ∧ ∃ hdr inputs body ok fresh,
      e = .fn hdr inputs body ok fresh ∧
      checkFacts (localFactRules V hs.fns) hdr.key none inputs body = .ok bounds := by
  obtain ⟨e', elaborated, checked⟩ := ok_of_bind h
  obtain ⟨b, facts, same⟩ := ok_of_map checked
  cases same
  refine ⟨elaborated, ?_⟩
  cases e with
  | fn hdr inputs body ok fresh => exact ⟨hdr, inputs, body, ok, fresh, rfl, facts⟩
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
      obtain ⟨hdr, inputs, body, ok, fresh, same, facts⟩ := (checkDefinition_fn checked).2
      subst same
      exact admitFrom_accepted (p.add (.fn hdr inputs body ok fresh)) (mine ++ bounds) rest q
        bounds'
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
      obtain ⟨hdr, inputs, body, ok, fresh, same, _⟩ := (checkDefinition_fn checked).2
      subst same
      exact admitFrom_functions (p.add (.fn hdr inputs body ok fresh)) (mine ++ bounds) rest q
        bounds'
        noProtocols later

/-- An admitted program is accepted by the check of facts, with its annotation. -/
theorem admit_accepted {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (h : admit named assoc = .ok a) : Defs.Accepted a.program.defs a.annotation.bounds := by
  obtain ⟨q, bounds, resolved, admitted, _, rfl⟩ := admit_ok h
  exact admitFrom_accepted .empty [] named.definitions q bounds rfl admitted

/-! ## The statements

Each theorem has its statement as its type, for any record of functions whose `admit`, `check`
and `elaborate`, those that the statement reads, are the definitions here; `roundTrip` has it for
the typed programs without protocols. -/

/-- Execution and state: elaborating the erased form of a typed program of functions gives the
program. This is `Statements.roundTrip` for the typed programs without protocols, which are those
that `elaborateFunctions` can give. -/
theorem roundTrip (c : Functions V) (elaborates : c.elaborate = elaborateFunctions) :
    ∀ p : Typed V, p.headers.protocols = [] → c.elaborate (erase p) = .ok p := by
  rw [elaborates]
  exact elaborateFunctions_erase

/-- Execution and state: a program that elaboration gives erases to the program by names that
was elaborated. -/
theorem eraseOfElaborated (c : Functions V) (elaborates : c.elaborate = elaborateFunctions) :
    Statements.eraseOfElaborated c := by
  unfold Statements.eraseOfElaborated
  rw [elaborates]
  exact erase_elab

/-- Execution and state: an admitted program is the elaboration of what was given, and its
association is the resolution in it of the association given. -/
theorem admitsWhatWasGiven (c : Functions V) (admits : c.admit = admit)
    (elaborates : c.elaborate = elaborateFunctions) : Statements.admitsWhatWasGiven c := by
  unfold Statements.admitsWhatWasGiven
  rw [admits, elaborates]
  intro named assoc a h
  obtain ⟨q, bounds, resolved, admitted, found, rfl⟩ := admit_ok h
  exact ⟨admitFrom_elaborates .empty [] named.definitions q bounds admitted, found⟩

/-- A view: what `admit` accepts as a program, `check` accepts one definition at a time, and
the headers that it gives, which are what an application sees of each definition, are the
program's. -/
theorem checkAgrees (c : Functions V) (admits : c.admit = admit) (checks : c.check = check) :
    Statements.checkAgrees c := by
  unfold Statements.checkAgrees
  rw [admits, checks]
  intro named assoc a h
  obtain ⟨q, bounds, resolved, admitted, _, rfl⟩ := admit_ok h
  exact admitFrom_checkAll .empty [] named.definitions q bounds admitted

/-- Validity: a function of an admitted program never stops `undefined`, on any valid
inputs. -/
theorem functionsSafe (c : Functions V) (admits : c.admit = admit) :
    Statements.functionsSafe c := by
  unfold Statements.functionsSafe
  rw [admits]
  intro named assoc a h M
  exact (typed_functions_sound a.program (admit_accepted h) M).1

/-- Validity: a function returns valid values. -/
theorem functionsKeepValidity (c : Functions V) (admits : c.admit = admit) :
    Statements.functionsKeepValidity c := by
  unfold Statements.functionsKeepValidity
  rw [admits]
  intro named assoc a h M
  exact (typed_functions_sound a.program (admit_accepted h) M).2.1

/-- A view: a function that its header says cannot stop does not stop. -/
theorem headersSayWhoStops (c : Functions V) (admits : c.admit = admit) :
    Statements.headersSayWhoStops c := by
  have safe := functionsSafe c admits
  unfold Statements.headersSayWhoStops
  unfold Statements.functionsSafe at safe
  intro named assoc a h M hdr f ins valid quiet
  exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ both => both.1 both.2)
    (Process.every_and _ _ (safe named assoc a h M hdr f ins valid)
      (Defs.fnTable_stops_undefined M a.program.defs hdr f ins quiet))

/-- Execution and state: two accepted functions of which the second follows the skeleton of the
first mean the same (`functions_follow_same`, `Transform/Local.lean`). -/
theorem functionsSame : Statements.functionsSame (V := V) :=
  fun _ _ _ inputs inputs' body body' definition definition' _ _ distinctBody distinctBody'
      accepted accepted' decided M table distinct safe keeps quiet ins valid permitted =>
    functions_follow_same inputs inputs' body body' definition definition' distinctBody
      distinctBody' accepted accepted' decided M table distinct safe keeps quiet ins valid
      permitted

/-- Execution and state: a transformation of a function that the step accepts relates functions
with the same meaning (`transform_sound`, `Transform/StepSound.lean`). -/
theorem transformSound : Statements.transformSound (V := V) :=
  fun _ _ _ _ _ accepted => transform_sound accepted

/-- Execution and state: every function of a program whose functions follow those of another
program over the same headers, both accepted by the check of facts, means what the function of
the other with its header means (`Defs.functionsFollow_sound`, `Admission/Programs.lean`). -/
theorem replacedFunctionsSame : Statements.replacedFunctionsSame (V := V) :=
  fun _ defs defs' distinct _ _ accepted accepted' follows M hdr f ins valid =>
    Defs.functionsFollow_sound defs defs' distinct accepted accepted' follows M hdr f ins valid

/-- Validity: what the annotation of an admitted program knows holds, and no loop runs more
often than its bound. -/
theorem annotationHolds (c : Functions V) (admits : c.admit = admit) :
    Statements.annotationHolds c := by
  unfold Statements.annotationHolds
  rw [admits]
  intro named assoc a h M
  obtain ⟨q, bounds, resolved, admitted, _, rfl⟩ := admit_ok h
  exact Respects.of_functions q
    (admitFrom_functions .empty [] named.definitions q bounds rfl admitted)
    (typed_functions_sound q (admitFrom_accepted .empty [] named.definitions q bounds rfl admitted)
      M).2.2

end

end Zkc.Core
