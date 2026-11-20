module

public import Zkc.Core.Admission.Admit
public import Zkc.Core.Program.Library
public import Zkc.Core.Meaning.Stops
public import Zkc.Core.Statements

@[expose] public section

/-!
The named elaborator satisfies both round-trip statements for every typed program.
Admission and transformation establish the function judgments from the returned
evidence. The table theorem supplies the safety of every open role on permitted replies.

Admission checks one definition at a time, each against the headers before it: so what it
returns is the elaboration of what was given (`admitsWhatWasGiven`), and the check of each
definition in order gives its headers (`checkAgrees`). Every admitted program is assured with
its annotation: every function satisfies its summary, so it never stops `undefined` on valid inputs
that satisfy its requirements (`functionsSafe`), keeps validity on every valid input
(`functionsKeepValidity`), and the program respects its annotation (`annotationHolds`). A
function whose header says that it cannot stop stops only `undefined`
(`Defs.fnTable_stops_undefined`), and never that on such inputs, so it does not stop there
(`headersSayWhoStops`). A function that follows a safe function is assured and means the same
(`functionsSame`): it is the theorem `TypedFn.follows_assured` of `Transform/StepSound.lean`. A
step of transformation from an assured function relates functions with the same meaning
(`transformSound`, the theorem `AssuredFn.step_same` of `Transform/Assured.lean`), and, when no
summary has a requirement, every function of a program whose functions follow those of a program
that the check of facts accepts means what the function of the other with its header means, and
is safe and keeps validity (`replacedFunctionsSame`, the theorem `Defs.functionsFollow_sound` of
`Admission/Programs.lean`).
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-! ## What the checks in order give -/

/-- The headers of a program with a definition are the definition's. -/
theorem Typed.add_headers (p : Typed V) (e : Elaborated V p.headers) :
    (p.add e).headers = e.headers := by
  cases e <;> rfl

/-- The checks in order elaborate the definitions in order. -/
theorem admitFrom_elaborates : ∀ (p : Typed V) (bounds : List (Place × Nat))
    (definitions : List (Definition V)) (q : Typed V) (bounds' : List (Place × Nat)),
    admitFrom p bounds definitions = .ok (q, bounds') → elaborateFrom p definitions = .ok q
  | p, bounds, [], q, bounds', h => by
      cases h
      rfl
  | p, bounds, definition :: rest, q, bounds', h => by
      obtain ⟨⟨e, mine⟩, checked, later⟩ := ok_of_bind h
      have elaborated := (checkDefinition_ok checked).1
      simp only [elaborateFrom, elaborated]
      exact admitFrom_elaborates (p.add e) (mine ++ bounds) rest q bounds' later

/-- Equality with the complete erasure of a proof's typed subject identifies the actual
admitted program, including its lexical bodies, operation keys, headers and annotations. -/
theorem admitted_eq_of_readback {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    {expected : Typed V} (accepted : admit named assoc = .ok a) (same : named = erase expected) :
    a.program = expected := by
  have found : elaborateProgram named = .ok a.program :=
    admitFrom_elaborates _ _ _ _ _ (admit_ok accepted).1
  rw [same, elaborateProgram_erase] at found
  exact (Except.ok.inj found).symm

/-- The program of an admission is the program that its definitions elaborate to, one after
another. A module that elaborates each definition of a program by names names the typed
program of every admission of it. -/
theorem admitted_eq_of_elaborated {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    {expected : Typed V} (accepted : admit named assoc = .ok a)
    (same : ElaboratedFrom .empty named.definitions expected) : a.program = expected := by
  have found : elaborateProgram named = .ok a.program :=
    admitFrom_elaborates _ _ _ _ _ (admit_ok accepted).1
  have also : elaborateProgram named = .ok expected := same.elaborates
  rw [found] at also
  exact Except.ok.inj also

/-- Decide program identity using the input that admission actually checked. A caller can
transport a meaning theorem in the positive case. The source association is a separate input. -/
def identifyAdmitted {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (accepted : admit named assoc = .ok a) (expected : Typed V) : Decidable (a.program = expected) :=
  decidable_of_iff (named = erase expected) ⟨admitted_eq_of_readback accepted, fun same => by
    have found := admitFrom_elaborates _ _ _ _ _ (admit_ok accepted).1
    exact (erase_elab named a.program found).symm.trans (congrArg erase same)⟩

/-- Incremental checking and the definition phase of admission agree on the headers or the
entire list of refusals, starting at any already typed prefix. Association resolution follows
this phase. -/
theorem checkAll_eq_admitFrom (p : Typed V) (bounds : List (Place × Nat))
    (definitions : List (Definition V)) :
    checkAll check p.headers definitions =
      (admitFrom p bounds definitions).map (fun result => result.1.headers) := by
  induction definitions generalizing p bounds with
  | nil => rfl
  | cons definition rest ih =>
      cases h : checkDefinition p.headers definition with
      | error refusals => simp only [checkAll, check, admitFrom, h, Except.map, Except.bind]
      | ok checked =>
          obtain ⟨e, mine⟩ := checked
          simpa only [checkAll, check, admitFrom, h, Except.map, Except.bind, Typed.add_headers]
            using ih (p.add e) (mine ++ bounds)

/-- The checks in order give the headers of the program, one definition at a time. -/
theorem admitFrom_checkAll (p : Typed V) (bounds : List (Place × Nat))
    (definitions : List (Definition V)) (q : Typed V) (bounds' : List (Place × Nat))
    (h : admitFrom p bounds definitions = .ok (q, bounds')) :
    checkAll check p.headers definitions = .ok q.headers := by
  rw [checkAll_eq_admitFrom p bounds, h]
  rfl

/-! ## The statements

Each theorem has its statement as its type: for any record of functions whose `admit`, `check`
and `elaborate`, those that the statement reads, are the definitions here, and for every admitted
program. -/

/-- The named elaborator recovers every typed program, including protocol applications. -/
theorem roundTrip (c : Functions V) (elaborates : c.elaborate = elaborateProgram) :
    Statements.roundTrip c := by
  unfold Statements.roundTrip
  rw [elaborates]
  exact elaborateProgram_erase

/-- Execution and state: a program that elaboration gives erases to the program by names that
was elaborated. -/
theorem eraseOfElaborated (c : Functions V) (elaborates : c.elaborate = elaborateProgram) :
    Statements.eraseOfElaborated c := by
  unfold Statements.eraseOfElaborated
  rw [elaborates]
  exact erase_elab

/-- Execution and state: an admitted program is the elaboration of what was given, and its
association is the resolution in it of the association given. -/
theorem admitsWhatWasGiven (c : Functions V) (admits : c.admit = admit)
    (elaborates : c.elaborate = elaborateProgram) : Statements.admitsWhatWasGiven c := by
  unfold Statements.admitsWhatWasGiven
  rw [admits, elaborates]
  intro named assoc a h
  obtain ⟨admitted, found⟩ := admit_ok h
  exact ⟨admitFrom_elaborates .empty [] named.definitions _ _ admitted, found⟩

/-- A view: what `admit` accepts as a program, `check` accepts one definition at a time, and
the headers that it gives, which are what an application sees of each definition, are the
program's. -/
theorem checkAgrees (c : Functions V) (admits : c.admit = admit) (checks : c.check = check) :
    Statements.checkAgrees c := by
  unfold Statements.checkAgrees
  rw [admits, checks]
  intro named assoc a h
  exact admitFrom_checkAll .empty [] named.definitions _ _ (admit_ok h).1

/-- The actual projected role process runs safely at every invocation path, against
permitted peer replies, under any accepted function contracts. -/
theorem rolesSafe (c : Functions V) (implements : c.admit = admit) : Statements.rolesSafe c := by
  intro named assoc a accepted M hdr callee r path args valid
  rw [implements] at accepted
  have checked := admitFrom_accepted .empty [] named.definitions a.program a.annotation.bounds rfl (admit_ok accepted).1
  have roles := (BodyAnalysis.RoleContracts.checkedTables M a.program.defs
    (List.nodup_append.mp a.program.distinct).1 (acceptedBodies _ checked)).2
  exact Process.every_mono _ _ (fun _ _ => trivial) (fun _ h => h) (roles hdr callee r path args valid)

/-- Validity: a function of an admitted program never stops `undefined`, on any valid inputs that
satisfy the requirements of its header's summary: what every admitted program carries, that its
functions satisfy their summaries. -/
theorem functionsSafe : Statements.functionsSafe (V := V) :=
  fun a M _ f ins valid required =>
    Process.every_mono _ _ (fun _ _ => trivial) (fun _ stop => stop)
      ((a.assured M).1 _ f ins
        (((localSem M _ (Defs.fnTable M a.program.defs)).dyns_valid_iff ins).mpr valid) required)

/-- Validity: a function of an admitted program returns valid values: what every admitted
program carries. -/
theorem functionsKeepValidity : Statements.functionsKeepValidity (V := V) :=
  fun a M _ f ins outs valid ran => (a.assured M).2.1 _ f ins outs valid ran

/-- A view: a function of an admitted program that its header says cannot stop does not
stop, on valid inputs that satisfy the requirements of its header's summary. -/
theorem headersSayWhoStops : Statements.headersSayWhoStops (V := V) :=
  fun a M hdr f ins valid required quiet =>
    Process.every_mono _ _ (fun _ _ => trivial) (fun _ both => both.1 both.2)
      (Process.every_and _ _ (functionsSafe a M hdr f ins valid required)
        (Defs.fnTable_stops_undefined M a.program.defs hdr f ins quiet))

/-- Execution and state: a function that follows a safe function is assured and means the
same (`TypedFn.follows_assured`, `Transform/StepSound.lean`). -/
theorem functionsSame : Statements.functionsSame (V := V) :=
  fun _ _ _ _ _ safe followed => TypedFn.follows_assured safe followed

/-- Execution and state: a step of transformation from an assured function relates functions
with the same meaning (`AssuredFn.step_same`, `Transform/Assured.lean`). -/
theorem transformSound : Statements.transformSound (V := V) :=
  fun _ _ _ _ _ accepted => AssuredFn.step_same accepted

/-- Execution and state, and validity: every function of a program whose functions follow those
of a program accepted by the check of facts, over the same headers of which no summary has a
requirement, means what the function of the other with its header means, and the functions of the
second are safe and keep validity (`Defs.functionsFollow_sound`, `Admission/Programs.lean`). -/
theorem replacedFunctionsSame : Statements.replacedFunctionsSame (V := V) :=
  fun _ defs defs' distinct unconditional _ accepted follows M =>
    Defs.functionsFollow_sound defs defs' distinct unconditional accepted follows M

/-- Validity: no loop of an admitted program runs more often than the bound that its annotation
gives it: what every admitted program carries. -/
theorem annotationHolds : Statements.annotationHolds (V := V) :=
  fun a M => (a.assured M).2.2

end

end Zkc.Core
