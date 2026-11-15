module

public import Zkc.Core.Admission.Admission
public import Zkc.Core.Admission.Elaboration
public import Zkc.Core.Facts.Local
public import Zkc.Core.Facts.Walk

@[expose] public section

/-!
The check of one definition, and admission.

One step serves both: a definition is elaborated against the headers of those before it, and
then its facts are checked. `check` is that step, as a frontend calls it while a program is
written; `admit` is that step for each definition in order, then the resolution of the
association in the program. So what admission accepts is what the check accepts one definition
at a time.

Admission stops at the first definition that is refused and gives every refusal of that
definition: those of its elaboration, or every application of it that is not known to be inside
its operation's domain.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- The check of facts of an elaborated definition: the bounds of its loops. In
`checkDefinition`, elaboration has already refused a protocol (`elaborateDefinition`), so the
arm of a protocol is not reached there; it refuses the protocol too. -/
def Elaborated.facts {hs : Headers V} :
    Elaborated V hs → Except (List (ProgramRefusal V)) (List (Place × Nat))
  | .fn hdr body _ _ => checkFacts (localFactRules V hs.fns) hdr.key none body
  | .protocol hdr .. => .error [refuseWhole hdr.key .protocol (.key hdr.key)]

/-- One definition checked against the headers of those before it: elaborated, with the
bounds that the check of its facts gives. -/
def checkDefinition (hs : Headers V) (definition : Definition V) :
    Except (List (ProgramRefusal V)) (Elaborated V hs × List (Place × Nat)) :=
  (elaborateDefinition hs definition).bind fun elaborated =>
    elaborated.facts.map fun bounds => (elaborated, bounds)

/-- The check of one definition against the headers of those before it: the headers with the
definition's. -/
def check (hs : Headers V) (definition : Definition V) :
    Except (List (ProgramRefusal V)) (Headers V) :=
  (checkDefinition hs definition).map fun checked => checked.1.headers

/-- A check of definitions one at a time, each against the headers that the check of those
before it gave. -/
def checkAll (step : Headers V → Definition V → Except (List (ProgramRefusal V)) (Headers V)) :
    Headers V → List (Definition V) → Except (List (ProgramRefusal V)) (Headers V)
  | hs, [] => .ok hs
  | hs, definition :: rest => (step hs definition).bind fun hs' => checkAll step hs' rest

/-- The check of definitions in order, after a program and the bounds of its loops. -/
def admitFrom (p : Typed V) (bounds : List (Place × Nat)) :
    List (Definition V) → Except (List (ProgramRefusal V)) (Typed V × List (Place × Nat))
  | [] => .ok (p, bounds)
  | definition :: rest =>
      (checkDefinition p.headers definition).bind fun checked =>
        admitFrom (p.add checked.1) (checked.2 ++ bounds) rest

/-- Admission: every definition checked in order, then the association resolved in the
program. -/
def admit (named : NamedProgram V) (association : Association) :
    Except (List (ProgramRefusal V)) (Admitted V) :=
  (admitFrom .empty [] named.definitions).bind fun admitted =>
    (resolve admitted.1 association).map fun resolved => ⟨admitted.1, ⟨admitted.2⟩, resolved⟩

/-- The check of facts accepts every function of a program against the headers before it, and
the bounds are theirs, the latest definition's first. A protocol is passed over: its role
programs are not walked yet. -/
def Defs.Accepted : {hs : Headers V} → Defs V hs → List (Place × Nat) → Prop
  | _, .nil, bounds => bounds = []
  | _, .fn (hs := hs) hdr body _ rest, bounds => ∃ mine others,
      checkFacts (localFactRules V hs.fns) hdr.key none body = .ok mine ∧
        Defs.Accepted rest others ∧ bounds = mine ++ others
  | _, .protocol _ _ _ rest, bounds => Defs.Accepted rest bounds

end

end Zkc.Core
