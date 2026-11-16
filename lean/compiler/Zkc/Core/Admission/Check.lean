module

public import Zkc.Core.Admission.Admission
public import Zkc.Core.Admission.Elaboration
public import Zkc.Core.Transform.Assured

@[expose] public section

/-!
The check of one definition, and the acceptance of a typed program by the check of facts.

A definition is checked against the headers of those before it: a function whose key no
definition before it has is admitted (`admitFn`, `Transform/Assured.lean`), elaborated and its
facts checked, the one path by which a function is admitted, here and in transformations alike; a
protocol is refused, since the rules of the protocol dialect are not built. `check` is that step,
as a frontend calls it while a program is written; admission (`admit`, `Admission/Admit.lean`) is
that step for each definition in order, then the resolution of the association in the program.
So what admission accepts is what the check accepts one definition at a time. The check of a
definition gives every refusal of that definition: those of its elaboration, or every
application of it that is not known to be inside its operation's domain.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- One definition checked against the headers of those before it: a function whose key no
definition before it has, admitted (`admitFn`: elaborated, and its facts checked), with the
bounds of its loops. A protocol is refused: the rules of the protocol dialect are not built. -/
def checkDefinition (hs : Headers V) :
    Definition V → Except (List (ProgramRefusal V)) (Elaborated V hs × List (Place × Nat))
  | .fn key ins outs canStop kernel body =>
      if repeated : key ∈ hs.keys then .error [refuseWhole key .key (.key key)]
      else (admitFn hs.fns ⟨key, ins, outs, canStop, kernel⟩ body).map fun admitted =>
        (.fn ⟨key, ins, outs, canStop, kernel⟩ admitted.fn.inputs admitted.fn.body
          admitted.fn.conditions repeated, admitted.bounds)
  | .protocol key .. => .error [refuseWhole key .protocol (.key key)]

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

/-- The check of facts accepts every function of a program against the headers before it, and
the bounds are theirs, the latest definition's first. A protocol is passed over: its role
programs are not walked yet. -/
def Defs.Accepted : {hs : Headers V} → Defs V hs → List (Place × Nat) → Prop
  | _, .nil, bounds => bounds = []
  | _, .fn (hs := hs) hdr inputs body _ rest, bounds => ∃ mine others,
      checkFacts (localFactRules V hs.fns) (localRules hs.fns).skel hdr.key none ⟨[], []⟩ inputs
        body = .ok mine ∧
        Defs.Accepted rest others ∧ bounds = mine ++ others
  | _, .protocol _ _ _ _ rest, bounds => Defs.Accepted rest bounds

end

end Zkc.Core
