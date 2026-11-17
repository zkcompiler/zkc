module

public import Zkc.Core.Admission.Programs
public import Zkc.Core.Program.Library

@[expose] public section

/-!
Admission: every definition checked in order, each against the headers before it
(`checkDefinition`), then the association resolved in the program; what it returns carries that
the program is assured with its annotation (`Admitted.assured`).

Every definition that the check accepts is a function whose facts the check accepts
(`checkDefinition_fn`), so the checks in order give a program that the check of facts accepts
with the bounds that they gather and that has no protocol (`admitFrom_accepted`); the theorem of
the check of facts for a program (`typed_functions_sound`) then gives what admission returns with
it. Admission stops at the first definition that is refused and gives every refusal of that
definition.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- The check of definitions in order, after a program and the bounds of its loops. -/
def admitFrom (p : Typed V) (bounds : List (Place × Nat)) :
    List (Definition V) → Except (List (ProgramRefusal V)) (Typed V × List (Place × Nat))
  | [] => .ok (p, bounds)
  | definition :: rest =>
      (checkDefinition p.headers definition).bind fun checked =>
        admitFrom (p.add checked.1) (checked.2 ++ bounds) rest

/-- A definition that the check accepts is elaborated, and is a function whose body the check of
facts accepts with the bounds given. -/
theorem checkDefinition_fn {hs : Headers V} {definition : Definition V} {e : Elaborated V hs}
    {bounds : List (Place × Nat)} (h : checkDefinition hs definition = .ok (e, bounds)) :
    elaborateDefinition hs definition = .ok e ∧ ∃ hdr inputs body ok fresh,
      e = .fn hdr inputs body ok fresh ∧
      checkFacts (localFactRules V hs.fns) (localRules hs.fns).skel hdr.key none hdr.summary
        inputs body = .ok bounds := by
  cases definition with
  | protocol => cases h
  | fn key ins outs canStop kernel summary body =>
      simp only [checkDefinition] at h
      split at h
      · cases h
      · rename_i fresh
        obtain ⟨admitted, found, same⟩ := ok_of_map h
        cases same
        obtain ⟨typed, checked⟩ := admitFn_ok found
        refine ⟨?_, _, _, _, _, fresh, rfl, checked⟩
        simp only [elaborateDefinition, fresh, ↓reduceDIte, typeFn_ok typed]

/-- The checks in order keep the program accepted by the check of facts, with the bounds that
they gather, and add no protocol. -/
theorem admitFrom_accepted : ∀ (p : Typed V) (bounds : List (Place × Nat))
    (definitions : List (Definition V)) (q : Typed V) (bounds' : List (Place × Nat)),
    Defs.Accepted p.defs bounds → p.headers.protocols = [] →
    admitFrom p bounds definitions = .ok (q, bounds') →
      Defs.Accepted q.defs bounds' ∧ q.headers.protocols = []
  | p, bounds, [], q, bounds', accepted, noProtocols, h => by
      cases h
      exact ⟨accepted, noProtocols⟩
  | p, bounds, definition :: rest, q, bounds', accepted, noProtocols, h => by
      obtain ⟨⟨e, mine⟩, checked, later⟩ := ok_of_bind h
      obtain ⟨hdr, inputs, body, ok, fresh, same, facts⟩ := (checkDefinition_fn checked).2
      subst same
      exact admitFrom_accepted (p.add (.fn hdr inputs body ok fresh)) (mine ++ bounds) rest q
        bounds' ⟨mine, bounds, facts, accepted, rfl⟩ noProtocols later

/-- Admission: every definition checked in order, then the association resolved in the program.
What it returns carries that its program is assured with its annotation, by the theorem of the
check of facts for a program. -/
def admit (named : NamedProgram V) (association : Association) :
    Except (List (ProgramRefusal V)) (Admitted V) :=
  match admitted : admitFrom .empty [] named.definitions with
  | .error refusals => .error refusals
  | .ok (program, bounds) =>
      (resolve program association).map fun resolved =>
        let accepted :=
          admitFrom_accepted .empty [] named.definitions program bounds rfl rfl admitted
        ⟨program, ⟨bounds⟩, resolved, typed_functions_sound program accepted.1 accepted.2⟩

/-- What admission gives: the program that its checks give, with its bounds as the annotation,
and the association resolved in it. -/
theorem admit_ok {named : NamedProgram V} {assoc : Association} {a : Admitted V}
    (h : admit named assoc = .ok a) :
    admitFrom .empty [] named.definitions = .ok (a.program, a.annotation.bounds) ∧
      resolve a.program assoc = .ok a.association := by
  unfold admit at h
  split at h
  · cases h
  · rename_i program bounds admitted
    obtain ⟨resolved, found, same⟩ := ok_of_map h
    cases same
    exact ⟨admitted, found⟩

end

end Zkc.Core
