module

public import Zkc.Core.Admission.Programs
public import Zkc.Core.Program.Library

@[expose] public section

/-!
Admission elaborates and checks definitions in declaration order, then resolves the
association in that program. Each successful definition contributes its certified bounds.
The program theorem uses the assembled bounds for functions and for every role. An error
identifies the first failed definition and includes the failures of all checked participants.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- The check of definitions in order, after a program and the bounds of its loops. -/
def admitFrom (p : Typed V) (bounds : List (Place × Nat)) :
    List (Definition V) → Except (List (AdmissionRefusal V)) (Typed V × List (Place × Nat))
  | [] => .ok (p, bounds)
  | definition :: rest =>
      (checkDefinition p.headers definition).bind fun checked =>
        admitFrom (p.add checked.1) (checked.2 ++ bounds) rest

/-- A successful definition check returns exactly the named elaboration and the bounds
certified by that function or protocol's own check. -/
theorem checkDefinition_ok {hs : Headers V} {definition : Definition V} {e : Elaborated V hs}
    {bounds} (h : checkDefinition hs definition = .ok (e, bounds)) :
    elaborateDefinition hs definition = .ok e ∧ e.Checked bounds := by
  cases parsed : elaborateDefinition hs definition with
  | error errs => simp [checkDefinition, parsed, Except.mapError, Bind.bind, Except.bind] at h
  | ok typed =>
    cases chk : typed.checkBounds with
    | error errs => simp [checkDefinition, parsed, chk, Except.mapError, Bind.bind, Except.bind] at h
    | ok bs =>
      simp [checkDefinition, parsed, chk, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, bs.property⟩

/-- Adding a checked definition puts its own bounds before the preceding declarations' bounds. -/
theorem admitFrom_accepted : ∀ (p : Typed V) (bounds : List (Place × Nat))
    (definitions : List (Definition V)) (q : Typed V) (bounds' : List (Place × Nat)),
    Defs.Accepted p.defs bounds → admitFrom p bounds definitions = .ok (q, bounds') →
      Defs.Accepted q.defs bounds'
  | p, bounds, [], q, bounds', accepted, h => by cases h; exact accepted
  | p, bounds, definition :: rest, q, bounds', accepted, h => by
      obtain ⟨⟨e, mine⟩, checked, later⟩ := ok_of_bind h
      apply admitFrom_accepted (p.add e) (mine ++ bounds) rest q bounds' _ later
      have pass := (checkDefinition_ok checked).2
      cases e <;> exact ⟨mine, bounds, pass, accepted, rfl⟩

/-- Admission: every definition checked in order, then the association resolved in the program.
What it returns carries that its program is assured with its annotation, by the theorem of the
check of facts for a program. -/
def admit (named : NamedProgram V) (association : Association) :
    Except (List (AdmissionRefusal V)) (Admitted V) :=
  match admitted : admitFrom .empty [] named.definitions with
  | .error refusals => .error refusals
  | .ok (program, bounds) =>
      ((resolve program association).mapError (List.map AdmissionRefusal.association)).map fun resolved =>
        let accepted :=
          admitFrom_accepted .empty [] named.definitions program bounds rfl admitted
        ⟨program, ⟨bounds⟩, resolved, typed_program_sound program accepted⟩

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
    refine ⟨admitted, ?_⟩
    cases resolvedAt : resolve program assoc with
    | ok _ => simpa [resolvedAt, Except.mapError] using found
    | error _ => simp [resolvedAt, Except.mapError] at found

end

end Zkc.Core
