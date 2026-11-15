module

public import Zkc.Core.Program.PrintProgram

@[expose] public section

/-!
The elaboration of a program of functions by names, and its round trip.

One definition is elaborated against the headers of those before it, never against their
bodies (`elaborateDefinition`): a function's body against the headers before it, with a key
that none of them has; a protocol is refused, since the rules of the protocol dialect are not
built. A program is the same step for each definition in order, each added to the program
before it.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- The elaboration of one definition against the headers of those before it. -/
def elaborateDefinition (hs : Headers V) :
    Definition V → Except (List (ProgramRefusal V)) (Elaborated V hs)
  | .fn key ins outs canStop kernel body =>
      if repeated : key ∈ hs.keys then .error [refuseWhole key .key (.key key)]
      else
        match elabFn hs.fns ⟨key, ins, outs, canStop, kernel⟩ body with
        | .error refusal => .error [refusal]
        | .ok ⟨b, ok⟩ => .ok (.fn ⟨key, ins, outs, canStop, kernel⟩ b ok repeated)
  | .protocol key .. => .error [refuseWhole key .protocol (.key key)]

/-- The elaboration of definitions in order, after a program. -/
def elaborateFrom (p : Typed V) : List (Definition V) → Except (List (ProgramRefusal V)) (Typed V)
  | [] => .ok p
  | definition :: rest =>
      (elaborateDefinition p.headers definition).bind fun elaborated =>
        elaborateFrom (p.add elaborated) rest

/-- The typed program of a program of functions by names. -/
def elaborateFunctions (named : NamedProgram V) : Except (List (ProgramRefusal V)) (Typed V) :=
  elaborateFrom .empty named.definitions

/-! ## The round trip of a program -/

theorem elaborateFrom_append (p : Typed V) : ∀ (first second : List (Definition V)),
    elaborateFrom p (first ++ second) =
      (elaborateFrom p first).bind fun q => elaborateFrom q second
  | [], _ => rfl
  | definition :: rest, second => by
      simp only [List.cons_append, elaborateFrom]
      cases elaborateDefinition p.headers definition with
      | error _ => rfl
      | ok elaborated => exact elaborateFrom_append (p.add elaborated) rest second

theorem elaborateFrom_print : ∀ {hs : Headers V} (defs : Defs V hs) (distinct : hs.keys.Nodup),
    hs.protocols = [] → elaborateFrom .empty defs.print = .ok ⟨hs, defs, distinct⟩
  | _, .nil, _, _ => rfl
  | _, .fn (hs := hs) ⟨key, ins, outs, canStop, kernel⟩ body ok rest, distinct, functions => by
      have absent : key ∉ hs.keys := (List.nodup_cons.mp distinct).1
      have others : hs.keys.Nodup := (List.nodup_cons.mp distinct).2
      have fns : (hs.fns.map (·.key)).Nodup := (List.nodup_append.mp others).1
      rw [Defs.print, elaborateFrom_append, elaborateFrom_print rest others functions]
      simp only [Except.bind, printFn, elaborateFrom, elaborateDefinition, absent, ↓reduceDIte,
        elabFn_printFn fns body ok]
      rfl
  | _, .protocol .., _, functions => nomatch functions

/-- The round trip of a program: the printed form of every typed program of functions
elaborates as the program. -/
theorem elaborateFunctions_print (p : Typed V) (functions : p.headers.protocols = []) :
    elaborateFunctions (print p) = .ok p :=
  elaborateFrom_print p.defs p.distinct functions

/-- Elaboration after a program of functions gives a program of functions. -/
theorem elaborateFrom_functions : ∀ (p : Typed V) (definitions : List (Definition V)) (q : Typed V),
    p.headers.protocols = [] → elaborateFrom p definitions = .ok q → q.headers.protocols = []
  | _, [], _, functions, elaborated => by
      cases elaborated
      exact functions
  | p, .fn key ins outs canStop kernel body :: rest, q, functions, elaborated => by
      simp only [elaborateFrom, elaborateDefinition] at elaborated
      split at elaborated
      · cases elaborated
      · split at elaborated
        · cases elaborated
        · simp only [Except.bind] at elaborated
          apply elaborateFrom_functions _ rest q _ elaborated
          exact functions
  | _, .protocol .. :: _, _, _, elaborated => by cases elaborated

/-- The round trip of what elaboration gives: the printed form of an elaborated program
elaborates as the program. -/
theorem elaborateFunctions_roundTrip (named : NamedProgram V) (p : Typed V)
    (elaborated : elaborateFunctions named = .ok p) : elaborateFunctions (print p) = .ok p :=
  elaborateFunctions_print p (elaborateFrom_functions .empty _ p rfl elaborated)

end

end Zkc.Core
