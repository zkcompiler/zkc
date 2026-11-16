module

public import Zkc.Core.Program.EraseProgram

@[expose] public section

/-!
The elaboration of a program of functions by names, and its round trip in both directions.

One definition is elaborated against the headers of those before it, never against their
bodies (`elaborateDefinition`): a function's body against the headers before it, with a key
that none of them has; a protocol is refused, since the rules of the protocol dialect are not
built. A program is the same step for each definition in order, each added to the program
before it.

The erased form of every typed program of functions elaborates as the program
(`elaborateFunctions_erase`), and a program that elaboration gives erases to the program by
names that was elaborated (`erase_elab`).
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
        | .ok ⟨inputs, b, ok⟩ => .ok (.fn ⟨key, ins, outs, canStop, kernel⟩ inputs b ok repeated)
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

/-- The erased definitions of a typed program of functions, elaborated from no program, give
the program. -/
theorem elaborateFrom_erase : ∀ {hs : Headers V} (defs : Defs V hs) (distinct : hs.keys.Nodup),
    hs.protocols = [] → elaborateFrom .empty defs.erase = .ok ⟨hs, defs, distinct⟩
  | _, .nil, _, _ => rfl
  | _, .fn (hs := hs) ⟨key, ins, outs, canStop, kernel⟩ inputs body ok rest, distinct,
      functions => by
      have absent : key ∉ hs.keys := (List.nodup_cons.mp distinct).1
      have others : hs.keys.Nodup := (List.nodup_cons.mp distinct).2
      have fns : (hs.fns.map (·.key)).Nodup := (List.nodup_append.mp others).1
      rw [Defs.erase, elaborateFrom_append, elaborateFrom_erase rest others functions]
      simp only [Except.bind, elaborateFrom, elaborateDefinition, absent, ↓reduceDIte,
        elabFn_erase fns inputs body ok]
      rfl
  | _, .protocol .., _, functions => nomatch functions

/-- The round trip of a program, erased then elaborated: the erased form of every typed program
of functions elaborates as the program. -/
theorem elaborateFunctions_erase (p : Typed V) (functions : p.headers.protocols = []) :
    elaborateFunctions (erase p) = .ok p :=
  elaborateFrom_erase p.defs p.distinct functions

/-- What elaboration after a program gives erases to the program's definitions, then the
definitions elaborated. -/
theorem erase_elaborateFrom : ∀ (p : Typed V) (definitions : List (Definition V)) (q : Typed V),
    elaborateFrom p definitions = .ok q → q.defs.erase = p.defs.erase ++ definitions
  | _, [], _, elaborated => by
      cases elaborated
      exact (List.append_nil _).symm
  | p, .fn key ins outs canStop kernel body :: rest, q, elaborated => by
      simp only [elaborateFrom, elaborateDefinition] at elaborated
      split at elaborated
      · cases elaborated
      · rename_i fresh
        split at elaborated
        · cases elaborated
        · rename_i inputs b ok found
          have erased := eraseFn_elab body found
          rw [erase_elaborateFrom _ rest q elaborated]
          simp only [Typed.add, Defs.erase, erased, List.append_assoc, List.cons_append,
            List.nil_append]
  | _, .protocol .. :: _, _, elaborated => by cases elaborated

/-- The round trip of a program, elaborated then erased: a program that elaboration gives
erases to the program by names that was elaborated. -/
theorem erase_elab (named : NamedProgram V) (p : Typed V)
    (elaborated : elaborateFunctions named = .ok p) : erase p = named := by
  have erased := erase_elaborateFrom .empty named.definitions p elaborated
  obtain ⟨definitions⟩ := named
  simp only [erase, erased, Typed.empty, Defs.erase, List.nil_append]

end

end Zkc.Core
