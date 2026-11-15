module

public import Zkc.Core.Program.ElaborateLocal
public import Zkc.Core.Admission.Refusal

@[expose] public section

/-!
The elaboration of a program of functions by names, and its round trip.

The definitions are elaborated in order, each against the program before it: a function's body
against the headers before it, with a key that none of them has. `elaborateDefinition` is the
step for one definition; a protocol is refused, since the rules of the protocol dialect are not
built.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- A program without definitions. -/
def Typed.empty : Typed V := ⟨⟨[], []⟩, .nil, List.nodup_nil⟩

/-- The elaboration of one definition after the program before it: the program with it. -/
def elaborateDefinition (p : Typed V) : Definition V → Except (List (Refusal V)) (Typed V)
  | .fn key ins outs canStop kernel body =>
      if repeated : key ∈ p.headers.keys then .error [definitionRefusal key .key]
      else
        match elabFn p.headers.fns ⟨key, ins, outs, canStop, kernel⟩ body with
        | .error problem => .error [problem.refusal key]
        | .ok ⟨b, ok⟩ =>
            .ok ⟨⟨⟨key, ins, outs, canStop, kernel⟩ :: p.headers.fns, p.headers.protocols⟩,
              .fn _ b ok p.defs, List.nodup_cons.mpr ⟨repeated, p.distinct⟩⟩
  | .protocol key .. => .error [definitionRefusal key .protocol]

/-- The elaboration of definitions in order, after a program. -/
def elaborateFrom (p : Typed V) : List (Definition V) → Except (List (Refusal V)) (Typed V)
  | [] => .ok p
  | definition :: rest => (elaborateDefinition p definition).bind fun p' => elaborateFrom p' rest

/-- The typed program of a program of functions by names. -/
def elaborateFunctions (named : NamedProgram V) : Except (List (Refusal V)) (Typed V) :=
  elaborateFrom .empty named.definitions

/-! ## The round trip of a program -/

/-- Whether a program's definitions are functions whose case analyses without an arm give
nothing. -/
def Defs.armed : {hs : Headers V} → Defs V hs → Bool
  | _, .nil => true
  | _, .fn _ body _ rest => body.armed && rest.armed
  | _, .protocol .. => false

theorem elaborateFrom_append (p : Typed V) : ∀ (first second : List (Definition V)),
    elaborateFrom p (first ++ second) =
      (elaborateFrom p first).bind fun q => elaborateFrom q second
  | [], _ => rfl
  | definition :: rest, second => by
      simp only [List.cons_append, elaborateFrom]
      cases elaborateDefinition p definition with
      | error _ => rfl
      | ok q => exact elaborateFrom_append q rest second

theorem elaborateFrom_print : ∀ {hs : Headers V} (defs : Defs V hs) (distinct : hs.keys.Nodup),
    defs.armed = true → elaborateFrom .empty defs.print = .ok ⟨hs, defs, distinct⟩
  | _, .nil, _, _ => rfl
  | _, .fn (hs := hs) ⟨key, ins, outs, canStop, kernel⟩ body ok rest, distinct, armed => by
      simp only [Defs.armed, Bool.and_eq_true] at armed
      have absent : key ∉ hs.keys := (List.nodup_cons.mp distinct).1
      have others : hs.keys.Nodup := (List.nodup_cons.mp distinct).2
      have functions : (hs.fns.map (·.key)).Nodup := (List.nodup_append.mp others).1
      rw [Defs.print, elaborateFrom_append, elaborateFrom_print rest others armed.2]
      simp only [Except.bind, printFn, elaborateFrom, elaborateDefinition, absent, ↓reduceDIte,
        elabFn_printFn functions body ok armed.1]
  | _, .protocol .., _, armed => by simp [Defs.armed] at armed

/-- The round trip of a program: the printed form of a typed program of functions whose case
analyses without an arm give nothing elaborates as the program. -/
theorem elaborateFunctions_print (p : Typed V) (armed : p.defs.armed = true) :
    elaborateFunctions (print p) = .ok p :=
  elaborateFrom_print p.defs p.distinct armed

/-- Elaborating a definition after a program of functions whose case analyses without an arm
give nothing gives such a program. -/
theorem elaborateDefinition_armed (p : Typed V) : ∀ (definition : Definition V) (q : Typed V),
    p.defs.armed = true → elaborateDefinition p definition = .ok q → q.defs.armed = true
  | .fn _ _ _ _ _ body, _, armed, elaborated => by
      simp only [elaborateDefinition] at elaborated
      split at elaborated
      · cases elaborated
      · split at elaborated
        · cases elaborated
        · cases elaborated
          simp only [Defs.armed, armed, Bool.and_true]
          exact elabFn_armed body ‹elabFn _ _ body = _›
  | .protocol .., _, _, elaborated => by cases elaborated

theorem elaborateFrom_armed : ∀ (p : Typed V) (definitions : List (Definition V)) (q : Typed V),
    p.defs.armed = true → elaborateFrom p definitions = .ok q → q.defs.armed = true
  | _, [], _, armed, elaborated => by
      cases elaborated
      exact armed
  | p, definition :: rest, q, armed, elaborated => by
      simp only [elaborateFrom] at elaborated
      cases step : elaborateDefinition p definition with
      | error _ =>
          rw [step] at elaborated
          cases elaborated
      | ok p' =>
          rw [step] at elaborated
          exact elaborateFrom_armed p' rest q
            (elaborateDefinition_armed p definition p' armed step) elaborated

/-- The round trip of what elaboration gives: elaborating the printed form of an elaborated
program of functions gives the program. -/
theorem elaborateFunctions_roundTrip (named : NamedProgram V) (p : Typed V)
    (elaborated : elaborateFunctions named = .ok p) : elaborateFunctions (print p) = .ok p :=
  elaborateFunctions_print p (elaborateFrom_armed .empty _ p rfl elaborated)

end

end Zkc.Core
