module

public import Zkc.Core.Program.EraseProgram

@[expose] public section

/-!
Elaboration resolves each function and protocol against the preceding headers. Local
operations use the vocabulary, and protocol applications use the callee's ordered role
map to check located ports. The body supplies the protocol header's shape.

The two round trips cover arbitrary mixed programs. Elaborating an erasure returns the
original typed program (`elaborateProgram_erase`). Erasing a successful elaboration
returns all named definitions (`erase_elab`).
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- The elaboration of one definition against the headers of those before it. -/
def elaborateDefinition (hs : Headers V) :
    Definition V → Except (List (DefinitionRefusal V)) (Elaborated V hs)
  | .fn key ins outs canStop kernel summary body notes =>
      if repeated : key ∈ hs.keys then .error [.fn (refuseWhole key .key (.key key))]
      else
        match elabFn hs.fns ⟨key, ins, outs, canStop, kernel, summary⟩ body with
        | .error refusal => .error [.fn refusal]
        | .ok ⟨inputs, b, ok⟩ =>
            .ok (.fn ⟨key, ins, outs, canStop, kernel, summary⟩ inputs b ok repeated notes)
  | .protocol key roles ins outs body =>
      if repeated : key ∈ hs.keys then .error [.protocol (refuseWhole key .key (.key key))]
      else
        match elabProtocol hs key roles ins outs body with
        | .error refusal => .error [.protocol refusal]
        | .ok typed =>
            .ok (.protocol ⟨key, roles, ins, outs, shapeOf typed.body⟩ typed.inputs typed.body
              typed.conditions repeated)

/-- The elaboration of definitions in order, after a program. -/
def elaborateFrom (p : Typed V) : List (Definition V) → Except (List (DefinitionRefusal V)) (Typed V)
  | [] => .ok p
  | definition :: rest =>
      (elaborateDefinition p.headers definition).bind fun elaborated =>
        elaborateFrom (p.add elaborated) rest

/-- Elaborate the complete list of named definitions. -/
def elaborateProgram (named : NamedProgram V) : Except (List (DefinitionRefusal V)) (Typed V) :=
  elaborateFrom .empty named.definitions

/-- Historical spelling of the named elaborator. -/
abbrev elaborateFunctions (named : NamedProgram V) := elaborateProgram named

/-! ## Elaboration, one definition at a time -/

/-- Definitions that elaborate one after another, from a program to a program: each against the
headers of the program before it. This is what a module states when it elaborates the
definitions of a program by names one by one. -/
inductive ElaboratedFrom : Typed V → List (Definition V) → Typed V → Prop where
  | nil (p : Typed V) : ElaboratedFrom p [] p
  | cons {p : Typed V} {definition : Definition V} {elaborated : Elaborated V p.headers}
      {rest : List (Definition V)} {q : Typed V}
      (first : elaborateDefinition p.headers definition = .ok elaborated)
      (others : ElaboratedFrom (p.add elaborated) rest q) :
      ElaboratedFrom p (definition :: rest) q

/-- Definitions that elaborate one after another are what the elaboration in order gives. -/
theorem ElaboratedFrom.elaborates {p q : Typed V} {definitions : List (Definition V)}
    (h : ElaboratedFrom p definitions q) : elaborateFrom p definitions = .ok q := by
  induction h with
  | nil p => rfl
  | cons first _ ih => simp only [elaborateFrom, first, Except.bind, ih]

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

/-- The erased definitions of a typed program, elaborated from no program, give
the program. -/
theorem elaborateFrom_erase : ∀ {hs : Headers V} (defs : Defs V hs) (distinct : hs.keys.Nodup),
    elaborateFrom .empty defs.erase = .ok ⟨hs, defs, distinct⟩
  | _, .nil, _ => rfl
  | _, .fn (hs := hs) ⟨key, ins, outs, canStop, kernel, summary⟩ inputs body ok rest notes, distinct => by
      have absent : key ∉ hs.keys := (List.nodup_cons.mp distinct).1
      have others : hs.keys.Nodup := (List.nodup_cons.mp distinct).2
      have fns : (hs.fns.map (·.key)).Nodup := (List.nodup_append.mp others).1
      rw [Defs.erase, elaborateFrom_append, elaborateFrom_erase rest others]
      simp only [Except.bind, elaborateFrom, elaborateDefinition, absent, ↓reduceDIte,
        elabFn_erase fns inputs body ok]
      rfl
  | _, .protocol (hs := hs) hdr inputs body ok rest, distinct => by
      have separated := List.nodup_append.mp distinct
      have remaining := List.nodup_cons.mp separated.2.1
      have others : hs.keys.Nodup := List.nodup_append.mpr
        ⟨separated.1, remaining.2, fun a ha b hb => separated.2.2 a ha b (.tail _ hb)⟩
      have absent : hdr.key ∉ hs.keys := by
        intro found
        cases List.mem_append.mp found with
        | inl inFns => exact separated.2.2 _ inFns _ (.head _) rfl
        | inr earlier => exact remaining.1 earlier
      obtain ⟨⟨bound, term, conditions⟩, read, names, terms⟩ :=
        elabProtocol_erase others inputs body ok
      cases names
      cases terms
      rw [Defs.erase, elaborateFrom_append, elaborateFrom_erase rest others]
      simp only [Except.bind, elaborateFrom, elaborateDefinition, absent, ↓reduceDIte, read]
      obtain ⟨key, roles, ins, outs, shape⟩ := hdr
      change Names ins at bound
      change Term (protocolDialect V hs) (Ctx.empty.extend bound) outs at term
      have shaped : shape = shapeOf term := ok.shaped
      subst shape
      rfl

/-- The round trip of a program, erased then elaborated: the erased form of every typed program
elaborates as the program. -/
theorem elaborateProgram_erase (p : Typed V) : elaborateProgram (erase p) = .ok p :=
  elaborateFrom_erase p.defs p.distinct

theorem elaborateFunctions_erase (p : Typed V) (_ : p.headers.protocols = []) :
    elaborateFunctions (erase p) = .ok p := elaborateProgram_erase p

/-- What elaboration after a program gives erases to the program's definitions, then the
definitions elaborated. -/
theorem erase_elaborateFrom : ∀ (p : Typed V) (definitions : List (Definition V)) (q : Typed V),
    elaborateFrom p definitions = .ok q → q.defs.erase = p.defs.erase ++ definitions
  | _, [], _, elaborated => by
      cases elaborated
      exact (List.append_nil _).symm
  | p, .fn key ins outs canStop kernel summary body notes :: rest, q, elaborated => by
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
  | p, .protocol key roles ins outs region :: rest, q, elaborated => by
      simp only [elaborateFrom, elaborateDefinition] at elaborated
      split at elaborated
      · cases elaborated
      · split at elaborated
        · cases elaborated
        · rename_i typed found
          have erased := eraseProtocol_elab region found
          rw [erase_elaborateFrom _ rest q elaborated]
          simp only [Typed.add, Defs.erase, erased, List.append_assoc, List.cons_append,
            List.nil_append]

/-- The round trip of a program, elaborated then erased: a program that elaboration gives
erases to the program by names that was elaborated. -/
theorem erase_elab (named : NamedProgram V) (p : Typed V)
    (elaborated : elaborateFunctions named = .ok p) : erase p = named := by
  have erased := erase_elaborateFrom .empty named.definitions p elaborated
  obtain ⟨definitions⟩ := named
  simp only [erase, erased, Typed.empty, Defs.erase, List.nil_append]

end

end Zkc.Core
