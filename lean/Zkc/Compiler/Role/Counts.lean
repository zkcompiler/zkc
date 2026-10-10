import Zkc.Compiler.Role.Syntax
import Zkc.Compiler.Role.Projection
import Zkc.Source.Protocol.Counts

/-! Structural count substitution. Substitution never unfolds a loop or a stored
callee; `Nat` is the resolved count carrier used by the execution semantics. -/

set_option autoImplicit false
namespace Zkc.Compiler.Role
open Zkc.Source Zkc.Source.Protocol
variable {Count Other Third Role Binding Schema : Type} {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {scope : List (Signature Role language.Ty)}
variable {self : Role}

def Program.mapCounts (f : Count → Other) {Γ results} :
    Program Count self Binding Schema language locals scope Γ results → Program Other self Binding Schema language locals scope Γ results
  | .ret values => .ret values
  | .stop site reason => .stop site reason
  | .incomplete => .incomplete
  | .localCall site callee args next => .localCall site callee args (next.mapCounts f)
  | .send site schema receiver different value next => .send site schema receiver different value (next.mapCounts f)
  | .receive ty site schema sender different next => .receive ty site schema sender different (next.mapCounts f)
  | .skip different next => .skip different (next.mapCounts f)
  | .invoke site callee args next => .invoke site callee args (next.mapCounts f)
  | .repeat site count initial body next => .repeat site (f count) initial (body.mapCounts f) (next.mapCounts f)
  | .bind body next => .bind (body.mapCounts f) (next.mapCounts f)

theorem Program.mapCounts_id {Γ results} (program : Program Count self Binding Schema language locals scope Γ results) :
    program.mapCounts id = program := by
  induction program <;> simp_all [mapCounts]

theorem Program.mapCounts_comp (f : Count → Other) (g : Other → Third)
    {Γ results} (program : Program Count self Binding Schema language locals scope Γ results) :
    (program.mapCounts f).mapCounts g = program.mapCounts (g ∘ f) := by
  induction program <;> simp_all [mapCounts]

def Definitions.mapCounts (f : Count → Other)
    {scope : List (Signature Role language.Ty)} :
    Definitions Count self Binding Schema language locals scope → Definitions Other self Binding Schema language locals scope
  | .nil => .nil
  | .snoc previous signature body => .snoc (previous.mapCounts f) signature (body.mapCounts f)

theorem Definitions.mapCounts_id (definitions : Definitions Count self Binding Schema language locals scope) :
    definitions.mapCounts id = definitions := by
  induction definitions <;> simp_all [mapCounts, Program.mapCounts_id]

theorem Definitions.mapCounts_comp (f : Count → Other) (g : Other → Third)
    (definitions : Definitions Count self Binding Schema language locals scope) :
    (definitions.mapCounts f).mapCounts g = definitions.mapCounts (g ∘ f) := by
  induction definitions <;> simp_all [mapCounts, Program.mapCounts_comp]

theorem project_mapCounts [DecidableEq Role] (self : Role) (f : Count → Other) {Γ results}
    (program : Protocol.Program Count Role Binding Schema language locals scope Γ results) :
    project self (program.mapCounts f) = (project self program).mapCounts f := by
  induction program with
  | ret values => rfl
  | stop site owner reason =>
    by_cases same : owner = self <;>
      simp [project, Protocol.Program.mapCounts, Program.mapCounts, same]
  | localCall site owner callee args next ih =>
    by_cases same : owner = self
    · subst owner
      simp [project, Protocol.Program.mapCounts, Program.mapCounts, ih]
    · simp [project, Protocol.Program.mapCounts, Program.mapCounts, same, ih]
  | message site schema sender receiver different value next ih =>
    by_cases sending : sender = self
    · subst sender
      simp [project, Protocol.Program.mapCounts, Program.mapCounts, ih]
    · by_cases receiving : receiver = self
      · subst receiver
        simp [project, Protocol.Program.mapCounts, Program.mapCounts, sending, ih]
      · simp [project, Protocol.Program.mapCounts, Program.mapCounts, sending, receiving, ih]
  | invoke site callee args next ih =>
    simp [project, Protocol.Program.mapCounts, Program.mapCounts, ih]
  | «repeat» site count initial body next bodyIH nextIH =>
    simp [project, Protocol.Program.mapCounts, Program.mapCounts, bodyIH, nextIH]
  | bind body next bodyIH nextIH =>
    simp [project, Protocol.Program.mapCounts, Program.mapCounts, bodyIH, nextIH]

theorem projectDefinitions_mapCounts [DecidableEq Role] (self : Role) (f : Count → Other)
    (definitions : Protocol.Definitions Count Role Binding Schema language locals scope) :
    projectDefinitions self (definitions.mapCounts f) =
      (projectDefinitions self definitions).mapCounts f := by
  induction definitions <;>
    simp_all [projectDefinitions, Protocol.Definitions.mapCounts, Definitions.mapCounts, project_mapCounts]

end Zkc.Compiler.Role
