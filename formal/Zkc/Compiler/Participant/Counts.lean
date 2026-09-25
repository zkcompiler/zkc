import Zkc.Compiler.Participant.Syntax
import Zkc.Compiler.Participant.Projection
import Zkc.Source.Protocol.Counts

/-! Structural count substitution. Substitution never unfolds a loop or a stored
callee; `Nat` is the resolved count carrier used by the execution semantics. -/

set_option autoImplicit false
namespace Zkc.Compiler.Participant
open Zkc.Source Zkc.Source.Protocol
variable {Count Other Third Role Binding Schema : Type} {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {scope : List (Signature Role language.Ty)}

def Program.mapCounts (f : Count → Other) {pending Γ results} :
    Program Count Role Binding Schema language locals scope pending Γ results → Program Other Role Binding Schema language locals scope pending Γ results
  | .ret values => .ret values
  | .stop site role reason => .stop site role reason
  | .localCall site role callee args next => .localCall site role callee args (next.mapCounts f)
  | .send transfer value next => .send transfer value (next.mapCounts f)
  | .receive next => .receive (next.mapCounts f)
  | .invoke site callee args next => .invoke site callee args (next.mapCounts f)
  | .repeat site count initial body next => .repeat site (f count) initial (body.mapCounts f) (next.mapCounts f)
  | .bind body next => .bind (body.mapCounts f) (next.mapCounts f)

theorem Program.mapCounts_id {pending Γ results} (program : Program Count Role Binding Schema language locals scope pending Γ results) :
    program.mapCounts id = program := by
  induction program <;> simp_all [mapCounts]

theorem Program.mapCounts_comp (f : Count → Other) (g : Other → Third)
    {pending Γ results} (program : Program Count Role Binding Schema language locals scope pending Γ results) :
    (program.mapCounts f).mapCounts g = program.mapCounts (g ∘ f) := by
  induction program <;> simp_all [mapCounts]

def Definitions.mapCounts (f : Count → Other)
    {scope : List (Signature Role language.Ty)} :
    Definitions Count Role Binding Schema language locals scope → Definitions Other Role Binding Schema language locals scope
  | .nil => .nil
  | .snoc previous signature body => .snoc (previous.mapCounts f) signature (body.mapCounts f)

theorem Definitions.mapCounts_id (definitions : Definitions Count Role Binding Schema language locals scope) :
    definitions.mapCounts id = definitions := by
  induction definitions <;> simp_all [mapCounts, Program.mapCounts_id]

theorem Definitions.mapCounts_comp (f : Count → Other) (g : Other → Third)
    (definitions : Definitions Count Role Binding Schema language locals scope) :
    (definitions.mapCounts f).mapCounts g = definitions.mapCounts (g ∘ f) := by
  induction definitions <;> simp_all [mapCounts, Program.mapCounts_comp]

theorem project_mapCounts (f : Count → Other) {Γ results}
    (program : Protocol.Program Count Role Binding Schema language locals scope Γ results) :
    project (program.mapCounts f) = (project program).mapCounts f := by
  induction program <;> simp_all [project, Protocol.Program.mapCounts, Program.mapCounts]

theorem projectDefinitions_mapCounts (f : Count → Other)
    (definitions : Protocol.Definitions Count Role Binding Schema language locals scope) :
    projectDefinitions (definitions.mapCounts f) = (projectDefinitions definitions).mapCounts f := by
  induction definitions <;>
    simp_all [projectDefinitions, Protocol.Definitions.mapCounts, Definitions.mapCounts, project_mapCounts]

end Zkc.Compiler.Participant
