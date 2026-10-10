import Zkc.Source.Protocol.Syntax

/-! Structural count substitution. Substitution never unfolds a loop or a stored
callee; `Nat` is the resolved count carrier used by the execution semantics. -/

set_option autoImplicit false
namespace Zkc.Source.Protocol
variable {Count Other Third Role Binding Schema : Type} {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {scope : List (Signature Role language.Ty)}

def Program.mapCounts (f : Count → Other) {Γ results} :
    Program Count Role Binding Schema language locals scope Γ results → Program Other Role Binding Schema language locals scope Γ results
  | .ret values => .ret values
  | .stop site role reason => .stop site role reason
  | .localCall site role callee args next => .localCall site role callee args (next.mapCounts f)
  | .message site schema sender receiver different value next => .message site schema sender receiver different value (next.mapCounts f)
  | .invoke site callee args next => .invoke site callee args (next.mapCounts f)
  | .repeat site count initial body next => .repeat site (f count) initial (body.mapCounts f) (next.mapCounts f)
  | .bind body next => .bind (body.mapCounts f) (next.mapCounts f)

theorem Program.mapCounts_id {Γ results} (program : Program Count Role Binding Schema language locals scope Γ results) :
    program.mapCounts id = program := by
  induction program <;> simp_all [mapCounts]

theorem Program.mapCounts_comp (f : Count → Other) (g : Other → Third)
    {Γ results} (program : Program Count Role Binding Schema language locals scope Γ results) :
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

/-- Structural IR size, independent of any resolved loop trip count. -/
def Program.nodeCount {Γ results} : Program Count Role Binding Schema language locals scope Γ results → Nat
  | .ret _ => 1
  | .stop _ _ _ => 1
  | .localCall _ _ _ _ next => 1 + next.nodeCount
  | .message _ _ _ _ _ _ next => 1 + next.nodeCount
  | .invoke _ _ _ next => 1 + next.nodeCount
  | .repeat _ _ _ body next => 1 + body.nodeCount + next.nodeCount
  | .bind body next => 1 + body.nodeCount + next.nodeCount

theorem Program.nodeCount_mapCounts (f : Count → Other) {Γ results}
    (program : Program Count Role Binding Schema language locals scope Γ results) :
    (program.mapCounts f).nodeCount = program.nodeCount := by
  induction program <;> simp_all [mapCounts, nodeCount]

end Zkc.Source.Protocol
