import Zkc.Compiler.Role.Meaning
import Zkc.Source.Protocol.Role

/-! Mechanical role extraction and exact direct-source/target equality.
The call-table premise in the compositional lemma is discharged for every
actual stored definition table. No honest-peer or total-local-service law is used.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Role

open Zkc.Source Zkc.Source.Protocol
open Zkc.Source.Protocol.Role (Environment CallMeaning interface)
open Zkc.Source.LocatedExecution (Frame)

variable {Party Entry Binding Schema : Type} [DecidableEq Party] {self : Party}
  {language : Language} {locals : List (DefinitionSignature language.Ty)}
  {scope : List (Signature Party language.Ty)} {Value : language.Ty → Type}

def project {Count : Type} (self : Party) {Γ results} :
    Protocol.Program Count Party Binding Schema language locals scope Γ results →
      Program Count self Binding Schema language locals scope Γ results
  | .ret values => .ret values
  | .stop site owner reason => if owner = self then .stop site reason else .incomplete
  | .localCall site owner callee args next =>
      if same : owner = self then
        .localCall site callee (same ▸ args) (same ▸ project self next)
      else .skip same (project self next)
  | .message site schema sender receiver different value next =>
      if sending : sender = self then
        let foreign := fun receiving => different (sending.trans receiving.symm)
        .send site schema receiver foreign (sending ▸ value) (.skip foreign (project self next))
      else if receiving : receiver = self then
        .receive _ site schema sender sending (receiving ▸ project self next)
      else .skip receiving (project self next)
  | .invoke site callee args next => .invoke site callee args (project self next)
  | .repeat site count initial body next =>
      .repeat site count initial (project self body) (project self next)
  | .bind body next => .bind (project self body) (project self next)

def projectDefinitions {Count : Type} (self : Party) {scope : List (Signature Party language.Ty)}
    (definitions : Protocol.Definitions Count Party Binding Schema language locals scope) :
    Definitions Count self Binding Schema language locals scope :=
  match definitions with
  | .nil => .nil
  | .snoc previous signature body =>
      .snoc (projectDefinitions self previous) signature (project self body)

theorem denote_project
    (sourceCalls targetCalls : CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) self scope)
    (calls : ∀ {signature} (ref : Var scope signature) entry binding path args,
      targetCalls ref entry binding path args = sourceCalls ref entry binding path args)
    {Γ results} (source : Protocol.Program Nat Party Binding Schema language locals scope Γ results)
    (entry : Entry) (binding : Binding) (path : List Frame) (env : Environment Value self Γ) :
    (project self source).denote targetCalls entry binding path env =
      Protocol.Role.denote self sourceCalls entry binding path source env := by
  induction source generalizing path with
  | ret values => simp only [project, Program.denote, Protocol.Role.denote]
  | stop site owner reason =>
      by_cases same : owner = self <;>
        simp only [project, Program.denote, Protocol.Role.denote, same, if_true, if_false]
      congr 1
  | localCall site owner callee args next ih =>
      by_cases same : owner = self
      · subst owner
        simp only [project, Program.denote, Protocol.Role.denote, dite_true, ih]
      · simp only [project, Program.denote, Protocol.Role.denote, same, dite_false, ih]
  | message site schema sender receiver different value next ih =>
      by_cases sending : sender = self
      · subst sender
        simp only [project, Program.denote, Protocol.Role.denote, dite_true, ih]
      · by_cases receiving : receiver = self
        · subst receiver
          simp only [project, Program.denote, Protocol.Role.denote, sending, dite_false,
            dite_true, ih]
        · simp only [project, Program.denote, Protocol.Role.denote, sending, receiving,
            dite_false, ih]
  | invoke site callee args next ih =>
      simp only [project, Program.denote, Protocol.Role.denote, calls, ih]
  | «repeat» site count initial body next bodyIH nextIH =>
      simp only [project, Program.denote, Protocol.Role.denote, bodyIH, nextIH]
  | bind body next bodyIH nextIH =>
      simp only [project, Program.denote, Protocol.Role.denote, bodyIH, nextIH]

/-- Unconditional equality for actual acyclic call tables, at every reference and binding. -/
theorem denote_projectDefinitions
    (definitions : Protocol.Definitions Nat Party Binding Schema language locals scope)
    {signature : Signature Party language.Ty} (ref : Var scope signature)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (args : Environment Value self signature.arguments) :
    (projectDefinitions self definitions).denote ref entry binding path args =
      Protocol.Role.denoteDefinitions self definitions ref entry binding path args := by
  induction definitions generalizing signature entry binding path with
  | nil => cases ref
  | snoc previous signature body ih =>
      cases ref with
      | here =>
          exact denote_project (Protocol.Role.denoteDefinitions self previous)
            (projectDefinitions self previous).denote
            (fun ref entry binding path args => ih ref entry binding path args)
            body entry binding path args
      | there ref => exact ih ref entry binding path args

/-- Complete local outcome, residual state and events for any completed typed strategy. -/
theorem run_project {S E : Type}
    (handler : PIR.Handler (interface Party Entry Binding Schema language locals Value) S E)
    (definitions : Protocol.Definitions Nat Party Binding Schema language locals scope)
    {signature : Signature Party language.Ty} (ref : Var scope signature)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (args : Environment Value self signature.arguments) (state : S) :
    ((projectDefinitions self definitions).denote ref entry binding path args).run handler state =
      (Protocol.Role.denoteDefinitions self definitions ref entry binding path args).run
        handler state := by
  rw [denote_projectDefinitions]

/-- Different local implementations/strategies are supported under their actual per-action law.
This is source-role/target-role transport, not a joint/open scheduling theorem. -/
theorem run_project_related {S T E F O : Type}
    (relation : S → T → Prop) (left : E → List O) (right : F → List O)
    (sourceHandler : PIR.Handler (interface Party Entry Binding Schema language locals Value) S E)
    (targetHandler : PIR.Handler (interface Party Entry Binding Schema language locals Value) T F)
    (law : PIR.HandlerRelated relation left right sourceHandler targetHandler)
    (definitions : Protocol.Definitions Nat Party Binding Schema language locals scope)
    {signature : Signature Party language.Ty} (ref : Var scope signature)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (args : Environment Value self signature.arguments) (sourceState : S) (targetState : T)
    (initial : relation sourceState targetState) :
    PIR.Related relation left right
      ((Protocol.Role.denoteDefinitions self definitions ref entry binding path args).run
        sourceHandler sourceState)
      (((projectDefinitions self definitions).denote ref entry binding path args).run
        targetHandler targetState) := by
  rw [denote_projectDefinitions]
  exact PIR.run_related relation left right sourceHandler targetHandler law _ _ _ initial

end Zkc.Compiler.Role
