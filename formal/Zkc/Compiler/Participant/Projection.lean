import Zkc.Compiler.Participant.Meaning
import Zkc.Source.Interpretation
import Zkc.Semantics.InterpretationAdmission

/-! Structural lowering from common protocols to scheduled participant instructions.

The proof covers arbitrary stored definitions, local operations, domain values,
transport packet types and fixed loop counts. It does not flatten shared bodies.
-/

set_option autoImplicit false

namespace Zkc.Compiler.Participant

open Zkc.Source Zkc.Source.Protocol
open Zkc.Source.LocatedExecution (Frame)

variable {Role Entry Binding Schema : Type} {language : Language}
  {locals : List (DefinitionSignature language.Ty)}
  {scope : List (Signature Role language.Ty)} {Value Packet : language.Ty → Type}

def project {Count : Type} {Γ results} : Protocol.Program Count Role Binding Schema language locals scope Γ results →
    Program Count Role Binding Schema language locals scope none Γ results
  | .ret values => .ret values
  | .stop site role reason => .stop site role reason
  | .localCall site role callee args next => .localCall site role callee args (project next)
  | .message site schema sender receiver different value next =>
      .send ⟨site, schema, sender, receiver, different, _⟩ value (.receive (project next))
  | .invoke site callee args next => .invoke site callee args (project next)
  | .repeat site count initial body next => .repeat site count initial (project body) (project next)
  | .bind body next => .bind (project body) (project next)

def projectDefinitions {Count : Type} {scope : List (Signature Role language.Ty)}
    (definitions : Protocol.Definitions Count Role Binding Schema language locals scope) :
    Definitions Count Role Binding Schema language locals scope :=
  match definitions with
  | .nil => .nil
  | .snoc previous signature body => .snoc (projectDefinitions previous) signature (project body)

theorem denote_project
    (sourceCalls : Protocol.CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) scope)
    (targetCalls : CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) (Packet := Packet) scope)
    (calls : ∀ {signature} (ref : Var scope signature) entry binding path args,
      targetCalls ref entry binding path (separate args.get) =
        (sourceCalls ref entry binding path args).interpret expand)
    {Γ results} (source : Protocol.Program Nat Role Binding Schema language locals scope Γ results)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (env : Environment (PortValue Value) Γ) :
    (project source).denote targetCalls entry binding path (separate env) () =
      (source.denote sourceCalls entry binding path env).interpret expand := by
  induction source generalizing path with
  | ret values => rfl
  | stop site role reason =>
      simp only [project, Program.denote, Protocol.Program.denote,
        PIR.Proc.interpret, expand, PIR.Proc.bind]
      congr 1
      funext reply
      cases reply
  | localCall site role callee args next ih =>
      simp only [project, Program.denote, Protocol.Program.denote,
        PIR.Proc.interpret, expand, PIR.Proc.bind, push_separate, ih]
      rw [readLocal_separate env role args]
  | message site schema sender receiver different value next ih =>
      simp only [project, Program.denote, Protocol.Program.denote, PIR.Proc.interpret,
        expand, PIR.Proc.bind, push_separate, ih]
      rfl
  | invoke site callee args next ih =>
      simp only [project, Program.denote, Protocol.Program.denote, capture_separate,
        calls, PIR.Proc.interpret_bind, prepend_separate, ih]
  | «repeat» site count initial body next bodyIH nextIH =>
      simp only [project, Program.denote, Protocol.Program.denote, assemble_separate,
        PIR.Proc.interpret_bind, interpret_repeat, prepend_separate, bodyIH, nextIH,
        PIR.Proc.interpret]
  | bind body next bodyIH nextIH =>
      simp only [project, Program.denote, Protocol.Program.denote,
        PIR.Proc.interpret_bind, prepend_separate, bodyIH, nextIH]

/-- The callee relation follows from the actual translated definition table. -/
theorem denote_projectDefinitions
    (definitions : Protocol.Definitions Nat Role Binding Schema language locals scope)
    {signature : Signature Role language.Ty} (ref : Var scope signature)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (args : Values (PortValue Value) signature.arguments) :
    (projectDefinitions definitions).denote (Packet := Packet) ref
      entry binding path (separate args.get) =
        (definitions.denote ref entry binding path args).interpret expand := by
  induction definitions generalizing signature entry binding path with
  | nil => cases ref
  | snoc previous signature body ih =>
      cases ref with
      | here =>
          exact denote_project previous.denote (projectDefinitions previous).denote
            (fun ref entry binding path args => ih ref entry binding path args)
            body entry binding path args.get
      | there ref => exact ih ref entry binding path args

/-- Expansion counts scheduled interface requests, not work inside local services. -/
theorem expand_within
    (op : (Protocol.interface Role Entry Binding Schema language locals Value).Op) :
    PIR.Within 2 (expand (Packet := Packet) op) := by
  cases op <;> simp [expand, PIR.Within]

/-- A source request bound transports to twice that bound on scheduled requests. -/
theorem within_projectDefinitions
    (definitions : Protocol.Definitions Nat Role Binding Schema language locals scope)
    {signature : Signature Role language.Ty} (ref : Var scope signature)
    (entry : Entry) (binding : Binding) (path : List Frame)
    (args : Values (PortValue Value) signature.arguments) (bound : Nat)
    (bounded : PIR.Within bound (definitions.denote ref entry binding path args)) :
    PIR.Within (bound * 2) ((projectDefinitions definitions).denote (Packet := Packet) ref
      entry binding path (separate args.get)) := by
  rw [denote_projectDefinitions]
  exact PIR.Proc.within_interpret expand 2 (fun op => expand_within op) _ bound bounded

end Zkc.Compiler.Participant
