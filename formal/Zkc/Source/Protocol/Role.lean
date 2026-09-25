import Zkc.Source.Protocol.Role.Interface

/-! Direct open meaning of the common protocol grammar for one role.

The definition recurses on source syntax and actual source definitions. It does
not call a compiler, target interpreter, joint evaluator or honest peer. Replies
are arbitrary typed local-service/peer replies. Foreign local calls are erased;
a foreign syntactic stop leaf instead has no continuation and is incomplete.
-/

set_option autoImplicit false

namespace Zkc.Source.Protocol.Role

open LocatedExecution (Frame)

variable {Party Entry Binding Schema : Type} [DecidableEq Party] {language : Language}
  {locals : List (DefinitionSignature language.Ty)} {Value : language.Ty → Type}

def denote (self : Party) {scope : List (Signature Party language.Ty)}
    (calls : CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) self scope)
    (entry : Entry) (binding : Binding) (path : List Frame) {Γ results} :
    Program Nat Party Binding Schema language locals scope Γ results →
      Environment Value self Γ →
        PIR.Proc (interface Party Entry Binding Schema language locals Value)
          (Environment Value self results)
  | .ret values, env => .done (env.capture values)
  | .stop site owner reason, _ =>
      if owner = self then
        .call (.stop ⟨entry, binding, path, site⟩ reason) fun reply => nomatch reply
      else .halt .incomplete
  | .localCall site owner callee args next, env =>
      if same : owner = self then
        let args := same ▸ args
        let next := same ▸ next
        .call (.local ⟨entry, binding, path, site⟩ callee (env.read args)) fun value =>
          denote self calls entry binding path next (env.push value)
      else denote self calls entry binding path next (env.skip same)
  | .message site schema sender receiver different value next, env =>
      if sending : sender = self then
        .call (.send ⟨entry, binding, path, site⟩ schema receiver (env (sending ▸ value)))
          fun _ => denote self calls entry binding path next
            (env.skip (fun receiving => different (sending.trans receiving.symm)))
      else if receiving : receiver = self then
        .call (.receive _ ⟨entry, binding, path, site⟩ schema sender) fun value =>
          denote self calls entry binding path (receiving ▸ next) (env.push value)
      else denote self calls entry binding path next (env.skip receiving)
  | .invoke site callee args next, env =>
      (calls callee.callee entry callee.binding (path ++ [.invocation site])
        (env.capture args)).bind fun values =>
          denote self calls entry binding path next (env.prepend values)
  | .repeat (ports := ports) site count initial body next, env =>
      (PIR.repeatN count (fun (acc : Nat × Environment Value self ports) =>
        (denote self calls entry binding (path ++ [.iteration site acc.1])
          body (env.prepend acc.2)).bind fun values =>
            .done (acc.1 + 1, values)) (0, env.capture initial)).bind fun acc =>
              denote self calls entry binding path next (env.prepend acc.2)
  | .bind body next, env =>
      (denote self calls entry binding path body env).bind fun values =>
        denote self calls entry binding path next (env.prepend values)

/-- Resolve actual stored source bodies with locally captured arguments only. -/
def denoteDefinitions (self : Party) {scope : List (Signature Party language.Ty)}
    (definitions : Definitions Nat Party Binding Schema language locals scope) :
    CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) self scope :=
  match definitions with
  | .nil => fun ref => nomatch ref
  | .snoc previous _ body => fun ref entry binding path args =>
      match ref with
      | .here => denote self (denoteDefinitions self previous) entry binding path body args
      | .there ref => denoteDefinitions self previous ref entry binding path args

/-- The first-profile foreign leaf has no reply, successful output or remote diagnostic. -/
theorem denote_foreign_stop (self owner : Party) (different : owner ≠ self)
    {scope : List (Signature Party language.Ty)}
    (calls : CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) self scope)
    (entry : Entry) (binding : Binding) (path : List Frame) {Γ results}
    (env : Environment Value self Γ) (site : Nat) (reason : PIR.Stop) :
    denote self calls entry binding path
      (.stop (results := results) site owner reason) env = .halt .incomplete := by
  simp only [denote, different, if_false]

/-- Erased foreign local work is never called, including a body that dynamically stops. -/
theorem denote_foreign_local (self owner : Party) (different : owner ≠ self)
    {scope : List (Signature Party language.Ty)}
    (calls : CallMeaning (Entry := Entry) (Binding := Binding) (Schema := Schema)
      (locals := locals) (Value := Value) self scope)
    (entry : Entry) (binding : Binding) (path : List Frame) {Γ results signature}
    (env : Environment Value self Γ) (site : Nat) (callee : Var locals signature)
    (args : Operands Γ (owned owner signature.arguments))
    (next : Program Nat Party Binding Schema language locals scope
      ((owner, signature.result) :: Γ) results) :
    denote self calls entry binding path (.localCall site owner callee args next) env =
      denote self calls entry binding path next (env.skip different) := by
  simp only [denote, different, dite_false]

end Zkc.Source.Protocol.Role
