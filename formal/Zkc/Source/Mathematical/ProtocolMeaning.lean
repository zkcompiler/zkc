import Zkc.Source.Mathematical.Protocol

/-! Open-role execution of intrinsic graph protocols.

Pure graph interpretation is total. Ordered services, local operations, sends
and receives stay explicit actions; peer replies are arbitrary. Instantiated
calls are interpreted by the selected earlier-definition environment.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Protocol

inductive Action {Role : Type} (self : Role) (vocabulary : Vocabulary)
    (Value : vocabulary.Ty → Type) where
  | send {ty} (location : Location) (schema : vocabulary.Wire ty) (receiver : Role) (value : Value ty)
  | receive {ty} (location : Location) (schema : vocabulary.Wire ty) (sender : Role)
  | query (location : Location) (root : Nat) (service : vocabulary.Service)
      (arguments : Values Value (vocabulary.serviceArguments service))
  | local (location : Location) (op : vocabulary.Local) (roots : List Nat)
      (arguments : Values Value (vocabulary.localArguments op))
  | stop (location : Location) (reason : PIR.Stop)

abbrev interface {Role : Type} (self : Role) (vocabulary : Vocabulary)
    (Value : vocabulary.Ty → Type) : PIR.Signature where
  Op := Action self vocabulary Value
  Reply
    | .send .. => Unit
    | .receive (ty := ty) .. => Value ty
    | .query _ _ service _ => Value (vocabulary.serviceResult service)
    | .local _ op _ _ => Value (vocabulary.localResult op)
    | .stop .. => Empty

variable {Role : Type} [DecidableEq Role] {vocabulary : Vocabulary}
  {parties : List Role} {capabilities : List (Capability Role vocabulary.Service)}

abbrev CallMeaning (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    (scope : List (Signature Role vocabulary)) :=
  {signature : Signature Role vocabulary} → Var scope signature →
    CapabilityBindings capabilities signature.capabilities → List LocatedExecution.Frame →
    Values (Component meaning.Value self) signature.arguments →
    PIR.Proc (interface self vocabulary meaning.Value)
      (Values (Component meaning.Value self) signature.results)

/-- Checked call interpretation consumes the contract proof at each call. No
runtime refusal is needed to rediscover an admission invariant. -/
abbrev CheckedCallMeaning (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    (scope : List (Signature Role vocabulary))
    (condition : CallCondition (vocabulary := vocabulary) capabilities scope) :=
  {signature : Signature Role vocabulary} → (callee : Var scope signature) →
    (bindings : CapabilityBindings capabilities signature.capabilities) → condition callee bindings →
    List LocatedExecution.Frame → Values (Component meaning.Value self) signature.arguments →
    PIR.Proc (interface self vocabulary meaning.Value) (Values (Component meaning.Value self) signature.results)

def Program.denoteChecked (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    {scope : List (Signature Role vocabulary)} {condition : CallCondition (vocabulary := vocabulary) capabilities scope}
    (calls : CheckedCallMeaning (capabilities := capabilities) meaning self scope condition)
    (path : List LocatedExecution.Frame) {Γ results start finish} :
    (program : Program parties vocabulary capabilities scope Γ results start finish) →
      program.CallsSatisfy condition → Environment meaning.Value self Γ →
      PIR.Proc (interface self vocabulary meaning.Value) (Values (Component meaning.Value self) results)
  | .ret values, _, env => .done (Bindings.read values env)
  | .pure capture region next, valid, env =>
      let captured := Operands.eval env capture
      let values := region.denote meaning self (fun v => captured.get v)
      next.denoteChecked meaning self calls path valid (env.prepend values)
  | .local owner _ op bindings arguments available next, valid, env =>
      if owned : self = owner then
        .call (.local ⟨path, start⟩ op bindings.roots
          (Inputs.read parties arguments env (owned.symm ▸ available))) fun reply =>
            next.denoteChecked meaning self calls path valid (env.push (fun _ => reply))
      else next.denoteChecked meaning self calls path valid (env.push (fun h => by simp_all))
  | .query (signature := signature) owner _ _ _ arguments available next, valid, env =>
      if owned : self = owner then
        .call (.query ⟨path, start⟩ signature.root signature.service
          (Inputs.read parties arguments env (owned.symm ▸ available))) fun reply =>
            next.denoteChecked meaning self calls path valid (env.push (fun _ => reply))
      else next.denoteChecked meaning self calls path valid (env.push (fun h => by simp_all))
  | .guard owner _ test next, valid, env =>
      if owned : self = owner then
        if meaning.condition (test.read env (by simp [owned])) then
          next.denoteChecked meaning self calls path valid env
        else .call (.stop ⟨path, start⟩ .reject) fun reply => nomatch reply
      else next.denoteChecked meaning self calls path valid env
  | .message (ty := ty) schema sender receiver _ _ _ value next, valid, env =>
      if sending : self = sender then
        .call (.send ⟨path, start⟩ schema receiver (value.read env (by simp [sending]))) fun _ =>
          next.denoteChecked meaning self calls path valid
            (env.push (ty := ⟨messageRoles parties sender receiver, ty⟩)
              (fun _ => value.read env (by simp [sending])))
      else if receiving : self = receiver then
        .call (.receive ⟨path, start⟩ schema sender) fun reply =>
          next.denoteChecked meaning self calls path valid (env.push (fun _ => reply))
      else next.denoteChecked meaning self calls path valid (env.push (fun h => by simp_all [messageRoles]))
  | .invoke callee _ binding arguments next, valid, env =>
      (calls callee binding valid.1 (path ++ [.invocation start]) (Bindings.read arguments env)).bind fun values =>
        next.denoteChecked meaning self calls path valid.2 (env.prepend values)
  | .repeat count initial capture body next, valid, env =>
      let captured := Operands.eval env capture
      (indexed (meaning.count count) (fun index values =>
        body.denoteChecked meaning self calls (path ++ [.iteration start index.val]) valid.1
          (Source.Environment.push (Source.Environment.prepend (fun v => captured.get v) values)
            (fun _ => meaning.index index))) (Bindings.read initial env)).bind fun values =>
          next.denoteChecked meaning self calls path valid.2 (env.prepend values)
  | .stop owner _ reason, _, _ =>
      if self = owner then .call (.stop ⟨path, start⟩ reason) fun reply => nomatch reply
      else .halt .incomplete

/-- The unrestricted interpretation is the checked interpreter with the
trivial call contract. Graph, effect and iteration semantics remain shared. -/
def Program.denote (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    {scope : List (Signature Role vocabulary)}
    (calls : CallMeaning (capabilities := capabilities) meaning self scope)
    (path : List LocatedExecution.Frame) {Γ results start finish}
    (program : Program parties vocabulary capabilities scope Γ results start finish)
    (env : Environment meaning.Value self Γ) :=
  program.denoteChecked meaning self (condition := fun _ _ => True)
    (fun callee bindings _ => calls callee bindings) path program.callsSatisfy_true env

def Program.openMeaning (meaning : Graph.Interpretation vocabulary.toAlgebra) (self : Role)
    {Γ results start finish}
    (program : Program parties vocabulary capabilities [] Γ results start finish)
    (env : Environment meaning.Value self Γ) :=
  program.denote meaning self
    (fun {signature} (ref : Var ([] : List (Signature Role vocabulary)) signature) => nomatch ref) [] env

end Zkc.Source.Mathematical.Protocol
