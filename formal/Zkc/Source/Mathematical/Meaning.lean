import Zkc.Source.Mathematical.Syntax
import Zkc.Source.LocatedExecution

/-! Independent open-role interpretation, before placement or demand analysis.
Every available pure binding is evaluated. Peer replies remain arbitrary. -/

set_option autoImplicit false
namespace Zkc.Source.Mathematical

structure Interpretation (language : Language) where
  Value : language.Ty → Type
  pure : (op : language.Op) → Values Value (language.arguments op) → Value (language.result op)
  condition : Value language.condition → Bool
  index : {count : Nat} → Fin count → Value (language.index count)

structure Location where
  path : List LocatedExecution.Frame
  site : Nat
  deriving DecidableEq, Repr

inductive Action {Role : Type} (self : Role) (language : Language)
    (capabilities : List (Capability Role language.Ty)) (Value : language.Ty → Type) where
  | send {ty} (location : Location) (schema : language.Wire ty) (receiver : Role) (value : Value ty)
  | receive {ty} (location : Location) (schema : language.Wire ty) (sender : Role)
  | query {signature} (location : Location) (capability : Var capabilities signature)
      (permitted : self ∈ signature.permitted) (args : Values Value signature.arguments)
  | stop (location : Location) (reason : PIR.Stop)

abbrev interface {Role : Type} (self : Role) (language : Language)
    (capabilities : List (Capability Role language.Ty)) (Value : language.Ty → Type) :
    PIR.Signature where
  Op := Action self language capabilities Value
  Reply
    | .send .. => Unit
    | .receive (ty := ty) .. => Value ty
    | .query (signature := signature) .. => Value signature.result
    | .stop .. => Empty

variable {Role : Type} [DecidableEq Role] {parties : List Role} {language : Language}
  {capabilities : List (Capability Role language.Ty)}

/-- Iterate a compact body at each actual bounded index, with no fabricated zero index. -/
def indexed {I : PIR.Signature} {A : Type} : (count : Nat) →
    (Fin count → A → PIR.Proc I A) → A → PIR.Proc I A
  | 0, _, initial => .done initial
  | n + 1, body, initial => (body 0 initial).bind (indexed n (fun i => body i.succ))

@[simp] theorem indexed_zero {I : PIR.Signature} {A : Type}
    (body : Fin 0 → A → PIR.Proc I A) (initial : A) : indexed 0 body initial = .done initial := rfl

/-- Unfold at the actual first index; the residual body receives successor indices. -/
theorem indexed_succ {I : PIR.Signature} {A : Type} (n : Nat)
    (body : Fin (n + 1) → A → PIR.Proc I A) (initial : A) :
    indexed (n + 1) body initial =
      (body 0 initial).bind (indexed n (fun i => body i.succ)) := rfl


/-- Ignoring the index recovers existing finite repetition exactly. -/
theorem indexed_constant {I : PIR.Signature} {A : Type} (count : Nat)
    (body : A → PIR.Proc I A) (initial : A) :
    indexed count (fun _ => body) initial = PIR.repeatN count body initial := by
  induction count generalizing initial with
  | zero => rfl
  | succ count ih =>
      simp only [indexed_succ, PIR.repeatN]
      congr 1
      funext value
      exact ih value

abbrev CallMeaning (meaning : Interpretation language) (self : Role)
    (scope : List (Signature Role language.Ty)) :=
  {signature : Signature Role language.Ty} → Var scope signature →
    CapabilityBinding capabilities → List LocatedExecution.Frame →
    Values (Component meaning.Value self) signature.arguments →
    PIR.Proc (interface self language capabilities meaning.Value)
      (Values (Component meaning.Value self) signature.results)

def Program.denote (meaning : Interpretation language) (self : Role)
    {scope : List (Signature Role language.Ty)}
    (calls : CallMeaning (capabilities := capabilities) meaning self scope)
    (capabilityBinding : CapabilityBinding capabilities)
    (path : List LocatedExecution.Frame) {Γ results} :
    Program parties language capabilities scope Γ results → Environment meaning.Value self Γ →
      PIR.Proc (interface self language capabilities meaning.Value)
        (Values (Component meaning.Value self) results)
  | .ret values, env => .done (Bindings.read values env)
  | .pure op args availability next, env =>
      next.denote meaning self calls capabilityBinding path
        (env.push (fun h => meaning.pure op (Inputs.read parties args env (availability ▸ h))))
  | .message (ty := ty) site schema sender receiver _ value next, env =>
      if sending : self = sender then
        .call (.send ⟨path, site⟩ schema receiver (value.read env (by simp [sending]))) fun _ =>
          next.denote meaning self calls capabilityBinding path
            (env.push (ty := ⟨[sender, receiver], ty⟩)
              (fun _ => value.read env (by simp [sending])))
      else if receiving : self = receiver then
        .call (.receive ⟨path, site⟩ schema sender) fun reply =>
          next.denote meaning self calls capabilityBinding path (env.push (fun _ => reply))
      else
        next.denote meaning self calls capabilityBinding path (env.push (fun h => by simp_all))
  | .query site owner capability permitted args available next, env =>
      if owned : self = owner then
        .call (.query ⟨path, site⟩ (capabilityBinding capability) (owned.symm ▸ permitted) (Inputs.read parties args env (owned.symm ▸ available)))
          fun reply => next.denote meaning self calls capabilityBinding path (env.push (fun _ => reply))
      else next.denote meaning self calls capabilityBinding path (env.push (fun h => by simp_all))
  | .repeat site count initial body next, env =>
      (indexed count (fun index values =>
        body.denote meaning self calls capabilityBinding (path ++ [.iteration site index.val])
          (Source.Environment.push (env.prepend values)
            (fun _ => meaning.index index))) (Bindings.read initial env)).bind
        fun values => next.denote meaning self calls capabilityBinding path (env.prepend values)
  | .guard site owner condition next, env =>
      if owned : self = owner then
        if meaning.condition (condition.read env (by simp [owned])) then
          next.denote meaning self calls capabilityBinding path env
        else .call (.stop ⟨path, site⟩ .reject) fun reply => nomatch reply
      else next.denote meaning self calls capabilityBinding path env
  | .invoke site callee binding arguments next, env =>
      (calls callee (fun ref => capabilityBinding (binding ref))
        (path ++ [.invocation site]) (Bindings.read arguments env)).bind fun values =>
          next.denote meaning self calls capabilityBinding path (env.prepend values)
  | .stop site owner reason, _ =>
      if self = owner then .call (.stop ⟨path, site⟩ reason) fun reply => nomatch reply
      else .halt .incomplete

/-- The program-level round step threads the actual first result into the
remaining indexed rounds, then into the continuation. -/
theorem Program.denote_repeat_succ (meaning : Interpretation language) (self : Role)
    {scope Γ results ports} (calls : CallMeaning (capabilities := capabilities) meaning self scope)
    (roots : CapabilityBinding capabilities) (path : List LocatedExecution.Frame)
    (site n : Nat) (initial : Bindings Γ ports)
    (body : Program parties language capabilities scope
      (⟨parties, language.index (n + 1)⟩ :: (ports ++ Γ)) ports)
    (next : Program parties language capabilities scope (ports ++ Γ) results)
    (env : Environment meaning.Value self Γ) :
    let step := fun (index : Fin (n + 1)) values =>
      body.denote meaning self calls roots (path ++ [.iteration site index.val])
        (Source.Environment.push (env.prepend values) (fun _ => meaning.index index))
    (Program.repeat site (n + 1) initial body next).denote meaning self calls roots path env =
      (step 0 (Bindings.read initial env)).bind (fun first =>
        (indexed n (fun i => step i.succ) first).bind (fun values =>
          next.denote meaning self calls roots path (env.prepend values))) := by
  dsimp only
  simp only [Program.denote, indexed_succ]
  exact PIR.Proc.bind_assoc _ _ _

/-- Calls interpret the actual earlier body and keep the resolved root identity. -/
def Definitions.denote (meaning : Interpretation language) (self : Role) {scope}
    (definitions : Definitions parties language capabilities scope) :
    CallMeaning (capabilities := capabilities) meaning self scope :=
  match definitions with
  | .nil => fun ref => nomatch ref
  | .snoc previous _ body => fun ref binding path arguments =>
      match ref with
      | .here => body.denote meaning self (previous.denote meaning self) binding path
          (fun operand => arguments.get operand)
      | .there ref => previous.denote meaning self ref binding path arguments

def Program.openMeaning (meaning : Interpretation language) (self : Role) {Γ results}
    (program : Program parties language capabilities [] Γ results)
    (env : Environment meaning.Value self Γ) :=
  program.denote meaning self (Definitions.denote (parties := parties) meaning self .nil)
    (fun ref => ref) [] env

/-- A closed entry selects an actual stored definition and root binding. -/
def Definitions.entry (meaning : Interpretation language) (self : Role) {scope signature}
    (definitions : Definitions parties language capabilities scope)
    (callee : Var scope signature) (roots : CapabilityBinding capabilities)
    (arguments : Values (Component meaning.Value self) signature.arguments) :=
  definitions.denote meaning self callee roots [] arguments

end Zkc.Source.Mathematical
