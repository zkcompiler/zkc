module

public import Zkc.Source.Mathematical.Projection

@[expose] public section

/-! Common mathematical source with ordered, open role actions.

Pure calculations reuse mathematical blocks. An exchange aliases the sender's
component only at the sender; its receiver obtains an independent typed reply.
Guards stop only their owner. This finite, one-result profile has no implicit
joint execution or sampling policy.
-/

set_option autoImplicit false

namespace Zkc.Source.Common

structure Services (Ty : Type) where
  Op : Type
  arguments : Op → List Ty
  result : Op → Ty

inductive Program (Role : Type) (language : Language) (services : Services language.Ty) :
    List language.Ty → language.Ty → Type where
  | ret {Γ ty} (value : Var Γ ty) : Program Role language services Γ ty
  | calculate {Γ ty result} (body : Mathematical.Block Role language Γ result)
      (next : Program Role language services (result :: Γ) ty) : Program Role language services Γ ty
  | exchange {Γ ty sent} (site : String) (sender receiver : Role) (value : Var Γ sent)
      (next : Program Role language services (sent :: Γ) ty) : Program Role language services Γ ty
  | query {Γ ty} (site : String) (owner : Role) (op : services.Op)
      (args : Operands Γ (services.arguments op))
      (next : Program Role language services (services.result op :: Γ) ty) :
      Program Role language services Γ ty
  | guard {Γ ty} (site : String) (owner : Role) (condition : Var Γ language.condition)
      (next : Program Role language services Γ ty) : Program Role language services Γ ty
  | statement {Γ ty types} (relation : String) (selectors : List Role)
      (args : Operands Γ types) (next : Program Role language services Γ ty) :
      Program Role language services Γ ty

inductive Action (Role : Type) (language : Language) (services : Services language.Ty)
    (Value : language.Ty → Type) where
  | send {ty} (site : String) (receiver : Role) (value : Value ty)
  | receive (ty : language.Ty) (site : String) (sender : Role)
  | query (site : String) (op : services.Op) (args : Values Value (services.arguments op))

abbrev interface (Role : Type) (language : Language) (services : Services language.Ty)
    (Value : language.Ty → Type) : PIR.Signature where
  Op := Action Role language services Value
  Reply
    | .send .. => Unit
    | .receive ty .. => Value ty
    | .query _ op _ => Value (services.result op)

variable {Role : Type} [DecidableEq Role] {language : Language} {services : Services language.Ty}

def Program.denote (meaning : Mathematical.Meaning language)
    (condition : meaning.Value language.condition → Bool) (self : Role) {Γ ty} :
    Program Role language services Γ ty →
      Environment (fun sort => Option (meaning.Value sort)) Γ →
        PIR.Proc (interface Role language services meaning.Value) (Option (meaning.Value ty))
  | .ret value, env => .done (env value)
  | .calculate body next, env =>
      next.denote meaning condition self (env.push (body.evalAt meaning self env))
  | .exchange site sender receiver value next, env =>
      if sender = self then
        match env value with
        | none => .halt .incomplete
        | some sent => .call (.send site receiver sent) fun _ =>
            next.denote meaning condition self (env.push (some sent))
      else if receiver = self then
        .call (.receive _ site sender) fun received =>
          next.denote meaning condition self (env.push (some received))
      else next.denote meaning condition self (env.push none)
  | .query site owner op args next, env =>
      if owner = self then
        match RoleFamily.sequence (args.eval env) with
        | none => .halt .incomplete
        | some values => .call (.query site op values) fun value =>
            next.denote meaning condition self (env.push (some value))
      else next.denote meaning condition self (env.push none)
  | .guard _ owner ref next, env =>
      if owner = self then
        match env ref with
        | none => .halt .incomplete
        | some value => if condition value then next.denote meaning condition self env
                        else .halt .reject
      else next.denote meaning condition self env
  | .statement _ _ _ next, env => next.denote meaning condition self env

/-- The surrounding open process consumes the exact projected mathematical
component. State, events and failure behavior are inherited from that process. -/
theorem Program.calculate_projection (meaning : Mathematical.Meaning language)
    (condition : meaning.Value language.condition → Bool) (self : Role) {Γ ty result}
    (body : Mathematical.Block Role language Γ result)
    (next : Program Role language services (result :: Γ) ty)
    (env : Environment (fun sort => RoleFamily.Family Role (meaning.Value sort)) Γ) :
    (Program.calculate body next).denote meaning condition self (RoleFamily.project env self) =
      next.denote meaning condition self
        (Environment.push (RoleFamily.project env self) (body.eval meaning env self)) := by
  rw [Program.denote, Mathematical.Block.eval_project]

/-- Replace a calculation by any pointwise-equal block under an arbitrary open
suffix. This law does not decide equivalence or admit either original. -/
theorem Program.calculate_congr (meaning : Mathematical.Meaning language)
    (condition : meaning.Value language.condition → Bool) (self : Role) {Γ ty result}
    (first second : Mathematical.Block Role language Γ result)
    (next : Program Role language services (result :: Γ) ty)
    (env : Environment (fun sort => Option (meaning.Value sort)) Γ)
    (same : first.evalAt meaning self env = second.evalAt meaning self env) :
    (Program.calculate first next).denote meaning condition self env =
      (Program.calculate second next).denote meaning condition self env := by
  simp only [Program.denote, same]

def Program.scope {Γ ty} : Program Role language services Γ ty →
    Environment (fun _ => Role → Bool) Γ → Role → Bool
  | .ret value, scopes => scopes value
  | .calculate body next, scopes => next.scope (scopes.push (body.scope scopes))
  | .exchange _ sender receiver _ next, scopes =>
      next.scope (scopes.push fun role => decide (role = sender ∨ role = receiver))
  | .query _ owner _ _ next, scopes => next.scope (scopes.push fun role => decide (role = owner))
  | .guard _ _ _ next, scopes => next.scope scopes
  | .statement _ _ _ next, scopes => next.scope scopes

def statementAvailable {Γ types : List language.Ty} (scopes : Environment (fun _ => Role → Bool) Γ) :
    Operands Γ types → List Role → Bool
  | .nil, [] => true
  | .cons value rest, owner :: owners => scopes value owner && statementAvailable scopes rest owners
  | _, _ => false

/-- Every binding is checked before execution, including unused calculations.
Role-name and occurrence uniqueness are obligations of the concrete decoder. -/
def Program.check (roles : List Role) {Γ ty} : Program Role language services Γ ty →
    Environment (fun _ => Role → Bool) Γ → Bool
  | .ret value, scopes => roles.any (scopes value)
  | .calculate body next, scopes =>
      body.check roles scopes && next.check roles (scopes.push (body.scope scopes))
  | .exchange _ sender receiver value next, scopes =>
      decide (sender ∈ roles ∧ receiver ∈ roles ∧ sender ≠ receiver) && scopes value sender &&
        next.check roles (scopes.push fun role => decide (role = sender ∨ role = receiver))
  | .query _ owner _ args next, scopes =>
      decide (owner ∈ roles) && Mathematical.operandScope scopes args owner &&
        next.check roles (scopes.push fun role => decide (role = owner))
  | .guard _ owner value next, scopes =>
      decide (owner ∈ roles) && scopes value owner && next.check roles scopes
  | .statement _ selectors args next, scopes =>
      selectors.all (fun role => decide (role ∈ roles)) &&
        statementAvailable scopes args selectors && next.check roles scopes

end Zkc.Source.Common
