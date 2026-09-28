import Zkc.Source.Mathematical.GraphAdmission

/-! Intrinsic ordered protocols over the shared graph algebra.

Static counts remain parametric. Effects are indexed by their dense preorder
site interval, repeat bodies receive only declared carried values and captures,
and capability bindings are finite typed references with explicit root identity.
The resolved call scope is supplied by earlier-definition admission. Formed
templates retain root requirements; closed admission additionally discharges
them against actual roots.
-/

set_option autoImplicit false
namespace Zkc.Source.Mathematical.Protocol

structure Vocabulary extends Graph.Algebra where
  Service : Type
  serviceArguments : Service → List Ty
  serviceResult : Service → Ty
  Local : Type
  localCapabilities : Local → List Service
  localArguments : Local → List Ty
  localResult : Local → Ty
  localDistinct : Local → List (Nat × Nat)

structure Permission (Role Service : Type) where
  service : Service
  roles : List Role
  deriving DecidableEq, Repr

structure Capability (Role Service : Type) extends Permission Role Service where
  root : Nat
  deriving DecidableEq, Repr

variable {Role : Type} [DecidableEq Role] {vocabulary : Vocabulary}

abbrev Ports := List (Port Role vocabulary.Ty)
abbrev Capabilities := List (Capability Role vocabulary.Service)

/-- The selected capability retains its actual permissions and root. A required
port may weaken permissions, but cannot change the service signature. -/
structure CapabilityReference (capabilities : Capabilities (Role := Role) (vocabulary := vocabulary))
    (required : Permission Role vocabulary.Service) where
  available : List Role
  root : Nat
  operand : Var capabilities ⟨⟨required.service, available⟩, root⟩
  covers : ∀ role ∈ required.roles, role ∈ available

abbrev CapabilityBindings (capabilities : Capabilities (Role := Role) (vocabulary := vocabulary))
    (required : List (Permission Role vocabulary.Service)) :=
  Values (CapabilityReference capabilities) required

def CapabilityBindings.roots {capabilities required} :
    CapabilityBindings (Role := Role) (vocabulary := vocabulary) capabilities required → List Nat
  | .nil => []
  | .cons ref rest => ref.root :: CapabilityBindings.roots rest

def CapabilityBindings.indices {capabilities required} :
    CapabilityBindings (Role := Role) (vocabulary := vocabulary) capabilities required → List Nat
  | .nil => []
  | .cons ref rest => ref.operand.index :: CapabilityBindings.indices rest

/-- A callee receives only the required permission set. Root identity follows
the selected caller capability, including aliases. -/
def CapabilityBindings.bound {capabilities required} :
    CapabilityBindings (Role := Role) (vocabulary := vocabulary) capabilities required →
      List (Capability Role vocabulary.Service)
  | .nil => []
  | .cons (ty := required) ref rest => ⟨required, ref.root⟩ :: CapabilityBindings.bound rest

omit [DecidableEq Role] in
theorem CapabilityBindings.bound_permissions {capabilities required}
    (bindings : CapabilityBindings (Role := Role) (vocabulary := vocabulary) capabilities required) :
    bindings.bound.map Capability.toPermission = required := by
  induction bindings with
  | nil => rfl
  | cons ref rest ih => simp [bound, ih]

omit [DecidableEq Role] in
theorem CapabilityBindings.bound_roots {capabilities required}
    (bindings : CapabilityBindings (Role := Role) (vocabulary := vocabulary) capabilities required) :
    bindings.bound.map Capability.root = bindings.roots := by
  induction bindings with
  | nil => rfl
  | cons ref rest ih => simp [bound, roots, ih]

def distinctRoots (roots : List Nat) (pairs : List (Nat × Nat)) : Bool :=
  pairs.all fun (left, right) => match roots[left]?, roots[right]? with
    | some a, some b => a != b
    | _, _ => false

def localPermissions (owner : Role) (op : vocabulary.Local) :
    List (Permission Role vocabulary.Service) :=
  (vocabulary.localCapabilities op).map fun service => ⟨service, [owner]⟩

structure Signature (Role : Type) (vocabulary : Vocabulary) where
  parties : List Role
  capabilities : List (Permission Role vocabulary.Service)
  arguments : List (Port Role vocabulary.Ty)
  results : List (Port Role vocabulary.Ty)

/-- Canonical message availability follows the participating-role order. -/
def messageRoles (parties : List Role) (sender receiver : Role) : List Role :=
  parties.filter fun role => role = sender ∨ role = receiver

/-- Intrinsic site intervals count syntax, including dormant indexed bodies.
Each indexed body is stored once; the interval does not depend on its count. -/
inductive Program (parties : List Role) (vocabulary : Vocabulary)
    (capabilities : List (Capability Role vocabulary.Service))
    (scope : List (Signature Role vocabulary)) :
    List (Port Role vocabulary.Ty) → List (Port Role vocabulary.Ty) → Nat → Nat → Type where
  | ret {Γ results site} (values : Bindings Γ results) :
      Program parties vocabulary capabilities scope Γ results site site
  | pure {Γ results captures outputs start finish}
      (capture : Operands Γ captures)
      (region : Graph.Region parties vocabulary.toAlgebra captures outputs)
      (next : Program parties vocabulary capabilities scope (outputs ++ Γ) results start finish) :
      Program parties vocabulary capabilities scope Γ results start finish
  | local {Γ results site finish} (owner : Role) (participates : owner ∈ parties)
      (op : vocabulary.Local)
      (bindings : CapabilityBindings capabilities (localPermissions owner op))
      (arguments : Inputs Γ (vocabulary.localArguments op))
      (available : owner ∈ Inputs.available parties arguments)
      (next : Program parties vocabulary capabilities scope
        (⟨[owner], vocabulary.localResult op⟩ :: Γ) results (site + 1) finish) :
      Program parties vocabulary capabilities scope Γ results site finish
  | query {Γ results signature site finish} (owner : Role) (participates : owner ∈ parties)
      (capability : Var capabilities signature) (permitted : owner ∈ signature.roles)
      (arguments : Inputs Γ (vocabulary.serviceArguments signature.service))
      (available : owner ∈ Inputs.available parties arguments)
      (next : Program parties vocabulary capabilities scope
        (⟨[owner], vocabulary.serviceResult signature.service⟩ :: Γ) results (site + 1) finish) :
      Program parties vocabulary capabilities scope Γ results site finish
  | guard {Γ results site finish} (owner : Role) (participates : owner ∈ parties)
      (condition : Reference Γ ⟨[owner], vocabulary.condition⟩)
      (next : Program parties vocabulary capabilities scope Γ results (site + 1) finish) :
      Program parties vocabulary capabilities scope Γ results site finish
  | message {Γ results ty site finish} (schema : vocabulary.Wire ty)
      (sender receiver : Role) (sending : sender ∈ parties) (receiving : receiver ∈ parties)
      (different : sender ≠ receiver) (value : Reference Γ ⟨[sender], ty⟩)
      (next : Program parties vocabulary capabilities scope
        (⟨messageRoles parties sender receiver, ty⟩ :: Γ) results (site + 1) finish) :
      Program parties vocabulary capabilities scope Γ results site finish
  | invoke {Γ results signature site finish} (callee : Var scope signature)
      (participates : ∀ role ∈ signature.parties, role ∈ parties)
      (binding : CapabilityBindings capabilities signature.capabilities)
      (arguments : Bindings Γ signature.arguments)
      (next : Program parties vocabulary capabilities scope
        (signature.results ++ Γ) results (site + 1) finish) :
      Program parties vocabulary capabilities scope Γ results site finish
  | repeat {Γ results carried captures site middle finish} (count : vocabulary.Count)
      (initial : Bindings Γ carried) (capture : Operands Γ captures)
      (body : Program parties vocabulary capabilities scope
        (⟨parties, vocabulary.index count⟩ :: (carried ++ captures)) carried (site + 1) middle)
      (next : Program parties vocabulary capabilities scope (carried ++ Γ) results middle finish) :
      Program parties vocabulary capabilities scope Γ results site finish
  | stop {Γ results site} (owner : Role) (participates : owner ∈ parties) (reason : PIR.Stop) :
      Program parties vocabulary capabilities scope Γ results site (site + 1)

variable {parties : List Role} {capabilities : List (Capability Role vocabulary.Service)}
  {scope : List (Signature Role vocabulary)}

/-- A call contract is checked at each syntactic invocation, including those
inside dormant repeat bodies. The generic language does not prescribe which
contract a caller uses; stored closed definitions use exact root bindings. -/
abbrev CallCondition (capabilities : List (Capability Role vocabulary.Service))
    (scope : List (Signature Role vocabulary)) :=
  {signature : Signature Role vocabulary} → (callee : Var scope signature) →
    CapabilityBindings capabilities signature.capabilities → Prop

def Program.CallsSatisfy {Γ results start finish}
    (condition : CallCondition (vocabulary := vocabulary) capabilities scope) :
    Program parties vocabulary capabilities scope Γ results start finish → Prop
  | .ret _ | .stop .. => True
  | .pure _ _ next | .local _ _ _ _ _ _ next | .query _ _ _ _ _ _ next |
    .guard _ _ _ next | .message _ _ _ _ _ _ _ next => next.CallsSatisfy condition
  | .invoke callee _ bindings _ next => condition callee bindings ∧ next.CallsSatisfy condition
  | .repeat _ _ _ body next => body.CallsSatisfy condition ∧ next.CallsSatisfy condition

theorem Program.callsSatisfy_true {Γ results start finish}
    (program : Program parties vocabulary capabilities scope Γ results start finish) :
    program.CallsSatisfy (fun _ _ => True) := by
  induction program <;> simp_all [CallsSatisfy]

def Program.sites {Γ results start finish} :
    Program parties vocabulary capabilities scope Γ results start finish → List Nat
  | .ret _ => []
  | .pure _ _ next => next.sites
  | .local _ _ _ _ _ _ next => start :: next.sites
  | .query _ _ _ _ _ _ next => start :: next.sites
  | .guard _ _ _ next => start :: next.sites
  | .message _ _ _ _ _ _ _ next => start :: next.sites
  | .invoke _ _ _ _ next => start :: next.sites
  | .repeat _ _ _ body next => start :: (body.sites ++ next.sites)
  | .stop .. => [start]

theorem Program.finish_eq {Γ results start finish}
    (program : Program parties vocabulary capabilities scope Γ results start finish) :
    finish = start + program.sites.length := by
  induction program <;> simp_all [sites] <;> omega

theorem Program.sites_dense {Γ results start finish}
    (program : Program parties vocabulary capabilities scope Γ results start finish) :
    program.sites = List.range' start program.sites.length := by
  induction program <;>
    simp only [sites, List.length_nil, List.length_cons, List.length_append,
      List.range'_zero, List.range'_succ, List.cons.injEq, true_and]
  all_goals try rfl
  all_goals try assumption
  rename_i body next bodyIH nextIH
  rw [← List.range'_append]
  simpa only [Nat.one_mul, ← body.finish_eq] using
    congr (congrArg (fun a b : List Nat => a ++ b) bodyIH) nextIH

/-- A direct local-site requirement records the selected root tuple and the exact
registered pairs. In a template, roots name parameters; only a closed instance
can interpret them as concrete state identities. Indexed bodies contribute
once, independently of their iteration count. Callee obligations are discharged
in each stored callee instance; this list is not a transitive call summary. -/
structure RootRequirement where
  site : Nat
  roots : List Nat
  distinct : List (Nat × Nat)
  deriving DecidableEq, Repr

def RootRequirement.valid (requirement : RootRequirement) : Bool :=
  distinctRoots requirement.roots requirement.distinct

def Program.rootRequirements {Γ results start finish} :
    Program parties vocabulary capabilities scope Γ results start finish → List RootRequirement
  | .ret _ | .stop .. => []
  | .pure _ _ next | .query _ _ _ _ _ _ next | .guard _ _ _ next |
    .message _ _ _ _ _ _ _ next | .invoke _ _ _ _ next => next.rootRequirements
  | .local _ _ op bindings _ _ next =>
      ⟨start, bindings.roots, vocabulary.localDistinct op⟩ :: next.rootRequirements
  | .repeat _ _ _ body next => body.rootRequirements ++ next.rootRequirements

def Program.rootsValid {Γ results start finish}
    (program : Program parties vocabulary capabilities scope Γ results start finish) : Bool :=
  program.rootRequirements.all RootRequirement.valid

theorem Program.requirement_valid {Γ results start finish}
    (program : Program parties vocabulary capabilities scope Γ results start finish)
    (valid : program.rootsValid = true) {requirement : RootRequirement}
    (member : requirement ∈ program.rootRequirements) : requirement.valid = true :=
  List.all_eq_true.mp valid requirement member

end Zkc.Source.Mathematical.Protocol
