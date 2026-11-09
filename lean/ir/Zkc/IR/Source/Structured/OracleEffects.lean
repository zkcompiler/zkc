module

public import Zkc.IR.Source.Structured.OracleValues
public import Zkc.Program.Source.Participant
public import Zkc.Program.Semantics.SignatureSum

@[expose] public section

/-! Ordinary participant actions and an independently supplied oracle signature use the same
`PIR.Process`. Concrete data demand is explicit; this module defines no oracle store, virtual
body semantics, service identities, admission rule, or alternative evaluator. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

namespace OracleEffects

abbrev ordinaryInterface (carriers : Carriers)
    (services : Participant.Services Ty) : PIR.Signature :=
  Participant.interface Nat Ty services (ProtocolValue carriers)

/-- The parent supplies its checked dependent oracle request signature. Services keep their
existing single-result contract and are independent of logical table operations. -/
abbrev interface (carriers : Carriers) (services : Participant.Services Ty)
    (oracle : PIR.Signature) : PIR.Signature :=
  PIR.Signature.sum (ordinaryInterface carriers services) oracle

def ordinaryActions {carriers : Carriers} {services : Participant.Services Ty}
    {oracle : PIR.Signature} : PIR.OperationInterpretation
    (ordinaryInterface carriers services) (interface carriers services oracle) :=
  PIR.Signature.injectLeft

def oracleActions {carriers : Carriers} {services : Participant.Services Ty}
    {oracle : PIR.Signature} : PIR.OperationInterpretation oracle
    (interface carriers services oracle) := PIR.Signature.injectRight

@[simp] theorem ordinaryActions_interpret {carriers : Carriers}
    {services : Participant.Services Ty} {oracle target : PIR.Signature} {A : Type}
    (ordinary : PIR.OperationInterpretation (ordinaryInterface carriers services) target)
    (logical : PIR.OperationInterpretation oracle target)
    (source : PIR.Process (ordinaryInterface carriers services) A) :
    (source.interpret (ordinaryActions (oracle := oracle))).interpret
      (PIR.Signature.interpretSum ordinary logical) = source.interpret ordinary :=
  PIR.Signature.interpret_injectLeft ordinary logical source

end OracleEffects

/-- A demand retains its requester and exact paired view. Holder authorization, source/store
association, shape checks, observation policy, and invalid virtual contents belong to the
supplied handler. Constructing a request asserts none of those properties. -/
structure OracleDataDemand where
  requester : Nat
  sort : OracleLogicalSort
  view : OracleDataView sort

abbrev oracleDataDemandInterface (carriers : Carriers) : PIR.Signature where
  Op := OracleDataDemand
  Reply request := carriers.Value request.sort.dataType

abbrev OracleDataDemandInterpretation (carriers : Carriers) (interface : PIR.Signature) :=
  PIR.OperationInterpretation (oracleDataDemandInterface carriers) interface

namespace ProtocolValue

mutual
  /-- Explicitly demand this operand in field/element order. Project or select the actually
  required operands before calling this function. In particular it is not a pure Math calculation
  or a replacement for exact optional-dependency summaries. There is no default demand handler. -/
  def materializeWith {carriers : Carriers} {interface : PIR.Signature}
      (demand : OracleDataDemandInterpretation carriers interface) (self : Nat) :
      {type : Ty} → ProtocolValue carriers type → PIR.Process interface (carriers.Value type)
    | _, .concrete _ value => .done value
    | _, .deferred view => demand ⟨self, _, view⟩
    | _, .product _ _ fields values => materializeFieldsWith demand self fields values
    | _, .sequence _ values => materializeSequenceWith demand self values

  def materializeFieldsWith {carriers : Carriers} {interface : PIR.Signature}
      (demand : OracleDataDemandInterpretation carriers interface) (self : Nat) :
      (fields : ProductFields) → Values (ProtocolValue carriers) fields.toList →
        PIR.Process interface (carriers.ProductValue fields)
    | .nil, .nil => .done ()
    | .cons _ rest, .cons value values =>
        (materializeWith demand self value).bind fun head ↦
          (materializeFieldsWith demand self rest values).bind fun tail ↦ .done (head, tail)

  def materializeSequenceWith {carriers : Carriers} {interface : PIR.Signature}
      (demand : OracleDataDemandInterpretation carriers interface) (self : Nat) :
      {element : Ty} → ProtocolSequence carriers element →
        PIR.Process interface (List (carriers.Value element))
    | _, .nil => .done []
    | _, .cons value values =>
        (materializeWith demand self value).bind fun head ↦
          (materializeSequenceWith demand self values).bind fun tail ↦ .done (head :: tail)
end

@[simp] theorem materializeWith_concrete {carriers : Carriers} {interface : PIR.Signature}
    (demand : OracleDataDemandInterpretation carriers interface) (self : Nat) {type : Ty}
    (atomic : type.isAggregate = false) (value : carriers.Value type) :
    materializeWith demand self (.concrete atomic value) = .done value := by
  rw [materializeWith]

@[simp] theorem materializeWith_product {carriers : Carriers} {interface : PIR.Signature}
    (demand : OracleDataDemandInterpretation carriers interface) (self : Nat)
    (identity constructor : String) (fields : ProductFields)
    (values : Values (ProtocolValue carriers) fields.toList) :
    materializeWith demand self (.product identity constructor fields values) =
      materializeFieldsWith demand self fields values := by rw [materializeWith]

@[simp] theorem materializeWith_sequence {carriers : Carriers} {interface : PIR.Signature}
    (demand : OracleDataDemandInterpretation carriers interface) (self : Nat) (element : Ty)
    (values : ProtocolSequence carriers element) :
    materializeWith demand self (.sequence element values) =
      materializeSequenceWith demand self values := by rw [materializeWith]

@[simp] theorem materializeWith_deferred {carriers : Carriers} {interface : PIR.Signature}
    (demand : OracleDataDemandInterpretation carriers interface) (self : Nat)
    {sort : OracleLogicalSort} (view : OracleDataView sort) :
    materializeWith demand self (.deferred view) = demand ⟨self, sort, view⟩ := by
  rw [materializeWith]

mutual
  @[simp] theorem materializeWith_ofConcrete {carriers : Carriers} {interface : PIR.Signature}
      (demand : OracleDataDemandInterpretation carriers interface) (self : Nat) (type : Ty)
      (value : carriers.Value type) :
      materializeWith demand self (ofConcrete type value) = .done value := by
    cases type with
    | sequence element =>
      simpa only [ofConcrete, materializeWith] using
        materializeSequenceWith_ofConcreteSequence demand self element value
    | product identity constructor fields =>
      simpa only [ofConcrete, materializeWith] using
        materializeFieldsWith_ofConcreteFields demand self fields value
    | _ => simp only [ofConcrete]; exact materializeWith_concrete demand self _ _
  termination_by (sizeOf type, 0)
  decreasing_by all_goals subst_vars; simp_wf; omega

  theorem materializeFieldsWith_ofConcreteFields {carriers : Carriers} {interface : PIR.Signature}
      (demand : OracleDataDemandInterpretation carriers interface) (self : Nat)
      (fields : ProductFields) (values : carriers.ProductValue fields) :
      materializeFieldsWith demand self fields (ofConcreteFields fields values) = .done values := by
    cases fields with
    | nil => cases values; simp [ofConcreteFields, materializeFieldsWith]
    | cons type rest =>
      rcases values with ⟨value, values⟩
      simp only [ofConcreteFields, materializeFieldsWith,
        materializeWith_ofConcrete demand self type value,
        materializeFieldsWith_ofConcreteFields demand self rest values, PIR.Process.bind]
  termination_by (sizeOf fields, 0)
  decreasing_by all_goals subst_vars; simp_wf; omega

  theorem materializeSequenceWith_ofConcreteSequence {carriers : Carriers}
      {interface : PIR.Signature} (demand : OracleDataDemandInterpretation carriers interface)
      (self : Nat) (element : Ty) (values : List (carriers.Value element)) :
      materializeSequenceWith demand self (ofConcreteSequence element values) = .done values := by
    cases values with
    | nil => simp [ofConcreteSequence, materializeSequenceWith]
    | cons value values =>
      simp only [ofConcreteSequence, materializeSequenceWith,
        materializeWith_ofConcrete demand self element value,
        materializeSequenceWith_ofConcreteSequence demand self element values, PIR.Process.bind]
  termination_by (sizeOf element, values.length + 1)
  decreasing_by all_goals subst_vars; simp_wf; omega
end

mutual
  /-- Interpreting the explicit demand boundary composes on every value, without an honest-data
  or admissibility premise. The existing Process execution laws retain all stops and post-states. -/
  theorem materializeWith_interpret {carriers : Carriers} {interface target : PIR.Signature}
      (demand : OracleDataDemandInterpretation carriers interface) (self : Nat)
      {type : Ty} (value : ProtocolValue carriers type)
      (operations : PIR.OperationInterpretation interface target) :
      (materializeWith demand self value).interpret operations =
        materializeWith (fun request ↦ (demand request).interpret operations) self value := by
    cases value with
    | concrete atomic value =>
      simp only [materializeWith_concrete, PIR.Process.interpret]
    | deferred view => simp only [materializeWith_deferred]
    | product identity constructor fields values =>
      simpa only [materializeWith] using
        materializeFieldsWith_interpret demand self fields values operations
    | sequence element values =>
      simpa only [materializeWith] using
        materializeSequenceWith_interpret demand self values operations
  termination_by (sizeOf type, 0)
  decreasing_by all_goals subst_vars; simp_wf; omega

  theorem materializeFieldsWith_interpret {carriers : Carriers}
      {interface target : PIR.Signature}
      (demand : OracleDataDemandInterpretation carriers interface)
      (self : Nat) (fields : ProductFields) (values : Values (ProtocolValue carriers) fields.toList)
      (operations : PIR.OperationInterpretation interface target) :
      (materializeFieldsWith demand self fields values).interpret operations =
        materializeFieldsWith (fun request ↦ (demand request).interpret operations)
          self fields values := by
    cases fields with
    | nil => cases values; simp only [materializeFieldsWith, PIR.Process.interpret]
    | cons type rest =>
      cases values with
      | cons value values =>
        simp only [materializeFieldsWith, PIR.Process.interpret_bind,
          materializeWith_interpret demand self value operations,
          materializeFieldsWith_interpret demand self rest values operations, PIR.Process.interpret]
  termination_by (sizeOf fields, 0)
  decreasing_by all_goals subst_vars; simp_wf; omega

  theorem materializeSequenceWith_interpret {carriers : Carriers}
      {interface target : PIR.Signature}
      (demand : OracleDataDemandInterpretation carriers interface)
      (self : Nat) {element : Ty} (values : ProtocolSequence carriers element)
      (operations : PIR.OperationInterpretation interface target) :
      (materializeSequenceWith demand self values).interpret operations =
        materializeSequenceWith (fun request ↦ (demand request).interpret operations)
          self values := by
    induction values using ProtocolSequence.induction with
    | nil => simp only [materializeSequenceWith, PIR.Process.interpret]
    | cons value values ih =>
      simp only [materializeSequenceWith, PIR.Process.interpret_bind,
        materializeWith_interpret demand self value operations, ih, PIR.Process.interpret]
  termination_by (sizeOf element, 1)
  decreasing_by omega
end

end ProtocolValue
end Zkc.Source.Structured
