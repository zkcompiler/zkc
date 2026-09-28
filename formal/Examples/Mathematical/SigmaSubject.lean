import Zkc.Source.Mathematical.BlsAdmission

/-! The canonical mathematical subject captured from `sigma.pir`.

The consumer test compares its complete canonical encoding with fresh frontend
output. The protocol used by proofs comes from admitting this subject; no
separate handwritten intrinsic program supplies the semantics.
-/

set_option autoImplicit false
namespace Examples.Mathematical.SigmaSubject
open Zkc.Source.Mathematical BlsInstallation

private def use (index : Nat) : Raw.TypeUse := ⟨⟨index⟩, []⟩
private def values {kind : Raw.ReferenceKind} (indices : List Nat) : List (Raw.Reference kind) :=
  indices.map (⟨·⟩)
private def call (operation : Nat) (inputs : List Nat) : Raw.Node :=
  .operation ⟨operation⟩ [] (.object []) (values inputs)
private def region (captures : List Nat) (nodes : List Raw.Node) (outputs : List Nat) : Raw.Step :=
  .pure ⟨values captures, nodes, values outputs⟩
private def permission (index role : Nat) : Raw.Permission := ⟨⟨⟨index⟩, []⟩, [⟨role⟩]⟩
private def operation (index : Nat) (inputs : List Nat) (output : Nat) : Raw.Operation :=
  ⟨⟨index⟩, 0, [], inputs.map use, use output, .total, []⟩

def commitmentRegion : Raw.Region := ⟨values [2, 0], [call 0 [0, 1]], values [0]⟩

def definition : Raw.Definition where
  statics := 0
  roles := 2
  capabilities := [permission 0 0, permission 1 1]
  arguments := [⟨[⟨0⟩], use 1⟩, ⟨[⟨0⟩, ⟨1⟩], use 2⟩, ⟨[⟨0⟩, ⟨1⟩], use 2⟩]
  results := []
  relations := []
  body := .mk [
    .query 0 ⟨0⟩ ⟨0⟩ [],
    .pure commitmentRegion,
    .message 1 ⟨0⟩ [] ⟨0⟩ ⟨1⟩ ⟨0⟩,
    .query 2 ⟨1⟩ ⟨1⟩ [],
    .message 3 ⟨1⟩ [] ⟨1⟩ ⟨0⟩ ⟨0⟩,
    region [0, 5, 4] [call 1 [0], call 2 [0, 2], call 3 [4, 0]] [2, 1, 0],
    .message 4 ⟨2⟩ [] ⟨0⟩ ⟨1⟩ ⟨2⟩,
    region [5, 10, 0, 11, 6]
      [call 1 [0], call 0 [2, 3], call 0 [5, 1], call 4 [7, 0], call 5 [2, 0]] [4, 3, 2, 1, 0],
    .guard 5 ⟨1⟩ ⟨4⟩] (.ret [])

def subject : Raw.Subject where
  manifest := {
    domains := [Domain.scalar.identity, Domain.group.identity]
    operations := [Operation.scale.identity, Operation.fromNonzero.identity, Operation.fieldMul.identity,
      Operation.fieldAdd.identity, Operation.groupAdd.identity, Operation.equal.identity]
    wires := [LogicalType.scalar.wireIdentity, LogicalType.group.wireIdentity,
      LogicalType.nonzero.wireIdentity, LogicalType.boolean.wireIdentity]
    services := [Service.draw.identity, Service.drawNonzero.identity]
    laws := [] }
  module := {
    roles := ["Prover", "Verifier"]
    types := [⟨0, .fin (.literal 2)⟩, ⟨0, .nominal ⟨0⟩ "field" []⟩,
      ⟨0, .nominal ⟨1⟩ "group" []⟩, ⟨0, .nominal ⟨0⟩ "nonzero_field" []⟩]
    operations := [operation 0 [2, 1] 2, operation 1 [3] 1,
      operation 2 [1, 1] 1, operation 3 [1, 1] 1,
      operation 4 [2, 2] 2, operation 5 [2, 2] 0]
    wires := [⟨⟨1⟩, 0, use 2⟩, ⟨⟨2⟩, 0, use 3⟩, ⟨⟨0⟩, 0, use 1⟩]
    capabilityTypes := [⟨⟨0⟩, 0, [], use 1⟩, ⟨⟨1⟩, 0, [], use 3⟩]
    roots := [permission 0 0, permission 1 1]
    relations := []
    definitions := [definition]
    entry := ⟨⟨0⟩, [], [⟨0⟩, ⟨1⟩], [⟨0⟩, ⟨1⟩]⟩ }

def admission := BlsAdmission.admit subject 10000000

/-- Consumers pass the certificate returned by admission of this exact subject.
The intrinsic program is extracted from that certificate's actual assembly. -/
def closed (admitted : SubjectAdmission.Admitted BlsAdmission.installed subject) :=
  ClosedAssembly.Result.closed admitted.header admitted.assembly

section Semantics
open Zkc.Source Zkc.Algebra.Bls12381
variable [Fact baseModulus.Prime]

/-- The actual canonical source's stored entry, interpreted on the installed
BLS carriers. Base-field primality and an admission certificate are explicit
premises. The model generator selects the installed generator operation's
value; Sigma uses its own generator input at entry argument 1. -/
noncomputable def openMeaning (generator : G1)
    (admitted : SubjectAdmission.Admitted BlsAdmission.installed subject) (self : Nat)
    (arguments : Values (Component (BlsAdmission.interpretation generator admitted).Value self)
      (closed admitted).entry.signature.arguments) :=
  (closed admitted).denote (BlsAdmission.interpretation generator admitted) self arguments

end Semantics

end Examples.Mathematical.SigmaSubject
