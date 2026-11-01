import ZkcSecurityExamples.Gkr.CanonicalPolicy
import ZkcSecurityExamples.Gkr.CanonicalReading

/-! The production named ABI retains complete optional rows and the original
ordered constructors. Malformed statements need no admission hypothesis. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.NamedRootABI
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Realizations.Gkr

example (record : Generated.ABI.DataFields) :
    Generated.ABI.fields (Generated.ABI.fromFields record) = record :=
  Generated.ABI.fields_fromFields record

example (values : Generated.ABI.Data) :
    Generated.ABI.fromFields (Generated.ABI.fields values) = values :=
  Generated.ABI.fromFields_fields values

example (record : Generated.ABI.DataFields) :
    Generated.ABI.abi.complete (Generated.ABI.abi.pack (Generated.ABI.fromFields record)) =
      some (Generated.ABI.fromFields record) :=
  (Generated.ABI.abi.complete_iff _ _).mpr rfl

example (record : Generated.ABI.DataFields) (service : Option Nat) :
    (Generated.ABI.fields (Generated.ABI.fromFields { record with handle := service })).handle =
      service := rfl

example (record : Generated.ABI.RawInputs) :
    Generated.ABI.SourceView.unpack (Generated.ABI.SourceView.pack record) = record :=
  Generated.ABI.SourceView.unpack_pack record

example (model : DomainModel)
    (returned : Values (Component model.Value) Canonical.imported.program.payload.entry.outputs) :
    Canonical.OutputView.pack (Canonical.OutputView.unpack returned) = returned :=
  Canonical.OutputView.pack_unpack returned

example : (Canonical.OutputView.unpack
    (Canonical.OutputView.pack (Value := Component (fun _ : Ty => Nat))
      { accepted := none })).accepted = none := rfl

/-- Exact equality controls against the former positional source constructors. -/
example (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain)) :
    Canonical.sourceInputs model runtime =
      .cons (some runtime.inputs) (.cons (some runtime.outputs) (.cons (some runtime.add)
        (.cons (some runtime.mul) (.cons (some runtime.layers) (.cons (some runtime.selector)
          (.cons (some runtime.width) (.cons (some runtime.handle) .nil))))))) := rfl

example (model : DomainModel) (runtime : Source.Invocation (model.Field scalarDomain)) :
    Canonical.statement model runtime =
      .cons runtime.inputs (.cons runtime.outputs (.cons runtime.add (.cons runtime.mul
        (.cons runtime.layers (.cons runtime.selector (.cons runtime.width .nil)))))) := rfl

example {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
    (returned : CanonicalReading.Result F G) :
    CanonicalReading.acceptance returned = returned.1.get .here := rfl

example (statement : Generated.Subject.validatorArtifacts.Statement Generated.ABI.model)
    (handle : Nat) (witness : Generated.Subject.validatorSubject.Witness) :
    Generated.Subject.validatorSubject.Holds statement witness ↔
      (Canonical.invocation Generated.ABI.model statement handle).Correct :=
  Canonical.holds_all Generated.ABI.model statement handle witness

def malformed : Generated.ABI.StatementData :=
  { inputs := [], outputs := [0], add := [0], mul := [0],
    layers := 0, selector := 0, width := 0 }

example (handle : Nat) :
    Canonical.statement Generated.ABI.model
      (Canonical.invocation Generated.ABI.model (Generated.ABI.statementOfData malformed) handle) =
        Generated.ABI.statementOfData malformed :=
  Canonical.statement_invocation _ _ handle

example (handle : Nat) (witness : Generated.Subject.validatorSubject.Witness) :
    ¬ Generated.Subject.validatorSubject.Holds (Generated.ABI.statementOfData malformed) witness := by
  intro holds
  have correct := (Canonical.holds_all Generated.ABI.model _ handle witness).mp holds
  have impossible : (0 : Nat) = 1 := correct.1.1
  cases impossible

/-- Matching vector carriers cannot validate a swapped field projection. -/
example : True := by
  fail_if_success
    have wrong : (Generated.ABI.fields (Generated.ABI.fromFields
        { inputs := [0], outputs := [1], add := [], mul := [],
          layers := 0, selector := 0, width := 0, handle := none })).inputs = [1] := rfl
  trivial

#print axioms Canonical.relation_exact
#print axioms Canonical.input_clause_exact
#print axioms Canonical.holds_all
#print axioms Generated.ABI.fromFields_fields
end TestsSecurity.NamedRootABI
