module

public import Zkc.Protocol.Obligations.Bounded
public import Zkc.IR.Claims.Capability

public section

/-! Capability export of the bounded charged reading. The reading, its reduction
and the endpoint certificate are owned by `Zkc.Protocol.Obligations.Bounded`;
this module adds only the claim capability, which needs the IR claim vocabulary.
-/

set_option autoImplicit false
namespace ZkcSecurity.Obligations
open OracleComp OracleSpec Zkc.Transcript Zkc.Obligations
open ZkcSecurity.FiatShamir.Typed

variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type}
  [∀ event, SampleableType (Raw event)]

/-- A separate capability export over a fixed history/process meaning.
The postcondition (including residual No/frame links) and exact occurrence
charge are parameters. Canonical subject association is a caller obligation. -/
@[expose] def chargedCapability (absorb : Interface I E P Raw) (Post : List E → A → Prop)
    (charge : List E → E → ENNReal) : Zkc.Claims.Capability (List E × PIR.Process I A) where
  Payload := Reduction absorb Post charge
  Valid contract meaning := contract.doomed meaning.1 meaning.2

def exportCapability {absorb : Interface I E P Raw} {Post : List E → A → Prop}
    {charge : List E → E → ENNReal} {history : List E} {actual : PIR.Process I A}
    (derivation : Derivation absorb (boundedEscape charge) Post history actual) :
    (chargedCapability absorb Post charge).Export (history, actual) :=
  ⟨reduction absorb Post charge, derived_doomed derivation⟩

end ZkcSecurity.Obligations
