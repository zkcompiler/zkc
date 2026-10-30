module

public import Zkc.Source.Structured.DomainLaws
public import Zkc.Construction.DomainTranscript
public import VCVio.OracleComp.Constructions.SampleableType

@[expose] public section

/-! Algebraic, finite-carrier and sampling capabilities of an admitted domain
model. Registry and schema selection belong to Claims. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims.Domain
open Zkc.Source.Structured

structure Capabilities (model : DomainModel) (snapshot : Snapshot) where
  algebra : DomainLaws snapshot.catalogue model
  characteristic : CharacteristicLaws snapshot.catalogue model.toFieldModel
  finite : ∀ identity, snapshot.catalogue.identitySort identity = some .field →
    Fintype (model.Field identity)
  samples : ∀ event : Zkc.Construction.Domain.Event model.toCarriers,
    SampleableType (Zkc.Construction.Domain.Raw event)

end ZkcSecurity.Claims.Domain
