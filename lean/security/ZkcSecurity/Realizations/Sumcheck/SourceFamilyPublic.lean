module

public import ZkcSecurity.Realizations.Sumcheck.SourceFamilyComposition
public import ZkcSecurity.Source.PublicProperties

@[expose] public section

/-! Public query cuts and reached-history sampling for any installed source
family. The distribution law is explicit at every routed nominal origin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceFamilyPublic
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration SourceFamily
open ZkcSecurity.FiatShamir ZkcSecurity.Source OracleComp OracleSpec
variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance fieldStructure : Field (model.Field field) := fieldLaw.out.toField

def cuts (ctx : ProtocolContext) (handle : Nat) :
    SourceRound.Cuts model PublicProperties.interface ctx handle where
  low := .message (SumcheckRoundNormalForms.round0Site ctx) (ctx.roles 0)
  recoverLow := PublicProperties.recovered (.field field)
  receiveLow := rfl
  high := .message (SumcheckRoundNormalForms.round1Site ctx) (ctx.roles 0)
  recoverHigh := PublicProperties.recovered (.field field)
  receiveHigh := rfl
  query := .challenge (SumcheckRoundNormalForms.challengeSite ctx) field handle
  decode := some
  draw := rfl
  delivery r := .message (SumcheckRoundNormalForms.deliverySite ctx) (ctx.roles 0) (.field field r)
  send _ := rfl

def boundaries (ctx : ProtocolContext) : Boundaries model PublicProperties.interface ctx where
  enter index := .enter ⟨repeatSite ctx, index⟩
  leave index := .leave ⟨repeatSite ctx, index⟩
  entered _ := rfl
  left _ := rfl

variable [samples : ∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event)]
  (price : ENNReal)

omit fieldLaw in
theorem escape_empty (history : List (PublicProperties.Event model.toCarriers))
    (event : PublicProperties.Event model.toCarriers) :
    PublicProperties.escape price history event (fun _ => False) := by
  cases event <;> try trivial
  intro origin request
  simp

variable (sampling : ∀ (origin : Zkc.Construction.Origin)
    (request : origin.request = some (.draw field)) (p q : Polynomial (model.Field field)),
    p ≠ q → p.natDegree ≤ 1 → q.natDegree ≤ 1 →
    Pr{let raw ← $ᵗ (Domain.Raw (.challenge origin : Domain.Event model.toCarriers))}[
      p.eval (Zkc.Construction.Original.fieldReply origin field request raw) =
        q.eval (Zkc.Construction.Original.fieldReply origin field request raw)] ≤ price)

/-- Degree, mismatch and adversarial endpoint fixation come from the shared
representation. Sampling at the actual nominal request is explicit. -/
def no_steps {program : Zkc.Source.Structured.Program} (installation : SourceFamily.Installation program) (site : String) (handle : Nat)
    (original : List (model.Field field)) :
    RepeatedComponent.NoContract
      (component model program.payload.definitions (Occurrence.table model program.payload)
        (context site) handle) PublicProperties.interface (PublicProperties.escape price) (no model original ()) := by
  apply no_contract model _ program.payload.linked installation.roundBodies
    (Occurrence.table model program.payload) (context site) (context_distinct site) handle original ()
    PublicProperties.interface (PublicProperties.escape price) (cuts model (context site) handle)
    (boundaries model (context site))
  intro reached n reference wrong packetLo lo recoveredLo packetHi hi recoveredHi checked origin request
  have bounded := sampling origin request _ _
    (checked_polynomial_ne TableReference.laws Message.endpoints_laws
      ((layout model).representation.state reference) trivial reference.scalar wrong.2 (lo,hi) checked.symm)
    (Message.endpoints_laws.degree_le (lo,hi)) (TableReference.laws.degree_le _ trivial)
  simpa only [cuts, Option.some.injEq, exists_eq_left'] using bounded

end ZkcSecurity.Realizations.Sumcheck.SourceFamilyPublic
