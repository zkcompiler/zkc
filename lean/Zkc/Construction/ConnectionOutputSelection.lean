module

public import Zkc.Construction.ConnectionOutputs
public import Zkc.Construction.PairAcceptance
public import Zkc.Source.Structured.OutputSelection

@[expose] public section

/-! Full-row and source-selected Boolean consequences of CompleteReturns.
These are consumers of the fixed source output contract, never premises that
replace it. Probability and endpoint interpretations do not enter these laws.
-/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionOutputSelection
open Zkc.Source Zkc.Source.Structured Zkc.Construction

variable {carriers : Carriers}

/-- Encode all role-visible source outputs and the profile's exact history.
An absent or unencodable visible output remains a failure, not a dropped value. -/
def encodedValues (signature : ProtocolSignature) (context : Context) (role : Nat)
    (source : Values (Component carriers.Value) signature.outputs × Original.State carriers) :
    Option (Domain.Environment carriers) :=
  (Original.roleOutputValues role signature.outputScopes source.1).map
    (fun data => Domain.inputFrame context data source.2.history)

theorem encodedValues_agree {signature : ProtocolSignature} {context : Context}
    {role : Nat} {artifact : Participant}
    {source : Values (Component carriers.Value) signature.outputs × Original.State carriers}
    {target : Domain.Result carriers}
    (related : Original.CompleteReturns signature context role artifact source target) :
    encodedValues signature context role source = some target.values := by
  obtain ⟨data, encoded, returned⟩ := related.values
  simp only [encodedValues, encoded, Option.map_some, returned]

/-- Typed source selection commutes with the complete role encoder. This also
proves that the chosen position is a data position, before any final history. -/
theorem roleOutputValues_at (role : Nat) {types : List Ty} {ty : Ty}
    (scopes : List (List Nat)) (values : Values (Component carriers.Value) types)
    (output : Var types ty) (visible : inScope role scopes output = true)
    {data : Domain.Environment carriers}
    (encoded : Original.roleOutputValues role scopes values = some data) :
    ∃ value, values.get output = some value ∧ ∃ actual,
      Domain.Value.encode ty value = some actual ∧
      data[scopePosition role scopes output]? = some actual := by
  induction output generalizing scopes data with
  | here =>
    cases values with
    | cons value values =>
      cases scopes with
      | nil => simp [inScope] at visible
      | cons scope scopes =>
        have member : role ∈ scope := by simpa [inScope] using visible
        cases tail : Original.roleOutputValues role scopes values with
        | none => simp [Original.roleOutputValues, tail] at encoded
        | some rest =>
          cases value with
          | none => simp [Original.roleOutputValues, tail, member] at encoded
          | some value =>
            cases headEncoded : Domain.Value.encode _ value with
            | none => simp [Original.roleOutputValues, tail, member, headEncoded] at encoded
            | some actual =>
              have same : actual :: rest = data := by
                simpa [Original.roleOutputValues, tail, member, headEncoded] using encoded
              subst data
              exact ⟨value, rfl, actual, headEncoded, rfl⟩
  | @there types ty head output ih =>
    cases values with
    | cons value values =>
      cases scopes with
      | nil => simp [Original.roleOutputValues] at encoded
      | cons scope scopes =>
        cases tail : Original.roleOutputValues role scopes values with
        | none => simp [Original.roleOutputValues, tail] at encoded
        | some rest =>
          obtain ⟨accepted, selected, actual, actualEncoded, read⟩ := ih scopes values visible tail
          by_cases member : role ∈ scope
          · cases value with
            | none => simp [Original.roleOutputValues, tail, member] at encoded
            | some value =>
              cases headEncoded : Domain.Value.encode head value with
              | none => simp [Original.roleOutputValues, tail, member, headEncoded] at encoded
              | some actual =>
                have same : actual :: rest = data := by
                  simpa [Original.roleOutputValues, tail, member, headEncoded] using encoded
                subst data
                refine ⟨accepted, selected, _, actualEncoded, ?_⟩
                simpa [scopePosition, List.contains_iff_mem, member, Nat.one_add] using read
          · cases value with
            | some value => simp [Original.roleOutputValues, tail, member] at encoded
            | none =>
              have same : rest = data := by
                simpa [Original.roleOutputValues, tail, member] using encoded
              subst data
              refine ⟨accepted, selected, _, actualEncoded, ?_⟩
              simpa [scopePosition, List.contains_iff_mem, member] using read

theorem roleOutputValues_boolean (role : Nat) {types : List Ty}
    (scopes : List (List Nat)) (values : Values (Component carriers.Value) types)
    (output : Var types .boolean) (visible : inScope role scopes output = true)
    {data : Domain.Environment carriers}
    (encoded : Original.roleOutputValues role scopes values = some data) :
    ∃ accepted : Bool, values.get output = some accepted ∧
      data[scopePosition role scopes output]? = some (.data (.boolean accepted)) := by
  obtain ⟨accepted, selected, actual, actualEncoded, read⟩ :=
    roleOutputValues_at role scopes values output visible encoded
  have same : Domain.Value.data (.boolean accepted) = actual := by
    simpa [Domain.Value.encode, Domain.Payload.ofValue, Ty.isService] using actualEncoded
  exact ⟨accepted, selected, same.symm ▸ read⟩

/-- The source-selected Boolean agrees with the artifact's corresponding data
position. Every residual and the final history still belong to related. -/
theorem acceptance_agree {signature : ProtocolSignature} {context : Context}
    {role : Nat} {artifact : Participant}
    (output : Var signature.outputs .boolean)
    (visible : inScope role signature.outputScopes output = true)
    {source : Values (Component carriers.Value) signature.outputs × Original.State carriers}
    {target : Domain.Result carriers}
    (related : Original.CompleteReturns signature context role artifact source target) :
    source.1.get output =
      Domain.acceptanceAt (scopePosition role signature.outputScopes output) target.values := by
  obtain ⟨data, encoded, returned⟩ := related.values
  obtain ⟨accepted, selected, read⟩ := roleOutputValues_boolean role _ source.1 output visible encoded
  have bound : scopePosition role signature.outputScopes output < data.length :=
    List.getElem?_eq_some_iff.mp read |>.1
  rw [selected, returned]
  cases profile : context.profile <;>
    simp [Domain.acceptanceAt, Domain.inputFrame, profile, List.getElem?_append_left bound, read]

end Zkc.Construction.ConnectionOutputSelection
