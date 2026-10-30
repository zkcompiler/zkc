import ZkcSecurityExamples.Generated.SmallSumcheck
import ZkcSecurityExamples.Generated.TwoSums
import ZkcSecurity.Claims.DomainSoundness

/-! Charge admission and classification at actual generated source occurrences.
These checks do not replace either protocol's soundness theorem. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
noncomputable section
namespace TestsSecurity.DomainCharges
open Zkc.Source.Structured Zkc.Construction ZkcSecurity.Claims
open ZkcSecurity.Examples.Generated

def selected : Model := ⟨.adaptive, .symbolic "Q", "Q", "test", .constant 8, none⟩
def capabilities := ZkcSecurity.Domains.PrimeField.blsCapabilities TwoSums.original (by decide +kernel)
abbrev left := TwoSums.validatorSites[0]'(by decide)
abbrev right := TwoSums.validatorSites[1]'(by decide)

def occurrence (site : Domain.ChargeSite TwoSums.validatorCompiled) (coordinates : List Nat) :=
  Zkc.Construction.Domain.queryOrigin TwoSums.validatorCompiled.selection.context
    site.occurrence.suite site.occurrence.field site.occurrence.template coordinates

example : (occurrence left [0]).map left.matches = some true := by decide +kernel
example : (occurrence left [3]).map left.matches = some true := by decide +kernel
example : (occurrence right [0]).map right.matches = some true := by decide +kernel
example : (occurrence right [0]).map left.matches = some false := by decide +kernel
example : occurrence left [] = none := by decide +kernel
example : occurrence left [0, 1] = none := by decide +kernel
example : (occurrence left [0]).map (fun origin => left.matches { origin with entry := "foreign" }) =
    some false := by decide +kernel
example : (occurrence left [0]).map (fun origin => left.matches { origin with event := origin.event ++ ["junk"] }) =
    some false := by decide +kernel
example : (occurrence left [0]).map (fun origin => left.matches { origin with request := none }) =
    some false := by decide +kernel

example : (Domain.chargeSchedule capabilities TwoSums.validatorSubject selected
    [("left.challenge", .natural 1), ("right.challenge", .natural 2)]).map
      (fun result => result.toOption.isSome) = .ok true := by
  rfl

example : (Domain.chargeSchedule capabilities TwoSums.validatorSubject selected
    [("left.challenge", .natural 1), ("left.challenge", .natural 2)]).map
      (fun result => result.toOption.isNone) = .ok true := by
  rfl

def aliasSite : Domain.ChargeSite TwoSums.validatorCompiled := { left with label := "alias" }
def aliased : Domain.Subject ZkcSecurity.Domains.PrimeField.blsScalarModel TwoSums.validatorArtifacts :=
  { TwoSums.validatorSubject with sites := [left, aliasSite] }

-- Two labels for the same actual native occurrence cannot set distinct prices.
example : (Domain.chargeSchedule capabilities aliased selected
    [("left.challenge", .natural 1), ("alias", .natural 2)]).map
      (fun result => result.toOption.isNone) = .ok true := by
  rfl

def schedule : Domain.ChargeSchedule TwoSums.validatorSubject where
  entries := [(left, .constant 1), (right, .constant 2)]
  unique := by decide +kernel
  nativeUnique := by decide +kernel

def leftOrigin : Origin := (occurrence left [0]).get (by decide +kernel)
def rightOrigin : Origin := (occurrence right [0]).get (by decide +kernel)

example (queries : Nat) (history : Zkc.Construction.Domain.History
    ZkcSecurity.Domains.PrimeField.blsScalarModel.toCarriers) :
    schedule.charge queries history (.challenge leftOrigin) = (Bound.constant 1).value queries := by
  rfl
example (queries : Nat) (history : Zkc.Construction.Domain.History
    ZkcSecurity.Domains.PrimeField.blsScalarModel.toCarriers) :
    schedule.charge queries history (.challenge rightOrigin) = (Bound.constant 2).value queries := by
  rfl
example (queries : Nat) :
    schedule.charge queries [] (.challenge { leftOrigin with entry := "foreign" }) =
      schedule.maximum queries := by
  rfl

end TestsSecurity.DomainCharges
