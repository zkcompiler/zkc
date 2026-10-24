module

public meta import ZkcSecurity.Tools.HonestAssembly
public import Zkc.Source.Structured.Algebra

@[expose] public section
set_option autoImplicit false
namespace TestsSecurity.HonestAssembly

private def Policy (count : Nat) := count ≤ 4 ∧ count < 64
private def Relation (left right : Nat) := left = right
private theorem policy_iff (count : Nat) : Policy count ↔ count ≤ 4 ∧ count < 64 := Iff.rfl
private theorem relation_iff (left right : Nat) (_bounded : left < 64) :
    Relation left right ↔ left = right := Iff.rfl

example (left right : Nat) (policy : Policy left) (related : Relation left right) :
    right < 64 ∧ left = right := by
  prepare_honest_readback using policy_iff and relation_iff
  exact ⟨by assumption, rfl⟩

private theorem missingPremise (left right : Nat) (_required : False) :
    Relation left right ↔ left = right := Iff.rfl

-- The input equation's extra premise must have a proof.
example (left right : Nat) (_policy : Policy left) (_related : Relation left right) : True := by
  fail_if_success prepare_honest_readback using policy_iff and missingPremise
  trivial

-- A theorem about another predicate cannot select the requested relation.
example (left right : Nat) (_policy : Policy left) (_related : Relation left right) : True := by
  fail_if_success prepare_honest_readback using policy_iff and (Iff.rfl : False ↔ False)
  trivial

-- Independent caller goals survive the preparation tactic.
example (left right : Nat) (_policy : Policy left) (_related : Relation left right) :
    (right < 64 ∧ left = right) ∧ True := by
  constructor
  · prepare_honest_readback using policy_iff and relation_iff
    exact ⟨by assumption, rfl⟩
  · trivial

private def carriers : Zkc.Source.Structured.Carriers :=
  Zkc.Source.Structured.uniformCarriers Nat Nat
private def CarrierPolicy (count : carriers.Value .index) := count ≤ 4 ∧ count < 64
private theorem carrierPolicy_iff (count : carriers.Value .index) :
    CarrierPolicy count ↔ count ≤ 4 ∧ count < 64 := Iff.rfl

-- Type projections in policy facts must be exposed for arithmetic consumers.
example (left right : Nat)
    (_policy : CarrierPolicy left) (_related : Relation left right) : right < 5 := by
  prepare_honest_readback using carrierPolicy_iff and relation_iff
  omega

end TestsSecurity.HonestAssembly
