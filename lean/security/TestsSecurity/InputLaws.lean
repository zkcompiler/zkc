module

public meta import ZkcSecurityTools.InputLaws
public meta import ZkcSecurityTools.TableCapacity
public import Zkc.Source.Structured.Algebra

@[expose] public section
set_option autoImplicit false
namespace TestsSecurity.InputLaws

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

end TestsSecurity.InputLaws

namespace TestsSecurity.InputLaws

private def Selected (a b : Nat) : Prop := a = b
private theorem selected_iff (a b : Nat) (_bounded : a < 8) : Selected a b ↔ a = b := Iff.rfl
private theorem unavailable_iff (a b : Nat) (_required : False) : Selected a b ↔ a = b := Iff.rfl

example (a b : Nat) (bound : a ≤ 4) (selected : Selected a b) : b ≤ 4 ∧ True := by
  constructor
  · apply_input_law selected_iff solving omega
    omega
  · trivial

-- A callback cannot leave a premise open, even if the main result is trivial.
example (a b : Nat) (_selected : Selected a b) : True := by
  fail_if_success apply_input_law unavailable_iff solving skip
  fail_if_success apply_input_law unavailable_iff solving assumption
  trivial

open Zkc.Source.Structured

example (_raw : List Nat) (count : Nat) (_allowed : count ≤ 4)
    (_shape : _raw.length = 2 ^ count) : _raw.length < indexLimit ∧ True := by
  constructor
  · prove_table_capacity
  · trivial

example (_raw : List Nat) (count : Nat) (_allowed : count ≤ 4) : True := by
  fail_if_success have bounded : _raw.length < indexLimit := by prove_table_capacity
  trivial

example (_raw : List Nat) (count : Nat) (_shape : _raw.length = 2 ^ count) : True := by
  fail_if_success have bounded : _raw.length < indexLimit := by prove_table_capacity
  trivial

-- A large source guard does not establish capacity merely by existing.
example (_raw : List Nat) (count : Nat) (_allowed : count ≤ 64)
    (_shape : _raw.length = 2 ^ count) : True := by
  fail_if_success have bounded : _raw.length < indexLimit := by prove_table_capacity
  trivial

end TestsSecurity.InputLaws
