module

public import Zkc.Source.Structured.DomainEvaluation
public import Zkc.Source.Component
public import Zkc.Claims.Registry

@[expose] public section

/-! Historical request-owned policy, retained only for migration tests.
The definitions below preserve the former registered rules and wire encoding.
Production admission uses retained source clauses and executable ABI bounds. -/

set_option autoImplicit false
namespace TestsSecurity.SourceAdmission.HistoricalPolicy
open Zkc.Source Zkc.Source.Structured
open Zkc.Claims

inductive InputRule (types : List Ty) where
  | boundedIndex (value : Var types .index) (maximum : Nat)
  | cubeTable {domain : String} (values : Var types (.vector domain))
      (rounds : Var types .index) (width : Nat)
  deriving Repr

/-- Every limit is part of the typed request. A root generator must select
its actual component maximum, rather than infer a limit from proof evidence. -/
structure InputPolicy (types : List Ty) where
  rules : List (InputRule types)
  deriving Repr

namespace InputRule
variable {types : List Ty} {carriers : Carriers}

def Holds (rule : InputRule types) (inputs : Values (Component carriers.Value) types) : Prop :=
  match rule with
  | .boundedIndex value maximum =>
      ∃ actual, inputs.get value = some actual ∧ actual ≤ maximum ∧ actual < indexLimit
  | .cubeTable values rounds width =>
      ∃ table dimension, inputs.get values = some table ∧ inputs.get rounds = some dimension ∧
        0 < width ∧ width < indexLimit ∧ dimension < indexLimit ∧
        table.length < indexLimit ∧ table.length = width * 2 ^ dimension

/-- Exact policy data for reports; positions and nominal domain identities
remain visible. This is presentation of fixed data, not a predicate parser. -/
def describe : InputRule types → String
  | .boundedIndex value maximum =>
      s!"input[{value.index}] <= {maximum}; input[{value.index}] < {indexLimit}"
  | .cubeTable (domain := domain) values rounds width =>
      s!"input[{values.index}]:Vector<{domain}> has length {width} * 2^input[{rounds.index}]; positive width and index limits"

def wire : InputRule types → Wire.Expr
  | .boundedIndex value maximum => .application "honest.bounded_index" (some 0)
      [(some "input", .natural value.index), (some "maximum", .natural maximum)]
  | .cubeTable (domain := domain) values rounds width => .application "honest.cube_table" (some 0)
      [(some "domain", .reference domain), (some "table", .natural values.index),
       (some "rounds", .natural rounds.index), (some "width", .natural width)]

def acceptsWire : InputRule types → Wire.Expr → Bool
  | .boundedIndex value maximum,
      .application "honest.bounded_index" (some 0)
        [(some "input", .natural position), (some "maximum", .natural bound)] =>
      position == value.index && bound == maximum
  | .cubeTable (domain := domain) values rounds width,
      .application "honest.cube_table" (some 0)
        [(some "domain", .reference field), (some "table", .natural table),
         (some "rounds", .natural dimension), (some "width", .natural columns)] =>
      field == domain && table == values.index && dimension == rounds.index && columns == width
  | _, _ => false

theorem acceptsWire_wire (rule : InputRule types) : rule.acceptsWire rule.wire = true := by
  cases rule <;> simp [acceptsWire, wire]

theorem wire_eq_of_accepted (rule : InputRule types) (expression : Wire.Expr)
    (accepted : rule.acceptsWire expression = true) : expression = rule.wire := by
  cases rule <;> simp only [acceptsWire] at accepted
  all_goals split at accepted <;> simp_all [wire, Bool.and_eq_true, beq_iff_eq]
  obtain ⟨rfl, same, rfl, rfl⟩ := ‹_ ∧ HEq _ _ ∧ _ ∧ _›
  cases same
  rfl
end InputRule

def InputPolicy.Holds {types : List Ty} {carriers : Carriers}
    (policy : InputPolicy types) (inputs : Values (Component carriers.Value) types) : Prop :=
  ∀ rule ∈ policy.rules, rule.Holds inputs

def InputPolicy.description {types : List Ty} (policy : InputPolicy types) : List String :=
  policy.rules.map InputRule.describe

def matchPolicyRules {types : List Ty} : List (InputRule types) → List Wire.Expr → Bool
  | [], [] => true
  | rule :: rules, expression :: expressions => rule.acceptsWire expression && matchPolicyRules rules expressions
  | _, _ => false

theorem policyRules_eq_of_accepted {types : List Ty} (rules : List (InputRule types))
    (expressions : List Wire.Expr) (accepted : matchPolicyRules rules expressions = true) :
    expressions = rules.map InputRule.wire := by
  induction rules generalizing expressions with
  | nil => cases expressions <;> simp_all [matchPolicyRules]
  | cons rule rules ih =>
      cases expressions with
      | nil => cases accepted
      | cons expression expressions =>
          simp only [matchPolicyRules, Bool.and_eq_true] at accepted
          obtain ⟨head, tail⟩ := accepted
          rw [InputRule.wire_eq_of_accepted rule expression head, ih expressions tail]
          rfl

/-- A nonempty policy is an exact versioned property parameter. Empty policies
use the absent parameter; duplicate, reordered or unknown entries refuse. -/
def InputPolicy.parameters {types : List Ty} (policy : InputPolicy types) : Option Wire.Expr :=
  if policy.rules.isEmpty then none else
    some (.application "honest.input_policy" (some 0) [(some "rules", .list (policy.rules.map InputRule.wire))])

def InputPolicy.matchesParameters {types : List Ty} (policy : InputPolicy types) : Option Wire.Expr → Bool
  | none => policy.rules.isEmpty
  | some (.application "honest.input_policy" (some 0) [(some "rules", .list rules)]) =>
      !policy.rules.isEmpty && matchPolicyRules policy.rules rules
  | _ => false

def InputPolicy.checkParameters {types : List Ty} (policy : InputPolicy types)
    (parameters : Option Wire.Expr) : Except ResolutionError Unit :=
  if policy.matchesParameters parameters then .ok ()
  else .error (.schema "honest input policy does not match the typed request")

theorem InputPolicy.parameters_eq_of_checked {types : List Ty} (policy : InputPolicy types)
    (parameters : Option Wire.Expr) (checked : policy.checkParameters parameters = .ok ()) :
    parameters = policy.parameters := by
  have accepted : policy.matchesParameters parameters = true := by
    unfold checkParameters at checked
    split at checked <;> simp_all
  cases parameters with
  | none =>
      have empty : policy.rules = [] := List.isEmpty_iff.mp accepted
      simp [InputPolicy.parameters, empty]
  | some expression =>
      simp only [matchesParameters] at accepted
      split at accepted <;> simp_all [Bool.and_eq_true]
      obtain ⟨nonempty, rules⟩ := accepted
      have encoded := policyRules_eq_of_accepted _ _ rules
      simp_all [InputPolicy.parameters]

theorem InputPolicy.parameters_checked {types : List Ty} (policy : InputPolicy types) :
    policy.checkParameters policy.parameters = .ok () := by
  have matching (rules : List (InputRule types)) : matchPolicyRules rules (rules.map InputRule.wire) = true := by
    induction rules with
    | nil => rfl
    | cons rule rules ih => simp only [List.map_cons, matchPolicyRules, InputRule.acceptsWire_wire, ih, Bool.and_self]
  cases policy with
  | mk rules =>
      cases rules with
      | nil => rfl
      | cons head tail =>
          change (if matchPolicyRules (head :: tail) ((head :: tail).map InputRule.wire) then
            Except.ok () else Except.error _) = .ok ()
          rw [matching]
          rfl

end TestsSecurity.SourceAdmission.HistoricalPolicy
