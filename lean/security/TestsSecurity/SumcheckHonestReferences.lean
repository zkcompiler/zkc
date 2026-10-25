import TestsSecurity.SumcheckConsumers

/-! Actual-reference honest execution regressions, adapted from the checked
independent component review probes. These exercise the library handler
consumer; compiled-pair root theorems require separate source bindings. -/

set_option autoImplicit false
noncomputable section
namespace TestsSecurity.SumcheckHonestReferences
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Families.Sumcheck.Consumers
open TestsSecurity.SumcheckConsumers Zkc.Polynomial.Multilinear

variable {F : Type} [Field F]

/-- A real handler stores the mathematical object, emits its current honest
    message, and restricts it at the actual query reply. -/
def handler (reference : Reference F) (message : Message F)
    (encode : {n : Nat} → reference.State (n + 1) → message.Carrier) (r : F) :
    PIR.Handler (signature F message.Carrier) (Sigma reference.State) (Event message.Carrier)
  | .receive context remaining, h => match h with
      | ⟨0, _⟩ => ⟨.stopped .abort, h, []⟩
      | ⟨n + 1, object⟩ => ⟨.returned (some (encode object)), ⟨n + 1, object⟩,
          [.received context remaining (some (encode object))]⟩
  | .challenge context remaining, h => match h with
      | ⟨0, _⟩ => ⟨.stopped .abort, h, []⟩
      | ⟨n + 1, object⟩ => ⟨.returned r, ⟨n, reference.restrict object r⟩,
          [.queried context remaining]⟩
  | .deliver context remaining _, h => ⟨.returned (), h, [.delivered context remaining]⟩

def invariant (reference : Reference F) (_count : Nat) {n : Nat} (_context : Nat)
    (s : State reference n) (h : Sigma reference.State) : Prop := h = ⟨n, s.object⟩

def ready (reference : Reference F) (message : Message F)
    (encode : {n : Nat} → reference.State (n + 1) → message.Carrier)
    (_count : Nat) {n : Nat} (_context : Nat) (s : State reference (n + 1))
    (m : message.Carrier) (h : Sigma reference.State) : Prop :=
  h = ⟨n + 1, s.object⟩ ∧ m = encode s.object

theorem execution (reference : Reference F) (message : Message F)
    (encode : {n : Nat} → reference.State (n + 1) → message.Carrier) (r : F) :
    HonestRunLaws (program message reference) (handler reference message encode r)
      (invariant reference) (ready reference message encode) where
  receive _count {_n} context s h same := by
    cases same
    exact ⟨encode s.object, ⟨_n + 1, s.object⟩,
      [.received context (_n + 1) (some (encode s.object))], rfl, rfl, rfl⟩
  query _count {_n} context s m h delivered := by
    obtain ⟨rfl, rfl⟩ := delivered
    exact ⟨r, ⟨_n, reference.restrict s.object r⟩, [.queried context (_n + 1)],
      ⟨_n, reference.restrict s.object r⟩, [.delivered context (_n + 1)], rfl, rfl, rfl⟩

def tableEncode {n : Nat} (table : Table F (n + 1)) : F × F :=
  Zkc.Protocols.Sumcheck.Multilinear.honestMessage table

theorem table_honest_message :
    HonestMessageLaw (representation (Message.endpoints F) (TableReference.data F))
      (ready (TableReference.data F) (Message.endpoints F) tableEncode) := by
  intro count n context s m h delivered
  rw [delivered.2]
  exact TableReference.honest_polynomial s.object

def factorEncode {n : Nat} (s : (FactorReference.data F).State (n + 1)) : F × F × F :=
  let m := Zkc.Protocols.Sumcheck.roundPolynomial (productCoefficients _ s.1 s.2)
  (m.constant, m.linear, m.quadratic)

theorem factor_honest_message :
    HonestMessageLaw (representation (Message.coefficientTriples F) (FactorReference.data F))
      (ready (FactorReference.data F) (Message.coefficientTriples F) factorEncode) := by
  intro count n context s m h delivered
  rw [delivered.2]
  rfl

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev K := ZMod 7

/-- f(x,y)=x+2y has a nonconstant marginal 2+2X over F7. -/
def table : Table K 2 := fun bits => (if bits 0 then 1 else 0) + (if bits 1 then 2 else 0)

def tableStart : State (TableReference.data K) 2 :=
  ⟨(TableReference.data K).total table, table, [], 91⟩

theorem table_message_and_restriction :
    tableEncode table = (2, 4) ∧
      (TableReference.data K).total ((TableReference.data K).restrict table 2) = 6 := by
  decide +kernel

theorem table_nonconstant :
    ((TableReference.data K).polynomial table).eval 0 ≠
      ((TableReference.data K).polynomial table).eval 1 := by
  rw [Message.endpointPolynomial_eval, Message.endpointPolynomial_eval]
  decide +kernel

/-- The honest-run theorem is exercised on actual table reference data. -/
theorem real_table_honest_run :
    ∃ result final observed,
      ((program (Message.endpoints K) (TableReference.data K)).remaining 2 17 tableStart).run
        (handler (TableReference.data K) (Message.endpoints K) tableEncode 2) ⟨2, table⟩ =
        ⟨.returned result, final, observed⟩ ∧
      (representation (Message.endpoints K) (TableReference.data K)).Yes result ∧
      invariant (TableReference.data K) 0 17 result final :=
  honest_run (representation _ _) Message.endpoints_laws TableReference.laws _ _ _
    (execution _ _ _ _) table_honest_message 2 17 tableStart ⟨2, table⟩ ⟨trivial, rfl⟩ rfl

/-- Check concrete return data after both stateful restrictions as well as the
consumer theorem above, which also retains the final handler and observations. -/
theorem table_return_data :
    ((((program (Message.endpoints K) (TableReference.data K)).remaining 2 17 tableStart).bind
      fun result => .done (result.claim, result.challengePrefix, result.privateFrame)).run
        (handler (TableReference.data K) (Message.endpoints K) tableEncode 2) ⟨2, table⟩).outcome =
      .returned (6, [2, 2], 91) := by
  decide +kernel

def factor : (FactorReference.data K).State 1 :=
  (fun bits => if bits 0 then 1 else 0, fun bits => if bits 0 then 1 else 0)

def factorStart : State (FactorReference.data K) 1 :=
  ⟨(FactorReference.data K).total factor, factor, [], 91⟩

/-- The X^2 reference is genuinely quadratic, and its decoded message differs
    from the multilinear extension of the Boolean product table off cube. -/
theorem factor_quadratic_at_two :
    (Message.coefficientTriples K).evaluate (factorEncode factor) 2 = 4 ∧
      ((FactorReference.data K).polynomial factor).natDegree = 2 := by
  constructor
  · decide +kernel
  · change (Polynomial.C (0 : K) + Polynomial.C 0 * Polynomial.X +
      Polynomial.C 1 * Polynomial.X ^ 2).natDegree = 2
    simp

theorem factor_message : factorEncode factor = (0, 0, 1) := by decide +kernel

theorem real_factor_honest_run :
    ∃ result final observed,
      ((program (Message.coefficientTriples K) (FactorReference.data K)).remaining 1 17 factorStart).run
        (handler (FactorReference.data K) (Message.coefficientTriples K) factorEncode 2) ⟨1, factor⟩ =
        ⟨.returned result, final, observed⟩ ∧
      (representation (Message.coefficientTriples K) (FactorReference.data K)).Yes result ∧
      invariant (FactorReference.data K) 0 17 result final :=
  honest_run (representation _ _) Message.coefficientTriples_laws FactorReference.laws _ _ _
    (execution _ _ _ _) factor_honest_message 1 17 factorStart ⟨1, factor⟩ ⟨trivial, rfl⟩ rfl

theorem factor_return_data :
    ((((program (Message.coefficientTriples K) (FactorReference.data K)).remaining 1 17 factorStart).bind
      fun result => .done (result.claim, result.challengePrefix, result.privateFrame)).run
        (handler (FactorReference.data K) (Message.coefficientTriples K) factorEncode 2) ⟨1, factor⟩).outcome =
      .returned (4, [2], 91) := by
  decide +kernel

#print axioms table_message_and_restriction
#print axioms table_nonconstant
#print axioms factor_quadratic_at_two
#print axioms factor_message
#print axioms table_return_data
#print axioms factor_return_data
#print axioms real_table_honest_run
#print axioms real_factor_honest_run
end TestsSecurity.SumcheckHonestReferences
