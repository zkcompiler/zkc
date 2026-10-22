import ZkcSecurity.Claims.Resolution
import ZkcSecurity.Examples.Subjects.Schnorr.Artifacts

/-! Admission controls use the actual admitted catalogue. No dictionary can
install a numeric meaning for an unknown spelling or fabricate a cardinality.
-/

set_option autoImplicit false
namespace TestsSecurity.ClaimAdmission
open Zkc.Claims Zkc.Source.Structured ZkcSecurity.Claims ZkcSecurity.Endpoint

private def snapshot := ZkcSecurity.Examples.Subjects.Schnorr.artifacts.original
private def cardinality : Wire.Expr := .application "cardinality" none [(none, .reference "bls12-381.fr")]

variable (F : Type) [Fintype F]

example : Numeric.cardinality F snapshot "bls12-381.fr" = .ok (Fintype.card F) := rfl
example : Numeric.cardinality F snapshot "unrelated.fr" =
    .error ⟨["unadmitted nominal domain: unrelated.fr"]⟩ := rfl
example : Numeric.cardinality F snapshot "bls12-381.g1" =
    .error ⟨["unsupported cardinality carrier: bls12-381.g1"]⟩ := rfl
example : Bound.elaborate F snapshot "Q" (.reference "fabricated") =
    .error ⟨["unbound numeric parameter: fabricated"]⟩ := rfl
example : Bound.elaborate F snapshot "Q" (.reference "cardinality(bls12-381.fr)") =
    .error ⟨["unbound numeric parameter: cardinality(bls12-381.fr)"]⟩ := rfl
example : Bound.elaborate F snapshot "Q" (.reference "Q") = .ok .queryBudget := rfl
example : Numeric.normalize F snapshot (.application "cardinality" none [(some "wrong", .reference "bls12-381.fr")]) =
    .error ⟨["numeric application: cardinality"]⟩ := rfl
example : Numeric.normalize F snapshot (.application "cardinality" none []) =
    .error ⟨["numeric application: cardinality"]⟩ := rfl
example : Numeric.normalize F snapshot (.application "cardinality" (some 0) [(none, .reference "bls12-381.fr")]) =
    .error ⟨["numeric application: cardinality"]⟩ := rfl
example : Numeric.normalize F snapshot (.application "cardinality" none [(none, .natural 17)]) =
    .error ⟨["numeric application: cardinality"]⟩ := rfl
example : Numeric.normalize F snapshot (.binary .div (.natural 2)
    (.application "cardinality" none [(some "wrong", .reference "bls12-381.fr")])) =
    .error ⟨["numeric application: cardinality"]⟩ := rfl
example [Nonempty F] : Bound.elaborate F snapshot "Q" (.binary .div (.natural 2) cardinality) =
    .ok (.div (.constant 2) (Fintype.card F : ℚ≥0)) := by
  exact Bound.elaborate_div_cardinality F snapshot "Q" "bls12-381.fr" (.natural 2) rfl

private def adaptive (symbol : String) : Wire.Application :=
  ⟨exactUniform, [(some "statement", .reference "statements.adaptive"),
    (some "application", .reference symbol), (some "queries", .reference "Q"),
    (some "budget_symbol", .reference "Q")]⟩

example (application : String) :
    modelSchema F snapshot (.parameter "application" application) .idealMeaning (adaptive "application") =
      .ok (.ok ⟨.adaptive, .symbolic "Q", "Q", application, .constant 0,
        some ⟨"application", application, .parameter⟩⟩) := rfl
example (application : String) :
    modelSchema F snapshot (.fixed "session" application) .idealMeaning (adaptive "session") =
      .ok (.ok ⟨.adaptive, .symbolic "Q", "Q", application, .constant 0,
        some ⟨"session", application, .fixed⟩⟩) := rfl
example : modelSchema F snapshot .empty .idealMeaning (adaptive "application") =
    .error (.schema "unbound application context: application") := rfl
example (application : String) :
    modelSchema F snapshot (.parameter "application" application) .idealMeaning (adaptive "unknown") =
      .error (.schema "unbound application context: unknown") := rfl
example : modelSchema F snapshot .empty .idealMeaning
    ⟨exactUniform, [(some "queries", .reference "undeclared"), (some "budget_symbol", .reference "Q")]⟩ =
      .ok (.error ⟨["unbound numeric parameter: undeclared"]⟩) := rfl
example : modelSchema F snapshot .empty .idealMeaning
    ⟨exactUniform, [(some "queries", .reference "Q")]⟩ =
      .ok (.error ⟨["unbound numeric parameter: Q"]⟩) := rfl

-- A model registry selected for another stage cannot override the subject's stage.
example : resolveModel (models .empty .idealMeaning) F snapshot .executableBytes ⟨exactUniform, []⟩ =
    .error .stageMismatch := rfl

-- The admitted carrier fixes cardinality, including under a binder.
example (n : Nat) (wrong : n ≠ Fintype.card F) : Numeric.cardinality F snapshot "bls12-381.fr" ≠ .ok n := by
  intro same
  exact wrong (Except.ok.inj same).symm

end TestsSecurity.ClaimAdmission
