module

public import ZkcSecurity.Claims.PairValidator
public import ZkcSecurity.Examples.Components.SmallSumcheckFormula
public import ZkcSecurity.Examples.Components.TwoSumsFormula

@[expose] public section

/-! Common public initialization, source gaps, optional inputs, and raw-all
binding controls. Historical scalar(vector/index) counterexamples remain in the
private review records; these regressions assert the repaired actual games. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
namespace TestsSecurity.DomainPublicBinding
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims ZkcSecurity.FiatShamir

/-- The common initializer law is generic in all nominal carriers and raw values. -/
theorem common_encoding {carriers : Carriers} {types : List Ty}
    (values : Values carriers.Value types) (positions : List Nat)
    (arity : positions.length = types.length) (application : String)
    (environment : Domain.Environment carriers)
    (encoded : Domain.encodeValues values = some environment) :
    Domain.PublicBinding.fromEnvironment application positions arity environment =
      some ((DomainReduction.policyCodec types positions arity application).encode values) :=
  Domain.PublicBinding.fromEnvironment_encodeValues values application positions arity encoded

abbrev carriers := uniformCarriers Bool Unit
abbrev types : List Ty := [.vector "scalar", .index]
abbrev Statement := Values carriers.Value types

def statement (raw : List Bool) (count : Nat) : Statement := .cons raw (.cons count .nil)

def optionalSource (privateValue : Option Bool) (raw : Option (List Bool))
    (gap count service : Option Nat) :
    Values (Component carriers.Value) [.field "private", .vector "scalar", .index, .index, .service "rng"] :=
  .cons privateValue (.cons raw (.cons gap (.cons count (.cons service .nil))))

/-- Absent private values and service handles do not renumber public positions. -/
theorem private_gaps (privateValue : Option Bool) (raw : List Bool) (gap count : Nat)
    (service : Option Nat) :
    Domain.PublicBinding.project
      (Domain.PublicBinding.optionalInputs (optionalSource privateValue (some raw) (some gap) (some count) service))
      [1, 3] = some [.data (.vector "scalar" raw), .data (.index count)] := rfl

theorem absent_private_gaps (raw : List Bool) (count : Nat) (service : Option Nat) :
    Domain.PublicBinding.project
      (Domain.PublicBinding.optionalInputs (optionalSource none (some raw) none (some count) service))
      [1, 3] = some [.data (.vector "scalar" raw), .data (.index count)] := rfl

theorem missing_public_refused (privateValue : Option Bool) (count : Nat) (service : Option Nat) :
    Domain.PublicBinding.project
      (Domain.PublicBinding.optionalInputs (optionalSource privateValue none none (some count) service))
      [1, 3] = none := rfl

theorem missing_count_refused (raw : List Bool) (service : Option Nat) :
    Domain.PublicBinding.project
      (Domain.PublicBinding.optionalInputs (optionalSource none (some raw) none none service))
      [1, 3] = none := rfl

theorem source_coordinates (raw : List Bool) (count : Nat) (application : String) :
    (DomainReduction.policyCodec (carriers := carriers) types [1, 3] rfl application).encode
      (statement raw count) =
      [.publicBinding ⟨application,
        [(toString (1 : Nat), .vector (raw.map (.field "scalar"))), (toString (3 : Nat), .count count)]⟩] := rfl

/-- Every raw typed statement is determined, including wrong lengths and counts. -/
theorem raw_all_determined (application : String) :
    Typed.Determined (DomainReduction.policyCodec (carriers := carriers) types [1, 3] rfl application).encode :=
  DomainReduction.policyCodec_determined types [1, 3] rfl application

theorem malformed_not_erased (application : String) :
    (DomainReduction.policyCodec (carriers := carriers) types [1, 3] rfl application).encode (statement [] 99) ≠
    (DomainReduction.policyCodec (carriers := carriers) types [1, 3] rfl application).encode (statement [false] 0) := by
  intro same
  have equal := (DomainReduction.policyCodec (carriers := carriers) types [1, 3] rfl application).injective same
  cases equal

theorem missing_abi_refused :
    Domain.PublicBinding.fromEnvironment (carriers := carriers) (tys := types)
      "application" [1, 3] rfl [] = none := rfl

theorem excess_abi_refused (raw : List Bool) (count : Nat) :
    Domain.PublicBinding.fromEnvironment (carriers := carriers) (tys := types)
      "application" [1, 3] rfl [.data (.vector "scalar" raw), .data (.index count), .data (.index 0)] = none := rfl

theorem wrong_nominal_domain_refused (raw : List Bool) (count : Nat) :
    Domain.PublicBinding.fromEnvironment (carriers := carriers) (tys := types)
      "application" [1, 3] rfl [.data (.vector "other" raw), .data (.index count)] = none := rfl

/-- Application identity remains a request choice, not a theorem equating games. -/
theorem wrong_application_refused (application other : String) (different : application ≠ other)
    (values : Statement) :
    (DomainReduction.policyCodec types [1, 3] rfl application).encode values ≠
    (DomainReduction.policyCodec types [1, 3] rfl other).encode values := by
  intro same
  exact different ((Domain.PublicBinding.history_eq_iff application other [1, 3] rfl values values).mp same).1

/-- Renumbering sparse source coordinates changes the actual first query key. -/
theorem wrong_coordinates_key_refused (application : String) (values : Statement)
    (before after : Domain.History carriers) :
    (DomainReduction.policyCodec types [1, 3] rfl application).encode values ++ before ≠
    (DomainReduction.policyCodec types [0, 1] rfl application).encode values ++ after := by
  cases values with | cons raw rest => ?_
  cases rest with | cons count rest => ?_
  cases rest
  intro same
  have different := congrArg (fun history : Domain.History carriers =>
    match history with
    | .publicBinding binding :: _ => binding.row.head?.map Prod.fst
    | _ => none) same
  change some (toString (1 : Nat)) = some (toString (0 : Nat)) at different
  have refused : (1 : Nat) = 0 := Domain.PublicBinding.coordinate_injective (Option.some.inj different)
  cases refused

/-- Large source positions do not alias the old bounded service-port formatter. -/
theorem large_coordinate_not_truncated : toString (10001 : Nat) ≠ toString (1 : Nat) := by
  intro same
  have impossible := Domain.PublicBinding.coordinate_injective same
  omega

/-- Historical scalar(vector/index) encoding cannot supply the repaired key. -/
theorem wrong_scalar_codec_key_refused (application : String) (raw : List Bool) (count : Nat)
    (before after : Domain.History carriers) :
    (DomainReduction.policyCodec types [1, 3] rfl application).encode (statement raw count) ++ before ≠
      [Domain.Event.publicBinding ⟨application,
        [("1", .scalar (.vector "scalar" raw)), ("3", .scalar (.index count))]⟩] ++ after := by
  intro same
  have different := congrArg (fun history : Domain.History carriers =>
    match history with
    | .publicBinding binding :: _ =>
      match binding.row with
      | (_, .vector _) :: _ => true
      | _ => false
    | _ => false) same
  change true = false at different
  cases different

noncomputable section
open ZkcSecurity.Examples ZkcSecurity.Domains.PrimeField
abbrev Scalar := ZMod blsModulus

/-- Actual small-root initializer, universally over raw tables and counts. -/
theorem small_initial_history (raw : List Scalar) (claim : Scalar) (count : Nat) :
    Generated.Components.SmallSumcheckABI.initialHistory raw claim count =
      (DomainReduction.policyCodec Generated.SmallSumcheck.validatorArtifacts.publics
        Generated.SmallSumcheck.selected.policy.publicInputs
        Generated.SmallSumcheck.subject.publicBindingArity
        Generated.SmallSumcheck.subject.originalExport).encode
          (.cons raw (.cons claim (.cons count .nil))) := rfl

/-- Actual composed-root initializer, including both statements and count. -/
theorem two_initial_history (left right : List Scalar) (lc rc : Scalar) (count : Nat) :
    Generated.Components.TwoSumsABI.initialHistory left right lc rc count =
      (DomainReduction.policyCodec Generated.TwoSums.validatorArtifacts.publics
        Generated.TwoSums.selected.policy.publicInputs Generated.TwoSums.subject.publicBindingArity
        Generated.TwoSums.subject.originalExport).encode
          (.cons left (.cons right (.cons lc (.cons rc (.cons count .nil))))) := rfl

/-- Both actual prepared ABIs carry that exact codec history, for every service option. -/
theorem small_actual_inputs (raw : List Scalar) (claim : Scalar) (count : Nat) (service : Option Nat) :
    Generated.SmallSumcheck.subject.runtimeInputs
      (Generated.Components.SmallSumcheckABI.inputs raw claim count service) =
      some (Generated.Components.SmallSumcheckABI.producerInputs raw claim count,
        Generated.Components.SmallSumcheckABI.validatorInputs raw claim count) :=
  Generated.Components.SmallSumcheckABI.runtimeInputs_eq raw claim count service

theorem two_actual_inputs (left right : List Scalar) (lc rc : Scalar) (count : Nat) (service : Option Nat) :
    Generated.TwoSums.subject.runtimeInputs
      (Generated.Components.TwoSumsABI.inputs left right lc rc count service) =
      some (Generated.Components.TwoSumsABI.producerInputs left right lc rc count,
        Generated.Components.TwoSumsABI.validatorInputs left right lc rc count) :=
  Generated.Components.TwoSumsABI.runtimeInputs_eq left right lc rc count service

/-- Completeness inputs instantiate the generic admitted-boundary equality. -/
theorem small_projected_binding (raw : List Scalar) (claim : Scalar) (count : Nat) (service : Option Nat) :
    ∃ (values : Values blsScalarModel.toCarriers.Value Generated.SmallSumcheck.validatorArtifacts.publics)
      (producer validator : Domain.Environment blsScalarModel.toCarriers),
      HonestPair.Subject.project (HonestPair.Subject.encodeInputs
        (Generated.Components.SmallSumcheckABI.inputs raw claim count service))
        Generated.SmallSumcheck.selected.policy.publicInputs = some validator ∧
      Domain.encodeValues values = some validator ∧
      Generated.Components.SmallSumcheckABI.producerInputs raw claim count = producer ++
        [.transcript Generated.SmallSumcheck.selected.policy.suite
          ((DomainReduction.policyCodec Generated.SmallSumcheck.validatorArtifacts.publics
            Generated.SmallSumcheck.validatorArtifacts.participant.policy.publicInputs
            (DomainReduction.policyArity Generated.SmallSumcheck.validatorCompiled)
            Generated.SmallSumcheck.subject.originalExport).encode values)] ∧
      Generated.Components.SmallSumcheckABI.validatorInputs raw claim count = validator ++
        [.transcript Generated.SmallSumcheck.selected.policy.suite
          ((DomainReduction.policyCodec Generated.SmallSumcheck.validatorArtifacts.publics
            Generated.SmallSumcheck.validatorArtifacts.participant.policy.publicInputs
            (DomainReduction.policyArity Generated.SmallSumcheck.validatorCompiled)
            Generated.SmallSumcheck.subject.originalExport).encode values)] :=
  Generated.SmallSumcheck.subject.runtimeInputs_binding
    (Generated.Components.SmallSumcheckABI.inputs raw claim count service) _ _
    (small_actual_inputs raw claim count service)

theorem two_projected_binding (left right : List Scalar) (lc rc : Scalar) (count : Nat) (service : Option Nat) :
    ∃ (values : Values blsScalarModel.toCarriers.Value Generated.TwoSums.validatorArtifacts.publics)
      (producer validator : Domain.Environment blsScalarModel.toCarriers),
      HonestPair.Subject.project (HonestPair.Subject.encodeInputs
        (Generated.Components.TwoSumsABI.inputs left right lc rc count service))
        Generated.TwoSums.selected.policy.publicInputs = some validator ∧
      Domain.encodeValues values = some validator ∧
      Generated.Components.TwoSumsABI.producerInputs left right lc rc count = producer ++
        [.transcript Generated.TwoSums.selected.policy.suite
          ((DomainReduction.policyCodec Generated.TwoSums.validatorArtifacts.publics
            Generated.TwoSums.validatorArtifacts.participant.policy.publicInputs
            (DomainReduction.policyArity Generated.TwoSums.validatorCompiled)
            Generated.TwoSums.subject.originalExport).encode values)] ∧
      Generated.Components.TwoSumsABI.validatorInputs left right lc rc count = validator ++
        [.transcript Generated.TwoSums.selected.policy.suite
          ((DomainReduction.policyCodec Generated.TwoSums.validatorArtifacts.publics
            Generated.TwoSums.validatorArtifacts.participant.policy.publicInputs
            (DomainReduction.policyArity Generated.TwoSums.validatorCompiled)
            Generated.TwoSums.subject.originalExport).encode values)] :=
  Generated.TwoSums.subject.runtimeInputs_binding
    (Generated.Components.TwoSumsABI.inputs left right lc rc count service) _ _
    (two_actual_inputs left right lc rc count service)

#print axioms Domain.PublicBinding.project_statement
#print axioms HonestPair.Subject.runtimeInputs_binding
#print axioms small_initial_history
#print axioms two_initial_history
#print axioms small_projected_binding
#print axioms two_projected_binding
end
end TestsSecurity.DomainPublicBinding
