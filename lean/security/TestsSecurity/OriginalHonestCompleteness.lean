module

import ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Completeness
import ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Completeness
import TestsSecurity.OriginalHonestTransport

/-! Audit the complete original-source path to the two unchanged actual
canonical subjects. No fixture inputs or conditional root premise remain. -/
set_option autoImplicit false
noncomputable section
namespace TestsSecurity.OriginalHonestCompleteness
open Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair
open ZkcSecurity.Examples.Generated
open ZkcSecurity.Domains.PrimeField

local instance : ∀ event : Domain.Event blsScalarModel.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable blsModulus

example : CanonicalCompleteness ZkcSecurity.Examples.Generated.SmallSumcheck.subject 0 :=
  OriginalSecurity.SmallSumcheck.Completeness.compiled_ideal_complete

example : CanonicalCompleteness ZkcSecurity.Examples.Generated.TwoSums.subject 0 :=
  OriginalSecurity.TwoSums.Completeness.compiled_ideal_complete

#check OriginalSecurity.SmallSumcheck.Completeness.compiled_ideal_complete
#check OriginalSecurity.TwoSums.Completeness.compiled_ideal_complete

#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalHonest.advance_honest
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalHonest.round
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalHonest.step
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalHonest.loop
#print axioms ZkcSecurity.Realizations.Sumcheck.OriginalHonest.reduce
#print axioms OriginalSecurity.SmallSumcheck.Honest.source
#print axioms OriginalSecurity.TwoSums.Honest.source
#print axioms OriginalSecurity.SmallSumcheck.Honest.readback
#print axioms OriginalSecurity.TwoSums.Honest.readback
#print axioms OriginalSecurity.SmallSumcheck.Honest.actual
#print axioms OriginalSecurity.TwoSums.Honest.actual
#print axioms OriginalSecurity.SmallSumcheck.Completeness.abi_readback
#print axioms OriginalSecurity.TwoSums.Completeness.abi_readback
#print axioms OriginalSecurity.SmallSumcheck.Completeness.compiled_ideal_complete
#print axioms OriginalSecurity.TwoSums.Completeness.compiled_ideal_complete
#print axioms ZkcSecurity.FiatShamir.Readback.run
#print axioms ZkcSecurity.FiatShamir.Readback.perfect_abi

end TestsSecurity.OriginalHonestCompleteness
