module

import ZkcSecurityExamples.RootProperties.SmallSumcheck
import ZkcSecurityExamples.RootProperties.TwoSums

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
  ZkcSecurity.Examples.RootProperties.SmallSumcheck.compiled_ideal_complete

example : CanonicalCompleteness ZkcSecurity.Examples.Generated.TwoSums.subject 0 :=
  ZkcSecurity.Examples.RootProperties.TwoSums.compiled_ideal_complete

#check ZkcSecurity.Examples.RootProperties.SmallSumcheck.compiled_ideal_complete
#check ZkcSecurity.Examples.RootProperties.TwoSums.compiled_ideal_complete

#print axioms ZkcSecurity.Examples.RootProperties.SmallSumcheck.abi_readback
#print axioms ZkcSecurity.Examples.RootProperties.TwoSums.abi_readback
#print axioms ZkcSecurity.Examples.RootProperties.SmallSumcheck.compiled_ideal_complete
#print axioms ZkcSecurity.Examples.RootProperties.TwoSums.compiled_ideal_complete
#print axioms ZkcSecurity.FiatShamir.Readback.run
#print axioms ZkcSecurity.FiatShamir.Readback.perfect_abi

end TestsSecurity.OriginalHonestCompleteness
