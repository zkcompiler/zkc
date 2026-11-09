module

public import Zkc.Verification.Families.Sumcheck.Derivation
public import Zkc.Protocol.Library.Families.Sumcheck.Completeness
public import Zkc.Verification.Families.Sumcheck.Cost
public import Zkc.Protocol.Obligations.TokenRules

/-! The Sumcheck consumers compose through the generic derivation, returned
frame, path-budget and execution APIs re-exported here. Shared-key probability
is not inferred by bind. No family-specific composition wrapper is needed. -/
