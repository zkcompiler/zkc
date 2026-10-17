module

public import Zkc.Source.Structured.Import

@[expose] public section

/-! Bounded model admission without native application-expansion budgets.
This opt-in API returns the existing UnitPayload. The standard importer retains
its original checks, refusal order and native-profile evidence. -/

namespace Zkc.Source.Structured

/-- Admit formed bodies without the native expansion policy. Stored-source
limits, effective-site identity and traversal capacity, linking, availability,
roles, services and authored repeat maxima remain unchanged. -/
def checkFormedPayload (snapshot : Snapshot) : Except String UnitPayload := do
  let (domains, headers, summaries) ← checkUnitHeaders snapshot
  let helpers ← checkUnitHelpers snapshot domains summaries
  let protocols ← checkUnitProtocols snapshot domains summaries headers helpers
  checkEffectiveProtocolSites snapshot
  linkUnitPayload snapshot helpers protocols

/-- Expose the actual model checks without substituting a semantic assumption. -/
theorem checkFormedPayload_stages {snapshot : Snapshot} {payload : UnitPayload}
    (accepted : checkFormedPayload snapshot = .ok payload) :
    ∃ domains headers summaries helpers protocols,
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      checkUnitHelpers snapshot domains summaries = .ok helpers ∧
      checkUnitProtocols snapshot domains summaries headers helpers = .ok protocols ∧
      checkEffectiveProtocolSites snapshot = .ok () ∧
      linkUnitPayload snapshot helpers protocols = .ok payload := by
  unfold checkFormedPayload at accepted
  simp only [bind, Except.bind] at accepted
  repeat' first | contradiction | split at accepted
  all_goals exact ⟨_, _, _, _, _, by assumption, by assumption, by assumption,
    by assumption, accepted⟩

/-- Native-profile success is exactly model admission plus native expansion
budgets, for the same payload. This is a success equivalence: the two entry
points intentionally need not choose the same error when several checks fail. -/
theorem check_payload_ok_iff {snapshot : Snapshot} {payload : UnitPayload} :
    check_payload snapshot = .ok payload ↔
      checkFormedPayload snapshot = .ok payload ∧
      (checkNativeApplicationBudgets snapshot).isOk = true := by
  constructor
  · intro accepted
    obtain ⟨domains, headers, summaries, helpers, protocols,
      headerEq, helperEq, protocolEq, metadataEq, linked⟩ := check_payload_stages accepted
    obtain ⟨⟨nativeSummary, nativeEq⟩, sitesEq⟩ := checkApplicationMetadata_checks metadataEq
    constructor
    · simp only [checkFormedPayload, headerEq, helperEq, protocolEq, sitesEq, linked,
        bind, Except.bind]
    · simp [nativeEq, Except.isOk, Except.toBool]
  · rintro ⟨formed, native⟩
    obtain ⟨domains, headers, summaries, helpers, protocols,
      headerEq, helperEq, protocolEq, sitesEq, linked⟩ := checkFormedPayload_stages formed
    exact check_payload_of_phases headerEq helperEq protocolEq
      (checkApplicationMetadata_of_checks native sitesEq) linked

end Zkc.Source.Structured
