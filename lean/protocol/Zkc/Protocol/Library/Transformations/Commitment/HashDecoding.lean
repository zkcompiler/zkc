module

public import Zkc.Protocol.Library.Transformations.Commitment.Extractable

@[expose] public section

/-! # Consistent decoding of recorded hash answers

Extraction needs uniqueness of the decoded value within a role. Leaf and node
queries may legitimately have the same answer when they encode the same
primitive input. Global response injectivity is sufficient, but is stronger
than the consistency needed by each decoder. These are deterministic record
properties; no cryptographic collision bound is asserted here.
-/

set_option autoImplicit false
namespace ZkcSecurity.Commitment
variable {Query Y Value : Type}

/-- Two recorded answers with a common label decode to the same value whenever
both queries belong to this decoder's role. Queries outside that role impose
no condition. -/
def DecoderConsistent (decode : Query → Option Value) (log : HashLog Query Y) : Prop :=
  ∀ first ∈ log, ∀ second ∈ log, ∀ firstValue secondValue,
    decode first.1 = some firstValue → decode second.1 = some secondValue →
    first.2 = second.2 → firstValue = secondValue

namespace DecoderConsistent

/-- Global query injectivity implies every decoder's consistency. -/
theorem of_responseInjective (decode : Query → Option Value) {log : HashLog Query Y}
    (injective : MerkleTreeExtractor.ResponseInjectiveOn log) : DecoderConsistent decode log := by
  intro first firstMem second secondMem firstValue secondValue firstDecoded secondDecoded same
  have queryEq := injective first firstMem second secondMem same
  rw [queryEq, secondDecoded] at firstDecoded
  exact Option.some.inj firstDecoded.symm

/-- Restricting the record preserves decoder consistency. -/
theorem mono {decode : Query → Option Value} {small large : HashLog Query Y}
    (consistent : DecoderConsistent decode large)
    (included : ∀ entry ∈ small, entry ∈ large) : DecoderConsistent decode small := by
  intro first firstMem second secondMem
  exact consistent first (included _ firstMem) second (included _ secondMem)

/-- First-match extraction returns any recorded value in a consistent decoding
role. The extractor is unchanged and does not choose an arbitrary preimage. -/
theorem find_of_mem [DecidableEq Y] {decode : Query → Option Value}
    {log : HashLog Query Y} (consistent : DecoderConsistent decode log)
    {query : Query} {label : Y} {value : Value}
    (member : (⟨query, label⟩ : (_ : Query) × Y) ∈ log)
    (decoded : decode query = some value) :
    (log.find? fun entry => (decode entry.1).isSome && entry.2 == label).bind
      (fun entry => decode entry.1) = some value := by
  cases found : log.find? (fun entry => (decode entry.1).isSome && entry.2 == label) with
  | none =>
      have := List.find?_eq_none.mp found _ member
      simp [decoded] at this
  | some entry =>
      have holds := List.find?_some found
      have entryMember := List.mem_of_find?_eq_some found
      simp only [Bool.and_eq_true, beq_iff_eq] at holds
      cases entryDecoded : decode entry.1 with
      | none => simp [entryDecoded] at holds
      | some entryValue =>
          have same := consistent entry entryMember _ member entryValue value
            entryDecoded decoded holds.2
          simpa [entryDecoded] using congrArg some same

end DecoderConsistent
end ZkcSecurity.Commitment
