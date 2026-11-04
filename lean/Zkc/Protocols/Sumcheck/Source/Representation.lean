module

public import Zkc.Protocols.Sumcheck.Multilinear.Fold
public import Zkc.Protocols.Sumcheck.Multilinear.Reduction

@[expose] public section

/-! Mathematics of the flat-table representation, independent of source slots,
helper tables and interaction. The existing Sumcheck mathematics is unchanged. -/
set_option autoImplicit false
namespace Zkc.Protocols.Sumcheck.Multilinear
open Zkc.Polynomial Zkc.Polynomial.Multilinear

variable {F : Type} [CommRing F]

def endpoints (entries : List F) : F × F :=
  ((entries.take (entries.length / 2)).sum, (entries.drop (entries.length / 2)).sum)

/-- Conservation makes the second endpoint recoverable from the first. -/
theorem endpoints_sum (entries : List F) :
    (endpoints entries).1 + (endpoints entries).2 = entries.sum := by
  simpa only [endpoints, List.sum_append] using
    congrArg List.sum (List.take_append_drop (entries.length / 2) entries)

theorem endpoints_high (entries : List F) :
    entries.sum - (endpoints entries).1 = (endpoints entries).2 := by
  rw [← endpoints_sum entries]
  exact add_sub_cancel_left _ _

omit [CommRing F] in
/-- Decoding supplies exactly the positive, even split needed by sums. -/
theorem decoded_split {n : Nat} (entries : List F) (table : Table F (n + 1))
    (decoded : ofList? (n + 1) entries = some table) :
    0 < entries.length ∧ entries.length % 2 = 0 := by
  rw [ofList?_length entries table decoded, Nat.pow_succ]
  constructor
  · exact Nat.mul_pos (Nat.pow_pos (by decide)) (by decide)
  · omega

/-- No admission premise on width is needed for the endpoint mathematics. -/
theorem endpoints_honestMessage {n : Nat} (entries : List F) (table : Table F (n + 1))
    (decoded : ofList? (n + 1) entries = some table) :
    endpoints entries = honestMessage table := by
  exact Prod.ext
    (booleanSum_ofList? _ _ (decode_low_half entries table decoded)).symm
    (booleanSum_ofList? _ _ (decode_high_half entries table decoded)).symm

/-- The mathematical state obligation carried by the actual restriction loop.
The endpoint and residual-claim consequences are derived, not extra hypotheses. -/
structure RestrictionInvariant {N : Nat} (table : Table F N) (point entries : List F)
    (dimension columns : Nat) : Prop where
  represents : PartialEvaluation table point entries
  remaining : dimension = N - point.length
  unitWidth : columns = 1

namespace RestrictionInvariant
variable {N : Nat} {table : Table F N} {point entries : List F} {dimension columns : Nat}

theorem ofPrefix (raw : List F) (decoded : ofList? N raw = some table)
    (point : List F) (fits : point.length ≤ N) :
    RestrictionInvariant table point (restrictPrefixValues raw point) (N - point.length) 1 :=
  ⟨partialEvaluation_restrict raw table decoded point fits, rfl, rfl⟩

theorem step (invariant : RestrictionInvariant table point entries dimension columns)
    (remaining : point.length < N) (challenge : F) :
    RestrictionInvariant table (point ++ [challenge]) (restrictValues entries challenge)
      (dimension - 1) columns := by
  refine ⟨partialEvaluation_fold table point entries invariant.represents remaining challenge,
    ?_, invariant.unitWidth⟩
  simp only [invariant.remaining, List.length_append, List.length_singleton, Nat.sub_sub]

theorem message (invariant : RestrictionInvariant table point entries dimension columns)
    (remaining : point.length < N) :
    endpoints entries = (roundEndpoint table point 0, roundEndpoint table point 1) :=
  Prod.ext (partialEvaluation_endpoints table point entries invariant.represents remaining).1
    (partialEvaluation_endpoints table point entries invariant.represents remaining).2

theorem residual (invariant : RestrictionInvariant table point entries dimension columns) :
    entries.sum = cubeSum (N - point.length)
      (fun suffix => extension N table (coordinates N (point ++ List.ofFn suffix))) :=
  partialEvaluation_sum table point entries invariant.represents

/-- The invariant supplies the current finite table without any scalar claim. -/
theorem decoded (invariant : RestrictionInvariant table point entries dimension columns) :
    ∃ current : Table F dimension, ofList? dimension entries = some current := by
  rw [invariant.remaining]
  obtain ⟨current, decoded, _⟩ := invariant.represents.2
  exact ⟨current, decoded⟩

/-- The same represented restriction step supports honest equality and false
claim preservation. No distribution or honest-message assumption is needed. -/
theorem round_sum {n : Nat}
    (invariant : RestrictionInvariant table point entries (n + 1) columns) (challenge : F) :
    (restrictValues entries challenge).sum =
      (1 - challenge) * (endpoints entries).1 + challenge * (endpoints entries).2 := by
  obtain ⟨current, decoded⟩ := invariant.decoded
  exact restrictValues_sum entries challenge (decoded_split entries current decoded).2

theorem complete (invariant : RestrictionInvariant table point entries dimension columns)
    (finished : point.length = N) :
    entries.sum = extension N table (coordinates N point) :=
  partialEvaluation_complete table point entries invariant.represents finished

end RestrictionInvariant
end Zkc.Protocols.Sumcheck.Multilinear
