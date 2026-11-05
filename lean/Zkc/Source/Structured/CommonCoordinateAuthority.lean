module

public import Zkc.Source.Structured.OracleIngress
public import Zkc.Source.Structured.CommonCoordinateReport

@[expose] public section

/-! Finite certificate coverage is read back through the canonical importer's exact
retained-source theorem. No caller supplies a replacement protocol body. -/

set_option autoImplicit false
namespace Zkc.Source.Structured.CommonCoordinate
open NormalForm

abbrev RootPlan (snapshot : Snapshot) (definitions : List CheckedProtocol)
    (definition : CheckedProtocol) (pair : Pair) :=
  Plan snapshot definitions pair id
    {definition := snapshot.definitions.findIdx (·.name == definition.name)}
    (inputOrigins (snapshot.definitions.findIdx (·.name == definition.name)) definition.inputs)
    definition.body (inputSymbols pair id definition.inputs definition.inputScopes)

theorem rolePairs_complete (count left right : Nat) (leftBound : left < count)
    (rightBound : right < count) (ordered : left < right) :
    (⟨left, right⟩ : Pair) ∈ rolePairs count := by
  apply List.mem_flatMap.mpr
  refine ⟨left, List.mem_range.mpr leftBound, List.mem_map.mpr ?_⟩
  refine ⟨right, ?_, rfl⟩
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨rightBound, ordered⟩

theorem PlansFor.covers {snapshot : Snapshot} {definitions : List CheckedProtocol}
    {definition : CheckedProtocol} {pairs : List Pair}
    (certificate : PlansFor snapshot definitions definition pairs) {pair : Pair}
    (member : pair ∈ pairs) : Nonempty (RootPlan snapshot definitions definition pair) := by
  induction certificate with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | member
    · subst pair; exact ⟨head⟩
    · exact ih member

theorem UnitCertificate.covers {snapshot : Snapshot} {definitions remaining : List CheckedProtocol}
    (certificate : UnitCertificate snapshot definitions remaining) {definition : CheckedProtocol}
    (member : definition ∈ remaining) {pair : Pair} (selected : pair ∈ rolePairs definition.roles.length) :
    Nonempty (RootPlan snapshot definitions definition pair) := by
  induction certificate with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | member
    · subst definition; exact head.covers selected
    · exact ih member

end Zkc.Source.Structured.CommonCoordinate

namespace Zkc.Source.Structured

/-- A canonical Oracle subject certifies every stored role-pair/body, including dormant
ones. The same definition is the exact lowering and elaboration of retained source. -/
theorem OracleSubject.coordinateAuthority {snapshot : Snapshot} (subject : OracleSubject snapshot)
    {definition : CheckedProtocol} (member : definition ∈ subject.imported.program.payload.protocols)
    {pair : CommonCoordinate.Pair} (selected : pair ∈ CommonCoordinate.rolePairs definition.roles.length) :
    Nonempty (CommonCoordinate.RootPlan snapshot subject.imported.program.payload.protocols
      definition pair) ∧
    ∃ function domains headers summaries,
      .function function ∈ snapshot.definitions ∧ function.kind = .protocol ∧
      checkUnitHeaders snapshot = .ok (domains, headers, summaries) ∧
      checkProtocol snapshot domains summaries function headers = .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol snapshot domains summaries headers function definition.signature = .ok definition.raw :=
  ⟨subject.coordinates.covers member selected, subject.imported.protocolSource member⟩

end Zkc.Source.Structured
