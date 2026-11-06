module

public import ZkcArkLib.Fri.SourcePublication
public import Zkc.Source.Structured.OracleReadback

@[expose] public section

/-! An expanded read follows the logical registry to a base table and
returns the same cell that was installed at publication. Other newer entries
and child expansion metadata do not change the selected cell. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.StoredWord
open Zkc.Source Zkc.Source.Structured

variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {Aux E : Type} {d : String} {n : Nat}

/-- The visible source table and its immutable provider word agree on their
anchor, row count and coordinates. The receiver may retain no private data. -/
structure Base (entries : OracleEntries model snapshot domains math) (self : Nat)
    (source : OracleAnchor) (word : Fin (2 ^ n) → model.Field d)
    (state : PublishedWords.State model Aux) where
  registry : OracleStoredTable model snapshot domains math (.field d)
  lookup : OracleStore.find entries (.field d) source = some registry
  data : Option (List (model.Field d))
  base : registry.payload = .base data
  visible : OracleStore.visible self registry.holder registry.receivers = true
  registryRows : registry.rows = 2 ^ n
  stored : PublishedWords.Word model (.field d)
  found : PublishedWords.find state.words (.field d) source = some stored
  answer : stored.kind.answer = .field d
  shape : OracleStore.validRows stored.kind stored.rows = true
  rows : stored.rows = 2 ^ n
  cells : stored.cells = List.ofFn word

theorem Base.cell {entries : OracleEntries model snapshot domains math} {self : Nat}
    {source : OracleAnchor} {word : Fin (2 ^ n) → model.Field d}
    {state : PublishedWords.State model Aux} (live : Base entries self source word state)
    (index : Fin (2 ^ n)) (location : OracleLocation)
    (expansion : List (OracleAnchor × OracleLocation)) (count : Nat) :
    let request := Phases.publishedRequest d source index.val location expansion
    OracleStore.answer model (PublishedWords.read (E := E)) self entries request (state, count) =
      ⟨.returned (word index), (state, count + 1), [.query request]⟩ := by
  dsimp only
  rcases live with ⟨registry, lookup, data, base, visible, registryRows, stored, found, answer, shape, rows, cells⟩
  have limit : stored.rows < indexLimit := of_decide_eq_true (Bool.and_eq_true_iff.mp shape).1
  have registryShape : OracleStore.validRows (.table (.field d) none) registry.rows = true := by
    simp [OracleStore.validRows, OracleKind.rows, registryRows, ← rows, limit]
  have routed := OracleStore.answerOfBase (PublishedWords.read (E := E)) self entries
    (Phases.publishedRequest d source index.val location expansion) (state, count) registry data
    lookup base visible registryShape (registryRows.symm ▸ index.isLt)
  rw [routed, SourcePublication.read_fixed_word source word stored answer shape rows cells
    index location expansion state found]
  rfl

end ZkcSecurity.ArkLib.Fri.StoredWord
