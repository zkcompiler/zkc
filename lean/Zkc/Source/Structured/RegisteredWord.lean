module

public import Zkc.Source.Structured.PublishedWordsLaws
public import Zkc.Source.Structured.OracleInvariant
public import Zkc.Source.Structured.OracleReadback
public import Zkc.Source.Structured.OracleReadEffects

@[expose] public section

/-! A published base word has two entries at the same dynamic anchor. The
logical table authorizes this participant and the provider fixes every cell.
Subsequent fresh publications may grow both tables. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.PublishedWords
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {Aux E : Type} {row : Ty} {size : Nat}

structure RegisteredWord (entries : OracleEntries model snapshot domains math) (participant : Nat)
    (source : OracleAnchor) (word : Fin size → model.Value row) (state : State model Aux) where
  registry : OracleStoredTable model snapshot domains math row
  lookup : OracleStore.find entries row source = some registry
  data : Option (List (model.Value row))
  base : registry.payload = .base data
  visible : OracleStore.visible participant registry.holder registry.receivers = true
  registryRows : registry.rows = size
  stored : Word model row
  found : find state.words row source = some stored
  answer : stored.kind.answer = row
  shape : OracleStore.validRows stored.kind stored.rows = true
  rows : stored.rows = size
  cells : stored.cells = List.ofFn word
  holder : stored.holder = registry.holder
  receivers : stored.receivers = registry.receivers
  occurrence : stored.location.anchor = source

variable {entries : OracleEntries model snapshot domains math} {participant : Nat} {source : OracleAnchor}
  {word : Fin size → model.Value row} {state : State model Aux}

def RegisteredWord.extend (live : RegisteredWord entries participant source word state)
    (newer : OracleEntries model snapshot domains math) (fresh : OracleStore.hasAnchor newer source = false)
    {after : State model Aux} (frame : Preserves state.words after.words) :
    RegisteredWord (newer ++ entries) participant source word after :=
  {live with
    lookup := (OracleStore.findSkipNewer newer entries row source fresh).trans live.lookup
    found := frame.lookup row source live.stored live.found}

/-- The source interpreter already proves that each logical step leaves the
registry alone or inserts one fresh table. This suffices to transport an old
word without asking a protocol author for a disjointness proof. -/
def RegisteredWord.afterExtension (live : RegisteredWord entries participant source word state)
    {later : OracleEntries model snapshot domains math} (extension : OracleStore.Extension participant entries later)
    {after : State model Aux} (frame : Preserves state.words after.words) :
    RegisteredWord later participant source word after := by
  refine {live with found := frame.lookup row source live.stored live.found, lookup := ?_}
  rcases extension with rfl | ⟨ty, table, rfl, fresh, _⟩
  · exact live.lookup
  · have different : table.anchor ≠ source := by
      intro same
      have absent := OracleStore.findSkipNewer entries [] row source (same ▸ fresh)
      simp [live.lookup, OracleStore.find] at absent
    simpa [OracleStore.find, different] using live.lookup

/-- A returned publication fixes all coordinates at this anchor. Equal row
sorts and lengths at some other anchor do not imply this equality. -/
theorem RegisteredWord.unique (live : RegisteredWord entries participant source word state)
    {other : Fin size → model.Value row} (second : RegisteredWord entries participant source other state) :
    word = other := by
  have stored := Option.some.inj (live.found.symm.trans second.found)
  have eq : List.ofFn word = List.ofFn other := live.cells.symm.trans (stored ▸ second.cells)
  exact List.ofFn_injective eq

def cellRequest (row : Ty) (source : OracleAnchor) (position : Nat) (location : OracleLocation)
    (expansion : List (OracleAnchor × OracleLocation)) : OracleRead :=
  ⟨.table row none, source, position, location, expansion⟩

theorem readAt (source : OracleAnchor) (word : Fin size → model.Value row)
    (stored : Word model row) (answer : stored.kind.answer = row)
    (shape : OracleStore.validRows stored.kind stored.rows = true)
    (rows : stored.rows = size) (cells : stored.cells = List.ofFn word)
    (index : Fin size) (location : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (state : State model Aux) (found : find state.words row source = some stored) :
    read (E := E) (cellRequest row source index.val location expansion) state =
      ⟨.returned (word index), state, []⟩ := by
  have limit : stored.rows < indexLimit := of_decide_eq_true (Bool.and_eq_true_iff.mp shape).1
  apply read_compatible_cell (cellRequest row source index.val location expansion) state stored (word index) found answer shape
  · simp [cellRequest, OracleStore.validRows, OracleKind.rows, limit]
  · rw [cells, rows]; exact List.length_ofFn
  · exact rows.symm ▸ index.isLt
  · change stored.cells[index.val]? = _
    rw [cells, List.getElem?_ofFn, dite_eq_left index.isLt]
    rfl

theorem RegisteredWord.cell (live : RegisteredWord entries participant source word state)
    (index : Fin size) (location : OracleLocation) (expansion : List (OracleAnchor × OracleLocation))
    (count : Nat) :
    let request := cellRequest row source index.val location expansion
    OracleStore.answer model (read (E := E)) participant entries request (state, count) =
      ⟨.returned (word index), (state, count + 1), [.query request]⟩ := by
  dsimp only
  have limit : live.stored.rows < indexLimit := of_decide_eq_true (Bool.and_eq_true_iff.mp live.shape).1
  have valid : OracleStore.validRows (.table row none) live.registry.rows = true := by
    simp [OracleStore.validRows, OracleKind.rows, live.registryRows, ← live.rows, limit]
  rw [OracleStore.answerOfBase (read (E := E)) participant entries (cellRequest row source index.val location expansion) (state, count) live.registry live.data
    live.lookup live.base live.visible valid (live.registryRows.symm ▸ index.isLt),
    readAt source word live.stored live.answer live.shape live.rows live.cells index location expansion state live.found]
  rfl

/-- A reached source read records its actual cursor, returns the installed
cell and charges exactly once. A misaligned cursor can still refuse. -/
theorem RegisteredWord.sourceQuery {m : Type → Type} [Monad m] [LawfulMonad m]
    (oracles : List (CheckedOracle snapshot domains math))
    (network : Table model → PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : Chooser m model Aux E)
    (state : OracleProtocol.State model snapshot domains math (State model Aux))
    (live : RegisteredWord state.oracle.entries state.oracle.self source word state.oracle.provider)
    (index : Fin size) (participant owner : Nat) (roles : Nat → Nat) (site : OracleLocation)
    (atSelf : participant = state.oracle.self) (active : roles owner = state.oracle.self) :
    actionM oracles network choose (OracleProtocol.tableQuery model row none source index.val participant owner roles site) state =
      pure (OraclePublication.cursorReply site state (.cons (some (ProtocolValue.ofConcrete row (word index))) .nil)
        {state.oracle with queries := state.oracle.queries + 1}
        [.logical (.query (cellRequest row source index.val {site with invocation := state.frame.invocation} []))]) := by
  subst participant
  exact OraclePublication.cursorCell oracles (liftM network) read (publishM choose) row none source index.val owner roles site
    state active (word index) _ _ (live.cell index _ [] state.oracle.queries)

end Zkc.Source.Structured.PublishedWords
