module

public import Zkc.Source.Structured.RegisteredWord
public import Zkc.Source.Structured.PublishedWordsFrame

@[expose] public section

/-! A published word has two lifetimes to check. Its logical registry can
grow by fresh insertions and its immutable provider table can grow under
the chooser. Both properties hold on the records of the actual process. -/
set_option autoImplicit false
namespace Zkc.Source.Structured
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment}

namespace OracleStore

/-- Later entries cannot shadow any anchor present in the earlier registry. -/
def FreshExtension (before after : OracleEntries model snapshot domains math) : Prop :=
  ∃ extra, after = extra ++ before ∧ ∀ anchor, hasAnchor before anchor = true → hasAnchor extra anchor = false

theorem FreshExtension.refl (entries : OracleEntries model snapshot domains math) : FreshExtension entries entries :=
  ⟨[], rfl, fun _ _ ↦ rfl⟩

theorem Extension.fresh {self : Nat} {before after : OracleEntries model snapshot domains math}
    (step : Extension self before after) : FreshExtension before after := by
  rcases step with rfl | ⟨row, table, rfl, fresh, _⟩
  · exact .refl _
  · refine ⟨[⟨row, table⟩], rfl, ?_⟩
    intro anchor present
    have different : table.anchor ≠ anchor := by intro eq; simp [eq, present] at fresh
    simp [hasAnchor, different]

theorem FreshExtension.trans {first middle final : OracleEntries model snapshot domains math}
    (before : FreshExtension first middle) (after : FreshExtension middle final) : FreshExtension first final := by
  obtain ⟨earlier, rfl, earlierFresh⟩ := before
  obtain ⟨later, rfl, laterFresh⟩ := after
  refine ⟨later ++ earlier, List.append_assoc .. |>.symm, ?_⟩
  intro anchor found
  have present : hasAnchor (earlier ++ first) anchor = true := by
    simpa [hasAnchor, List.any_append] using Or.inr (a := hasAnchor earlier anchor = true) found
  simpa [hasAnchor, List.any_append] using And.intro (laterFresh anchor present) (earlierFresh anchor found)

theorem hasAnchor_of_find {entries : OracleEntries model snapshot domains math} {row : Ty}
    {anchor : OracleAnchor} {table : OracleStoredTable model snapshot domains math row}
    (found : find entries row anchor = some table) : hasAnchor entries anchor = true := by
  cases missing : hasAnchor entries anchor with
  | true => rfl
  | false =>
    have absent := findSkipNewer entries [] row anchor missing
    rw [List.append_nil, found] at absent
    contradiction

end OracleStore
namespace PublishedWords
open Std.Do.Internal
variable {Aux E A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

abbrev Runtime (model : DomainModel) (snapshot : Snapshot) (domains : List DomainSpec) (math : OracleMathEnvironment)
    (Aux : Type) := OracleRuntimeState model snapshot domains math (State model Aux)

def RetainsRegistry (before after : Runtime model snapshot domains math Aux) :=
  after.self = before.self ∧ OracleStore.FreshExtension before.entries after.entries

theorem RetainsRegistry.refl (state : Runtime model snapshot domains math Aux) : RetainsRegistry state state :=
  ⟨rfl, .refl _⟩

theorem RetainsRegistry.trans {first middle final : Runtime model snapshot domains math Aux}
    (early : RetainsRegistry first middle) (late : RetainsRegistry middle final) : RetainsRegistry first final :=
  ⟨late.1.trans early.1, early.2.trans late.2⟩

private theorem handlerRegistry (oracles : List (CheckedOracle snapshot domains math))
    (base : PIR.Handler (oracleReadInterface model.toCarriers) (State model Aux) E)
    (action : (OracleProtocol.Interface model).Op)
    (before : OracleProtocol.State model snapshot domains math (State model Aux)) :
    RetainsRegistry before.oracle
      ((OracleProtocol.handler model oracles OracleProcess.refusingOrdinary base action before).state.oracle) := by
  cases action with
  | oracle req =>
    dsimp only [OracleProtocol.handler]
    split
    · exact .refl _
    · exact ⟨OracleExecution.operation_self .., (OracleExecution.operation_extension ..).fresh⟩
  | demand req =>
    change RetainsRegistry _ (OracleStore.demandBase (E := E) _ _ _).state
    rw [OracleStore.demandBase_state]
    exact .refl _
  | _ =>
    dsimp only [OracleProtocol.handler]
    all_goals repeat' first | exact ⟨rfl, .refl _⟩ | split

variable (oracles : List (CheckedOracle snapshot domains math))
  (network : Table model → PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
  (choose : Chooser m model Aux E)

private theorem afterRegistry (action : (OracleProtocol.Interface model).Op)
    (before : OracleProtocol.State model snapshot domains math (State model Aux))
    (candidate : PIR.Execution _ (OracleProtocol.Event E) ((OracleProtocol.Interface model).Reply action))
    (growth : RetainsRegistry before.oracle candidate.state.oracle) :
    Ensures (fun result ↦ RetainsRegistry before.oracle result.state.oracle)
      (OraclePublication.afterM (publishM choose) action before candidate) := by
  unfold OraclePublication.afterM
  split
  · simp only [pure_bind]
    exact Zkc.MonadicPostcondition.pure _ _ growth
  · rename_i req _
    obtain ⟨checked, erase⟩ := publishM_framed choose req candidate.state.oracle.provider
    apply Zkc.MonadicPostcondition.map (Zkc.MonadicPostcondition.of_refinement checked erase)
    rintro ⟨out, provider, events⟩ _
    cases out with
    | stopped why => exact ⟨rfl, .refl _⟩
    | returned token => cases token; exact growth

theorem actionRegistry (action : (OracleProtocol.Interface model).Op)
    (before : OracleProtocol.State model snapshot domains math (State model Aux)) :
    Ensures (fun result ↦ RetainsRegistry before.oracle result.state.oracle)
      (actionM oracles network choose action before) := by
  cases action with
  | oracle req =>
    unfold actionM OraclePublication.actionM
    unfold readM
    rw [OracleProcess.logicalWithPureReads, pure_bind]
    exact afterRegistry choose _ before _ (handlerRegistry oracles read _ before)
  | ordinary op =>
    rw [actionM_ordinary]
    apply Zkc.MonadicPostcondition.of_refinement (do
      let result ← network before.oracle.provider.words op before.oracle.provider.auxiliary
      pure ⟨⟨result.outcome, {before with oracle.provider := ⟨before.oracle.provider.words, result.state⟩},
        result.events.map OracleProtocol.Event.ordinary⟩, ⟨rfl, .refl _⟩⟩)
    simp
  | _ =>
    unfold actionM
    rw [OraclePublication.actionM_local _ _ _ _ _ _ rfl]
    exact Zkc.MonadicPostcondition.pure _ _ (handlerRegistry oracles OracleProcess.refusingBase _ before)

theorem processRegistry (process : PIR.Process (OracleProtocol.Interface model) A)
    (before : OracleProtocol.State model snapshot domains math (State model Aux)) :
    Ensures (fun result ↦ RetainsRegistry before.oracle result.state.oracle)
      (process.runM (actionM oracles network choose) before) := by
  apply OracleProviderFrame.runM_invariant (fun state ↦ RetainsRegistry before.oracle state.oracle)
    (actionM oracles network choose) _ process before (.refl _)
  intro action current earlier
  exact (actionRegistry oracles network choose action current).weaken fun _ later ↦ earlier.trans later

/-- The two parts of a source publication have to survive on the same record.
The logical prefix rules out shadowing even by a table with a different sort. -/
structure PublicationFrame (before after : Runtime model snapshot domains math Aux) : Prop where
  registry : RetainsRegistry before after
  words : Preserves before.provider.words after.provider.words

theorem processPublicationFrame [MonadAttach m] [LawfulMonadAttach m]
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (before : OracleProtocol.State model snapshot domains math (State model Aux)) :
    Ensures (fun record ↦ PublicationFrame before.oracle record.state.oracle)
      (process.runM (actionM oracles network choose) before) := by
  exact (Zkc.MonadicPostcondition.conjunction (processRegistry oracles network choose process before)
    (process_frame oracles network choose process before)).weaken fun _ both ↦ ⟨both.1, both.2⟩

theorem RegisteredWord.transport {before after : Runtime model snapshot domains math Aux}
    {row : Ty} {size : Nat} {source : OracleAnchor} {word : Fin size → model.Value row}
    (live : RegisteredWord (row := row) before.entries before.self source word before.provider)
    (frame : PublicationFrame before after) :
    Nonempty (RegisteredWord (row := row) after.entries after.self source word after.provider) := by
  obtain ⟨self, extra, entries, fresh⟩ := frame.registry
  rw [entries, self]
  exact ⟨live.extend extra (fresh source (OracleStore.hasAnchor_of_find live.lookup)) frame.words⟩

end PublishedWords
end Zkc.Source.Structured
