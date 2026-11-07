module

public import Zkc.Source.Structured.OracleProviderFrame
public import Zkc.Source.Structured.PublishedWordsLaws

@[expose] public section

/-! Complete-record immutability for the constructed PublishedWords source handlers.
Arbitrary lawful monads, arbitrary reached-history choosers, all nominal sorts, and
arbitrary initial words are included. Only the original action interpreter executes.
-/

set_option autoImplicit false
namespace Zkc.Source.Structured.PublishedWords

open OracleProviderFrame Std.Do.Internal

variable {model : DomainModel} {Aux E A : Type} {m : Type → Type}
  [Monad m] [LawfulMonad m]

/-- Ordinary effects may inspect all reached words but can return only auxiliary state. -/
theorem liftM_invariant {I : PIR.Signature} (invariant : Table model → Prop)
    (ordinary : Table model → PIR.MonadHandler m I Aux E)
    (operation : I.Op) (state : State model Aux) (valid : invariant state.words) :
    Ensures (fun result ↦ invariant result.state.words) (liftM ordinary operation state) := by
  apply MonadicPostcondition.of_refinement (do
    let attempt ← ordinary state.words operation state.auxiliary
    pure ⟨⟨attempt.outcome, ⟨state.words, attempt.state⟩, attempt.events⟩, valid⟩)
  simp [liftM]

/-- Every read, including refused reads, leaves the entire provider state unchanged. -/
theorem readM_invariant (invariant : Table model → Prop) (request : OracleRead)
    (state : State model Aux) (valid : invariant state.words) :
    Ensures (fun result ↦ invariant result.state.words) (readM (m := m) (E := E) request state) :=
  MonadicPostcondition.pure _ _ valid

/-- All original source actions before publication leave the whole word table equal.
This is stronger than preserving individual successful lookups. -/
theorem original_actionM_readonly {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : Table model →
      PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (action : OracleProtocolAction model.toCarriers)
    (state : OracleProtocol.State model snapshot domains math (State model Aux)) :
    Ensures (fun result ↦ result.state.oracle.provider.words = state.oracle.provider.words)
      (OracleProcess.actionM model oracles (liftM ordinary) readM action state) := by
  exact actionM_invariant (fun provider : State model Aux ↦
      provider.words = state.oracle.provider.words) oracles (liftM ordinary) readM
    (fun operation current valid ↦ liftM_invariant
      (fun words ↦ words = state.oracle.provider.words) ordinary operation current valid)
    (fun request current valid ↦ readM_invariant (m := m) (E := E)
      (fun words ↦ words = state.oracle.provider.words) request current valid) action state rfl

/-- Instrumentation preserves old words on successful and stopped publications. Its
poststate and events are exactly `complete`'s, including refused duplicate keys. -/
theorem afterM_frame {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} (choose : Chooser m model Aux E)
    (action : OracleProtocolAction model.toCarriers)
    (before : OracleProtocol.State model snapshot domains math (State model Aux))
    (candidate : PIR.Execution (OracleProtocol.State model snapshot domains math (State model Aux))
      (OracleProtocol.Event E) ((OracleProtocol.Interface model).Reply action))
    (candidateFrame : Preserves before.oracle.provider.words candidate.state.oracle.provider.words) :
    Ensures (fun result ↦ Preserves before.oracle.provider.words result.state.oracle.provider.words)
      (OraclePublication.afterM (publishM choose) action before candidate) := by
  unfold OraclePublication.afterM
  split
  · simp only [pure_bind]
    apply MonadicPostcondition.pure
    exact candidateFrame
  · rename_i request present
    obtain ⟨checked, erase⟩ := publishM_framed choose request candidate.state.oracle.provider
    have localLaw : Ensures
        (fun result ↦ Preserves candidate.state.oracle.provider.words result.state.words)
        (publishM choose request candidate.state.oracle.provider) :=
      MonadicPostcondition.of_refinement checked erase
    exact MonadicPostcondition.map localLaw _ (fun publication kept ↦
      complete_frame before candidate publication candidateFrame kept)

/-- The constructed handler's local frame is discharged here, with no caller-supplied
framed handler or word consistency premise. All outcomes retain their full original record. -/
theorem actionM_frame {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : Table model →
      PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : Chooser m model Aux E) (action : OracleProtocolAction model.toCarriers)
    (before : OracleProtocol.State model snapshot domains math (State model Aux)) :
    Ensures (fun result ↦ Preserves before.oracle.provider.words result.state.oracle.provider.words)
      (actionM oracles ordinary choose action before) := by
  apply (original_actionM_readonly oracles ordinary action before).bind
  intro candidate same
  apply afterM_frame choose action before candidate
  rw [same]
  exact .refl _

/-- Every complete result of every original Process retains every old word, including
stopped results. The equality in `Ensures` preserves all outcomes, state fields and events;
outer failure need not produce a record. Initial words may be arbitrary and nonempty. -/
theorem process_frame {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : Table model →
      PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : Chooser m model Aux E)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (before : OracleProtocol.State model snapshot domains math (State model Aux)) :
    Ensures (fun result ↦ Preserves before.oracle.provider.words result.state.oracle.provider.words)
      (process.runM (actionM oracles ordinary choose) before) := by
  apply runM_invariant (fun state ↦ Preserves before.oracle.provider.words state.oracle.provider.words)
    (actionM oracles ordinary choose) _ process before (.refl _)
  intro action current live
  exact (actionM_frame oracles ordinary choose action current).weaken
    (fun result kept ↦ live.trans kept)

/-- Canonically admitted source execution inherits the complete generic frame without any
restriction to a particular protocol, oracle kind, source descriptor, or adversary. -/
theorem sourceRunM_frame {snapshot : Snapshot} {subject : OracleSubject snapshot} {self : Nat}
    (start : OracleStart subject model self (State model Aux))
    (ordinary : Table model →
      PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : Chooser m model Aux E) :
    Ensures (fun result ↦ Preserves start.state.oracle.provider.words
      result.state.oracle.provider.words) (sourceRunM start ordinary choose) :=
  process_frame subject.unit.oracles ordinary choose _ start.state

/-- The exact live membership fact needed by local published-word readback consumers. -/
theorem process_live {snapshot : Snapshot} {domains : List DomainSpec}
    {math : OracleMathEnvironment} (oracles : List (CheckedOracle snapshot domains math))
    (ordinary : Table model →
      PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : Chooser m model Aux E)
    (process : PIR.Process (OracleProtocol.Interface model) A)
    (before : OracleProtocol.State model snapshot domains math (State model Aux))
    (row : Ty) (anchor : OracleAnchor) (stored : Word model row)
    (found : find before.oracle.provider.words row anchor = some stored) :
    Ensures (fun result ↦ find result.state.oracle.provider.words row anchor = some stored)
      (process.runM (actionM oracles ordinary choose) before) := by
  have frame := process_frame oracles ordinary choose process before
  exact frame.weaken (fun result kept ↦ kept.lookup row anchor stored found)

/-- Exact stored membership remains live across an arbitrary admitted source suffix. -/
theorem sourceRunM_live {snapshot : Snapshot} {subject : OracleSubject snapshot} {self : Nat}
    (start : OracleStart subject model self (State model Aux))
    (ordinary : Table model →
      PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : Chooser m model Aux E) (row : Ty) (anchor : OracleAnchor)
    (stored : Word model row)
    (found : find start.state.oracle.provider.words row anchor = some stored) :
    Ensures (fun result ↦ find result.state.oracle.provider.words row anchor = some stored)
      (sourceRunM start ordinary choose) := by
  exact (sourceRunM_frame start ordinary choose).weaken
    (fun result kept ↦ kept.lookup row anchor stored found)

end Zkc.Source.Structured.PublishedWords
