module

public import ZkcArkLibExamples.Fri.VerifierInitialRead
public import ZkcArkLibExamples.Fri.VirtualStore
public import ZkcExamples.Structured.FriCheckRound

@[expose] public section

/-! Interpret the admitted round against its immutable published words.
The same two metadata steps select the actual layer and its virtual fold.
A different published value can never pass the verifier's carried claim. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.VerifierRound
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource (extension)
open FriCheckRound
open OracleProtocol (concrete)
variable {model : DomainModel} {snapshot : Snapshot} {domains : List DomainSpec}
  {math : OracleMathEnvironment} {Aux E : Type} {M : Type → Type} [Monad M] [LawfulMonad M]
abbrev Runtime (model : DomainModel) (snapshot : Snapshot) (domains : List DomainSpec)
    (math : OracleMathEnvironment) (Aux : Type) :=
  OracleRuntimeState model snapshot domains math (PublishedWords.State model Aux)
abbrev State := VerifierInitialRead.State

/-- Facts about the registry, independent of the source frame or chooser.
A sequence operation validates every anchor before selecting one by index. -/
structure Selection (original : Runtime model snapshot domains math Aux)
    (handles : List OracleAnchor) (index rows : Nat) where
  fits : handles.length ≤ 3
  inside : index < handles.length
  visible : handles.all (OracleExecution.visibleReference original kind) = true
  table : OracleStoredTable model snapshot domains math (.field extension)
  lookup : OracleStore.find original.entries (.field extension) handles[index] = some table
  allowed : OracleStore.visible original.self table.holder table.receivers = true
  valid : OracleStore.validRows kind table.rows = true
  size : table.rows = rows

variable (oracles : List (CheckedOracle snapshot domains math))
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

theorem selectionOutcomes {A : Type} (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (original : Runtime model snapshot domains math Aux) (role : original.self = 1)
    (handles : List OracleAnchor) (index rows : Nat) (seqSite shapeSite : OracleLocation)
    (registered : Selection original handles index rows)
    {tail : OracleAnchor → PIR.Process (OracleProtocol.Interface model) A → Prop}
    {process : PIR.Process (OracleProtocol.Interface model) A}
    (head : selectsRows context handles index rows seqSite shapeSite tail process)
    (property : PIR.Outcome A → Runtime model snapshot domains math Aux → Prop)
    (refusal : ∀ store, property (.stopped .refused) store)
    (rest : ∀ p, tail (handles.get ⟨index, registered.inside⟩) p → ∀ current : State model snapshot domains math Aux,
      current.oracle = original → Std.Do.Internal.Ensures (fun record ↦ property record.outcome record.state.oracle)
        (p.runM (PublishedWords.actionM oracles network choose) current))
    (state : State model snapshot domains math Aux) (same : state.oracle = original) :
    Std.Do.Internal.Ensures (fun record ↦ property record.outcome record.state.oracle)
      (process.runM (PublishedWords.actionM oracles network choose) state) := by
  let anchor := handles.get ⟨index, registered.inside⟩
  apply OraclePublication.markedReplyOutcomes oracles (PublishedWords.liftM network) PublishedWords.readM
    (PublishedWords.publishM choose) head seqSite (.cons (concrete model FriBinding.initialSort.type anchor) .nil)
    original original (fun _ ↦ []) _ property refusal _ state same
  · intro current kept
    have active : current.oracle.self ∈ ([0, 1] : List Nat).map context.roles := by simp [kept, role, receiver]
    have visible : handles.all (OracleExecution.visibleReference current.oracle kind) = true := by
      rw [kept]; exact registered.visible
    have law := OraclePublication.sequenceAt oracles (PublishedWords.liftM network) PublishedWords.readM
      (PublishedWords.publishM choose) (.field extension) none 3 [0, 1] context.roles seqSite current 1 (kept ▸ role.symm) handles
      ⟨index, registered.inside⟩ active registered.fits (by decide) visible
    simp only [kept] at law
    with_unfolding_all exact law
  · intro select selected
    apply OraclePublication.markedReplyOutcomes oracles (PublishedWords.liftM network) PublishedWords.readM
      (PublishedWords.publishM choose) (selected anchor) shapeSite (.cons (concrete model .index rows) .nil)
      original original (fun _ ↦ []) _ property refusal _
    · intro current kept
      have lookup : OracleStore.find current.oracle.entries (.field extension) anchor = some registered.table := by
        rw [kept]; exact registered.lookup
      have allowed : OracleStore.visible current.oracle.self registered.table.holder registered.table.receivers = true := by
        rw [kept]; exact registered.allowed
      have law := OraclePublication.rows oracles (PublishedWords.liftM network) PublishedWords.readM
        (PublishedWords.publishM choose) (.field extension) none anchor context.roles shapeSite current 1 (kept ▸ role.symm) registered.table
        lookup registered.valid allowed
      simp only [kept, registered.size] at law
      with_unfolding_all exact law
    · intro shape checked
      exact rest _ checked

private theorem layerOutcomes (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (step : Nat) (carried : FriCheckRound.State model) (layers folds : List OracleAnchor)
    (state : State model snapshot domains math Aux) (role : state.oracle.self = 1)
    (registered : Selection state.oracle layers (wrappingAdd step 1) carried.rows)
    {n : Nat} (word : Fin (2 ^ n) → model.Field extension) (inside : carried.position < 2 ^ n)
    (live : StoredWord.Base state.oracle.entries state.oracle.self
      (layers.get ⟨wrappingAdd step 1, registered.inside⟩) word state.oracle.provider)
    (property : PIR.Outcome (Values (FriBinding.Value model) roundSite.spec.state) → Runtime model snapshot domains math Aux → Prop)
    (refusal : ∀ store, property (.stopped .refused) store)
    (reject : word ⟨carried.position, inside⟩ ≠ carried.expected → property (.stopped .reject)
      {state.oracle with queries := state.oracle.queries + 1})
    (rest : word ⟨carried.position, inside⟩ = carried.expected → ∀ p, checksFold context step carried folds p →
      ∀ current : State model snapshot domains math Aux,
      current.oracle = {state.oracle with queries := state.oracle.queries + 1} →
      Std.Do.Internal.Ensures (fun result ↦ property result.outcome result.state.oracle)
        (p.runM (PublishedWords.actionM oracles network choose) current)) :
    Std.Do.Internal.Ensures (fun result ↦ property result.outcome result.state.oracle)
      ((iteration context step carried layers folds).runM (PublishedWords.actionM oracles network choose) state) := by
  let anchor := layers.get ⟨wrappingAdd step 1, registered.inside⟩
  let index : Fin (2 ^ n) := ⟨carried.position, inside⟩
  apply selectionOutcomes oracles network choose context receiver state.oracle role layers (wrappingAdd step 1)
    carried.rows (site 0) (site 1) registered (installed context receiver step carried layers folds)
    property refusal _ state rfl
  intro p head
  apply OraclePublication.markedReplyOutcomes oracles (PublishedWords.liftM network) PublishedWords.readM
    (PublishedWords.publishM choose) head (site 2) (.cons (concrete model (.field extension) (word index)) .nil)
    state.oracle {state.oracle with queries := state.oracle.queries + 1}
    (fun current ↦ [.logical (.query (Phases.publishedRequest extension anchor carried.position
      {site 2 with invocation := current.frame.invocation} []))]) _
    property refusal _
  · intro current kept
    have live' : StoredWord.Base current.oracle.entries current.oracle.self anchor word current.oracle.provider := by
      rw [kept]; exact live
    have role' : current.oracle.self = 1 := kept ▸ role
    have returned := live'.sourceQuery oracles network choose current index 1 1 context.roles (site 2)
      role'.symm (receiver.trans role'.symm)
    simp only [kept] at returned
    with_unfolding_all exact returned
  · intro next checked current kept
    by_cases equal : word index = carried.expected
    · rw [equal]
      exact rest equal _ checked.2 current kept
    · obtain ⟨marks, equation⟩ := checked.1 (word index) equal
      rw [equation]
      apply OraclePublication.markedOutcomes oracles (PublishedWords.liftM network) PublishedWords.readM
        (PublishedWords.publishM choose) marks (.halt .reject) property refusal _ _ current kept
      intro s same
      exact Zkc.MonadicPostcondition.pure _ _ (same ▸ reject equal)

/-- A well-formed later word may contain a false cell. If it disagrees with
the carried value, every completed record rejects or refuses at a cursor.
The prover and network remain arbitrary throughout. -/
theorem rejectsMismatch (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (step : Nat) (carried : FriCheckRound.State model) (layers folds : List OracleAnchor)
    (state : State model snapshot domains math Aux) (role : state.oracle.self = 1)
    (registered : Selection state.oracle layers (wrappingAdd step 1) carried.rows)
    {n : Nat} (word : Fin (2 ^ n) → model.Field extension) (inside : carried.position < 2 ^ n)
    (live : StoredWord.Base state.oracle.entries state.oracle.self
      (layers.get ⟨wrappingAdd step 1, registered.inside⟩) word state.oracle.provider)
    (mismatch : word ⟨carried.position, inside⟩ ≠ carried.expected) :
    Std.Do.Internal.Ensures (fun result ↦ result.outcome = .stopped .reject ∨ result.outcome = .stopped .refused)
      ((iteration context step carried layers folds).runM (PublishedWords.actionM oracles network choose) state) := by
  exact layerOutcomes oracles network choose context receiver step carried layers folds state role registered
    word inside live (fun out _ ↦ out = .stopped .reject ∨ out = .stopped .refused) (fun _ ↦ Or.inr rfl)
    (fun _ ↦ Or.inl rfl) (fun equal ↦ False.elim (mismatch equal))

section Octic
open ZkcSecurity.Domains.KoalaBear (Octic)
open FriSource (checkedUnit)
local notation "K" => ZkcSecurity.Domains.KoalaBearModel.model

/-- The source machine-index computation at this round agrees with the
mathematical coset pair, including the upper half of the original word. -/
theorem lowCoordinate {m : Nat} (size : m + 1 ≤ 63) (carried : FriCheckRound.State K)
    (rows : carried.rows = 2 ^ (m + 1)) (inside : carried.position < 2 ^ (m + 1)) :
    low carried = carried.position % 2 ^ m := by
  have bounded : 2 ^ (m + 1) < wordModulus := Nat.pow_lt_pow_right (by decide) (by omega)
  simpa only [low, nextRows, rows] using machine_pair_low carried.position m size (inside.trans bounded)

/-- Interpret the virtual cell selected by either the peeled or a later fold.
Its one source query records its own event and the two reads of its parent. -/
theorem virtualOutcomes {A Aux E : Type}
    (network : PublishedWords.Table K → PIR.MonadHandler M (participantInterfaceOn (K).toCarriers) Aux E)
    (choose : PublishedWords.Chooser M K Aux E) (context : ProtocolContext) (receiver : context.roles 1 = 1)
    {n : Nat} (size : n + 1 ≤ 63) (domain : Domain.SmoothCosetFftDomain (n + 1) Octic)
    (shift : Octic) (geometry : ∀ i, domain i = point RetainedDomain.root shift (n + 1) i)
    (word : Fin (2 ^ (n + 1)) → Octic) (beta : Octic) (coordinate : Fin (2 ^ n))
    (source anchor : OracleAnchor) (location : OracleLocation)
    (original : Runtime K checkedUnit.snapshot checkedUnit.domains checkedUnit.math Aux)
    (role : original.self = 1) (registered : VirtualStore.Registered original source anchor word beta shift)
    {after} {process : PIR.Process (OracleProtocol.Interface K) A}
    (head : OracleProtocol.AtMarkedCall (OracleProtocol.tableQuery K (.field extension) none anchor
      coordinate.val 1 1 context.roles location) after process)
    (property : PIR.Outcome A → Runtime K checkedUnit.snapshot checkedUnit.domains checkedUnit.math Aux → Prop)
    (refusal : ∀ store, property (.stopped .refused) store)
    (rest : ∀ next, after next → ∀ state : State K checkedUnit.snapshot checkedUnit.domains checkedUnit.math Aux,
      state.oracle = {original with queries := original.queries + 3} →
      Std.Do.Internal.Ensures (fun record ↦ property record.outcome record.state.oracle)
        ((next (.cons (concrete K (.field extension) (ProximityGap.foldWord domain word 1 beta coordinate)) .nil)).runM
          (PublishedWords.actionM checkedUnit.oracles network choose) state))
    (state : State K checkedUnit.snapshot checkedUnit.domains checkedUnit.math Aux) (same : state.oracle = original) :
    Std.Do.Internal.Ensures (fun record ↦ property record.outcome record.state.oracle)
      (process.runM (PublishedWords.actionM checkedUnit.oracles network choose) state) := by
  let trace := fun (current : State K checkedUnit.snapshot checkedUnit.domains checkedUnit.math Aux) ↦
    let parent := Phases.publishedRequest extension anchor coordinate.val
      {location with invocation := current.frame.invocation} []
    [OracleProtocol.Event.logical (E := E) (.query parent),
     .logical (.query (parent.expand (VirtualReads.leftRequest source (lowIndex coordinate).val))),
     .logical (.query (parent.expand (VirtualReads.rightRequest source (highIndex coordinate).val)))]
  apply OraclePublication.markedReplyOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
    (PublishedWords.publishM choose) head location _ original {original with queries := original.queries + 3}
    trace _ property refusal rest state same
  intro current kept
  have view : VirtualStore.Registered current.oracle source anchor word beta shift := kept ▸ registered
  have atSelf : 1 = current.oracle.self := kept ▸ role.symm
  have law := view.sourceQuery network choose size domain shift geometry word beta coordinate
    source anchor current 1 1 atSelf context.roles location (receiver.trans atSelf)
  simp only [kept] at law
  with_unfolding_all exact law

/-- On matching input the only successful result of the actual iteration
contains the ArkLib fold of that same layer. Both the base and virtual
selection come from the admitted index, and the virtual registry captures
the same word as the direct read. A return preserves the registry and provider
and charges one direct read plus three for the virtual fold. An invalid frame can refuse. -/
theorem matchesFold {Aux E : Type}
    (network : PublishedWords.Table K → PIR.MonadHandler M (participantInterfaceOn (K).toCarriers) Aux E)
    (choose : PublishedWords.Chooser M K Aux E)
    (context : ProtocolContext) (receiver : context.roles 1 = 1) (step : Nat) (carried : FriCheckRound.State K)
    (layers folds : List OracleAnchor)
    (state : State K checkedUnit.snapshot checkedUnit.domains checkedUnit.math Aux) (role : state.oracle.self = 1)
    {m : Nat} (size : m + 1 ≤ 63) (domain : Domain.SmoothCosetFftDomain (m + 1) Octic)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point RetainedDomain.root carried.shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → Octic) (beta : Octic)
    (rows : carried.rows = 2 ^ (m + 1)) (inside : carried.position < 2 ^ (m + 1))
    (layer : Selection state.oracle layers (wrappingAdd step 1) carried.rows)
    (fold : Selection {state.oracle with queries := state.oracle.queries + 1}
      folds (wrappingAdd step 1) (nextRows carried))
    (live : StoredWord.Base (d := extension) (n := m + 1) state.oracle.entries state.oracle.self
      (layers.get ⟨wrappingAdd step 1, layer.inside⟩) word state.oracle.provider)
    (registered : VirtualStore.Registered {state.oracle with queries := state.oracle.queries + 1}
      (layers.get ⟨wrappingAdd step 1, layer.inside⟩) (folds.get ⟨wrappingAdd step 1, fold.inside⟩)
      word beta carried.shift)
    (matchValue : word ⟨carried.position, inside⟩ = carried.expected) :
    let coordinate : Fin (2 ^ m) := ⟨carried.position % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
    let folded := ProximityGap.foldWord domain word 1 beta coordinate
    Std.Do.Internal.Ensures (fun record ↦
      (record.outcome = .returned (advanced carried folded) ∧
        record.state.oracle = {state.oracle with queries := state.oracle.queries + 4}) ∨
      record.outcome = .stopped .refused)
      ((iteration context step carried layers folds).runM (PublishedWords.actionM checkedUnit.oracles network choose)
        state) := by
  dsimp only
  let coordinate : Fin (2 ^ m) := ⟨carried.position % 2 ^ m, Nat.mod_lt _ (by positivity)⟩
  let folded := ProximityGap.foldWord domain word 1 beta coordinate
  let property := fun (out : PIR.Outcome (Values (FriBinding.Value K) roundSite.spec.state)) store ↦
    (out = .returned (advanced carried folded) ∧
      store = {state.oracle with queries := state.oracle.queries + 4}) ∨ out = .stopped .refused
  let afterLayer := {state.oracle with queries := state.oracle.queries + 1}
  let source := layers.get ⟨wrappingAdd step 1, layer.inside⟩
  let anchor := folds.get ⟨wrappingAdd step 1, fold.inside⟩
  refine layerOutcomes checkedUnit.oracles network choose context receiver step carried layers folds state role
    layer word inside live property (fun _ ↦ Or.inr rfl) (fun h ↦ False.elim (h matchValue)) ?_
  intro _ p head
  apply selectionOutcomes checkedUnit.oracles network choose context receiver afterLayer role folds (wrappingAdd step 1)
    (nextRows carried) (site 3) (site 4) fold head property (fun _ ↦ Or.inr rfl) _
  intro q atQuery current atStore
  rw [lowCoordinate size carried rows inside] at atQuery
  apply virtualOutcomes network choose context receiver size domain carried.shift geometry word beta coordinate
    source anchor (site 5) afterLayer role registered atQuery property (fun _ ↦ Or.inr rfl) _ current atStore
  · intro next finished current kept
    obtain ⟨marks, equation⟩ := finished folded
    rw [equation]
    apply OraclePublication.markedOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
      (PublishedWords.publishM choose) marks (.done (advanced carried folded)) property (fun _ ↦ Or.inr rfl) _ _ current kept
    intro s finalStore
    exact Zkc.MonadicPostcondition.pure _ _ (Or.inl ⟨rfl, finalStore⟩)

end Octic
end ZkcSecurity.ArkLib.Fri.VerifierRound
