module

public import ZkcArkLibExamples.Fri.CommitReturn
public import ZkcArkLibExamples.Fri.VerifierCheck

@[expose] public section

/-! The receiver's ordered publications supply Check's entire registry.
A position in either sequence selects the parent or virtual table actually
returned at that iteration. The terminal message comes after these choices. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitReadback
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource (checkedUnit extension)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open CommitIteration (Store)
open CommitLoop (Rounds)
open VerifierPath (charged)
open FriCheckRound (kind)

variable {Aux : Type}
private abbrev Table : Type := OracleStoredTable model checkedUnit.snapshot checkedUnit.domains checkedUnit.math (.field extension)

/-- The three facts sequence selection asks of the particular table. -/
private def Known (store : Store Aux) (anchor : OracleAnchor) (rows : Nat) : Prop :=
  ∃ t : Table, OracleStore.find store.entries kind.answer anchor = some t ∧
    OracleStore.visible store.self t.holder t.receivers = true ∧
    OracleStore.validRows kind t.rows = true ∧ t.rows = rows

private theorem visible {store : Store Aux} {a : OracleAnchor} {rows : Nat} (found : Known store a rows) :
    OracleExecution.visibleReference store kind a = true := by
  obtain ⟨t, lookup, allowed, valid, _⟩ := found
  simp [OracleExecution.visibleReference, lookup, valid, allowed]

private theorem metadata {store : Store Aux} {source view : OracleAnchor} {n : Nat}
    {word : Fin (2 ^ (n+1)) → Octic} {beta shift : Octic} (bounded : n+1 ≤ 5)
    (base : PublishedWords.RegisteredWord (row := .field extension) store.entries store.self source word store.provider)
    (fold : VirtualStore.Registered store source view word beta shift) :
    Known store source (2 ^ (n+1)) ∧ Known store view (2 ^ n) := by
  have fits : 2 ^ (n+1) < indexLimit := Nat.pow_lt_pow_right (by decide) (by omega)
  have half : 2 ^ n < indexLimit := Nat.pow_lt_pow_right (by decide) (by omega)
  refine ⟨⟨base.registry, base.lookup, base.visible, ?_, base.registryRows⟩, ?_⟩
  · simp [OracleStore.validRows, OracleKind.rows, base.registryRows, fits]
  · unfold Known
    rw [fold.entries, OracleStore.findSkipNewer _ _ _ _ fold.fresh]
    simp only [OracleStore.find, VirtualStore.table, ↓reduceDIte, ↓reduceIte]
    exact ⟨_, rfl, fold.allowed, by simp [OracleStore.validRows, OracleKind.rows, half], rfl⟩

private theorem allVisible {store : Store Aux} {n r : Nat} (rounds : Rounds n r) {shift : Octic}
    (live : rounds.Installed store shift) (bound : n ≤ 5) :
    rounds.sources.all (OracleExecution.visibleReference store kind) = true ∧
    rounds.views.all (OracleExecution.visibleReference store kind) = true := by
  induction rounds generalizing shift with
  | empty => exact ⟨rfl, rfl⟩
  | fold source view word beta tail ih =>
    obtain ⟨⟨base⟩, ⟨virtual⟩, later⟩ := live
    have info := metadata bound base virtual
    obtain ⟨sources, views⟩ := ih later (by omega)
    simp only [Rounds.sources, Rounds.views, List.all_cons, visible info.1, visible info.2, sources, views, Bool.and_self, and_self]

private theorem lengths {n r : Nat} (rounds : Rounds n r) :
    rounds.sources.length = r ∧ rounds.views.length = r := by
  induction rounds with
  | empty => exact ⟨rfl, rfl⟩
  | fold source view word beta tail ih =>
    simp only [Rounds.sources, Rounds.views, List.length_cons, ih.1, ih.2, and_self]

private theorem select {store : Store Aux} {anchors earlier tail : List OracleAnchor}
    {anchor : OracleAnchor} {i rows : Nat} (list : anchors = earlier ++ anchor :: tail) (index : i = earlier.length)
    (fits : anchors.length ≤ 3) (all : anchors.all (OracleExecution.visibleReference store kind) = true)
    (found : Known store anchor rows) :
    ∃ s : VerifierRound.Selection store anchors i rows, anchors[i]'(s.inside) = anchor := by
  subst anchors i
  have inside : earlier.length < (earlier ++ anchor :: tail).length := by simp
  have head : (earlier ++ anchor :: tail)[earlier.length] = anchor := by
    rw [List.getElem_append_right (by omega : earlier.length ≤ earlier.length)]
    simp
  obtain ⟨t, lookup, allowed, valid, size⟩ := found
  exact ⟨⟨fits, inside, all, t, by rw [head]; exact lookup, allowed, valid, size⟩, head⟩

private theorem countFrame (store : Store Aux) (q : Nat) : PublishedWords.PublicationFrame store (charged store q) :=
  ⟨⟨rfl, .refl _⟩, .refl _⟩

/-- The inner loop starts with the second layer. Its carried step is the
index of the preceding layer, and the machine addition must be in range. -/
private theorem path {store : Store Aux} {n r : Nat} (rounds : Rounds n r) (cs : List Octic)
    (shift : Octic) (live : rounds.Installed store shift) (bound : n ≤ 5)
    (layers folds earlierLayers earlierViews : List OracleAnchor) (step : Nat)
    (layersEq : layers = earlierLayers ++ rounds.sources) (foldsEq : folds = earlierViews ++ rounds.views)
    (layerIndex : earlierLayers.length = step + 1) (viewIndex : earlierViews.length = step + 1)
    (layerCapacity : layers.length ≤ 3) (viewCapacity : folds.length ≤ 3)
    (layersVisible : layers.all (OracleExecution.visibleReference store kind) = true)
    (viewsVisible : folds.all (OracleExecution.visibleReference store kind) = true) :
    Nonempty (VerifierPath.Registered layers folds (rounds.transcript cs) shift step store) := by
  induction rounds generalizing step shift store earlierLayers earlierViews with
  | empty => exact ⟨.final _ _ _ _⟩
  | @fold n r source view word beta tail ih =>
    obtain ⟨⟨base⟩, ⟨virtual⟩, later⟩ := live
    have facts := metadata bound base virtual
    have small : step + 1 < wordModulus := by
      have room : step + 1 ≤ 3 := by
        have h := layerCapacity
        simp only [layersEq, Rounds.sources, List.length_append, layerIndex, List.length_cons] at h
        omega
      exact lt_of_le_of_lt room (by decide)
    have slot : wrappingAdd step 1 = step + 1 := Nat.mod_eq_of_lt small
    obtain ⟨selectedLayer, layerAt⟩ := select (store := store) layersEq (slot.trans layerIndex.symm) layerCapacity layersVisible facts.1
    have chargedMeta : Known (charged store 1) view (logicalShiftRight (2 ^ (n+1)) 1) :=
      BinaryDomain.halfSize n bound ▸ facts.2
    obtain ⟨selectedView, viewAt⟩ := select (store := charged store 1) foldsEq (slot.trans viewIndex.symm) viewCapacity viewsVisible chargedMeta
    obtain ⟨fold⟩ := virtual.transport (countFrame store 1)
    have liveTail := tail.transport (countFrame store 4) _ later
    have laterPath := ih (store := charged store 4) (shift := shift ^ 2) liveTail (by omega)
      (earlierLayers := earlierLayers ++ [source]) (earlierViews := earlierViews ++ [view]) (step := step + 1)
      (by simpa [Rounds.sources] using layersEq) (by simpa [Rounds.views] using foldsEq)
      (by simp [layerIndex]) (by simp [viewIndex]) layersVisible viewsVisible
    obtain ⟨rest⟩ := laterPath
    rw [pow_two] at rest
    refine ⟨.fold selectedLayer selectedView ?_ ?_ rest⟩
    · simpa only [List.get_eq_getElem, layerAt] using base
    · simpa only [List.get_eq_getElem, layerAt, viewAt] using fold

/-- The publications read by every outer path are read from the same
actual handles and words that Commit produced. This is independent of what
terminal coefficients the receiver was sent and which positions it samples. -/
theorem publication {store : Store Aux} {n r : Nat} {source view : OracleAnchor}
    {word : Fin (2 ^ (n+1)) → Octic} {beta shift : Octic} (tail : Rounds n r) (cs : List Octic)
    (live : (Rounds.fold source view word beta tail).Installed store shift) (bound : n+1 ≤ 5) (count : r+1 ≤ 3) :
    Nonempty (VerifierQueries.Publication store source (source :: tail.sources) (view :: tail.views)
      word beta shift (tail.transcript cs)) := by
  obtain ⟨layersVisible, viewsVisible⟩ := allVisible (.fold source view word beta tail) live bound
  obtain ⟨⟨base⟩, ⟨virtual⟩, later⟩ := live
  have facts := metadata bound base virtual
  have len := lengths tail
  have layerCapacity : (source :: tail.sources).length ≤ 3 := by simpa [len.1] using count
  have viewCapacity : (view :: tail.views).length ≤ 3 := by simpa [len.2] using count
  have size : Known (charged store 1) view (logicalShiftRight (2 ^ (n+1)) 1) :=
    BinaryDomain.halfSize n bound ▸ facts.2
  obtain ⟨selectedView, _⟩ := select (store := charged store 1) (earlier := []) (tail := tail.views) rfl rfl viewCapacity viewsVisible size
  obtain ⟨v⟩ := virtual.transport (countFrame store 1)
  have liveTail := tail.transport (countFrame store 4) _ later
  obtain ⟨rest⟩ := path tail cs (shift ^ 2) liveTail (by omega) _ _ [source] [view] 0 rfl rfl rfl rfl layerCapacity viewCapacity layersVisible viewsVisible
  rw [pow_two] at rest
  refine ⟨⟨base, selectedView, ?_, rest⟩⟩
  simpa only [List.get_eq_getElem, List.getElem_cons_zero] using v

variable {M : Type → Type} [Monad M] [LawfulMonad M] {E : Type}
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

/-- A future invocation of the installed Check on these handles and this
terminal message. Positions may repeat. Any successful result contains
the eight cells and charges precisely 96 reads against the incoming store. -/
def Checked (source view : OracleAnchor) (word : Fin 32 → Octic) (beta shift : Octic)
    (tail : Rounds 4 2) (cs : List Octic) (positions : Fin 8 → Fin 32)
    (context : ProtocolContext) (state : CommitLoop.State Aux) : Prop :=
  let handles : FriBindingExecution.Handles := ⟨source, source :: tail.sources, view :: tail.views⟩
  let inputs := FriCheckAdmission.arguments (model := model) handles shift cs (List.ofFn positions)
  let cells := (List.finRange 8).map fun i ↦ word (positions i)
  let output := Values.cons (OracleProtocol.concrete model .boolean true) (VerifierQueries.packed cells)
  Std.Do.Internal.Ensures (fun result ↦ ∀ values, result.outcome = .returned values →
    Phases.accepts RetainedDomain.root 0 (.fold word beta (tail.transcript cs)) shift positions = true ∧
    values = output ∧ result.state.oracle = charged state.oracle 96)
    ((invokeProtocol (FriSource.verifierTable model) FriSourceBodies.protocol3Signature context 1 inputs).runM
      (VerifierPath.handler network choose) state)

private theorem coefficients {n r : Nat} (rounds : Rounds n r) (cs : List Octic) :
    (rounds.transcript cs).coefficients = cs := by
  induction rounds with
  | empty => rfl
  | fold _ _ _ _ _ ih => exact ih

/-- A registered sequence and the terminal coefficient suffice at any later
checker frame. The positions can be chosen after publication and may repeat. -/
theorem checked {source view : OracleAnchor} {word : Fin 32 → Octic} {beta shift : Octic}
    (tail : Rounds 4 2) (cs : List Octic) (one : cs.length = 1) (positions : Fin 8 → Fin 32)
    (nonzero : shift ≠ 0) (child : ProtocolContext) (receiver : child.roles 1 = 1) (separate : 1 ≠ child.roles 0)
    (after : CommitLoop.State Aux) (role : after.oracle.self = 1)
    (live : (Rounds.fold source view word beta tail).Installed after.oracle shift) :
    Checked network choose source view word beta shift tail cs positions child after := by
  obtain ⟨pub⟩ := publication tail cs live (by decide) (by decide)
  have len := lengths tail
  have correct := VerifierCheck.installed network choose child receiver separate
    ⟨source, source :: tail.sources, view :: tail.views⟩ (by simp [len.1]) (by simp [len.2]) shift nonzero
    positions word beta (tail.transcript cs) (by rw [coefficients]; exact one) after role pub
  simpa only [Checked, coefficients] using correct

/-- A successful Commit fixes the checker inputs in its own output. Only the
future checker frame and sampled positions are supplied by its caller. -/
theorem fromCommit [MonadAttach M] [LawfulMonadAttach M]
    (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (shift : Octic) (nonzero : shift ≠ 0) (service : Nat)
    (before : CommitLoop.State Aux) (role : before.oracle.self = 1) :
    PIR.Process.OnReturn (CommitLoop.handler network choose) before
      (invokeProtocol (FriSource.verifierTable model) FriSourceBodies.protocol0Signature context 1
        (FriCommitAdmission.arguments model shift service))
      (fun out current ↦ ∃ source view word beta, ∃ tail : Rounds 4 2, ∃ cs : List Octic,
        cs.length = 1 ∧ out = FriCommitTerminal.output model source (source :: tail.sources) (view :: tail.views) shift cs ∧
        ∀ (child : ProtocolContext), child.roles 1 = 1 → 1 ≠ child.roles 0 →
        ∀ (after : CommitLoop.State Aux), PublishedWords.PublicationFrame current.oracle after.oracle →
        ∀ positions : Fin 8 → Fin 32, Checked network choose source view word beta shift tail cs positions child after) := by
  apply (CommitReturn.installed network choose context receiver separate shift nonzero service before role).weaken
  intro record law out returned
  obtain ⟨⟨source, view, word, beta, tail, cs, one⟩, output, live, who⟩ := law out returned
  change (Rounds.fold source view word beta tail).Installed record.state.oracle shift at live
  refine ⟨source, view, word, beta, tail, cs, one, output, ?_⟩
  intro child receiver' separate' after frame positions
  exact checked network choose (word := word) tail cs one positions nonzero child receiver' separate' after (frame.registry.1.trans who)
    ((Rounds.fold source view word beta tail).transport frame shift live)

end ZkcSecurity.ArkLib.Fri.CommitReadback
