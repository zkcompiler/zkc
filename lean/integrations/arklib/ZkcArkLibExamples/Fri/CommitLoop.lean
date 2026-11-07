module

public import ZkcArkLibExamples.Fri.CommitIteration
public import Zkc.Source.Structured.Bindings.Continuation

@[expose] public section

/-! The ordered publications made by the receiver's bounded Commit loop.
Each successful iteration chooses its own word. Later rounds can extend
the registry, but cannot shadow the preceding word or its captured fold. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitLoop
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource (extension checkedUnit)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open OracleProtocol (concrete)
open FriCommitRound (roundSite)
open CommitIteration (Store LoopState)
open Std.Do.Internal (Ensures)

inductive Rounds : Nat → Nat → Type where
  | empty (n : Nat) : Rounds n 0
  | fold {n r : Nat} (source view : OracleAnchor) (word : Fin (2 ^ (n + 1)) → Octic)
      (beta : Octic) (tail : Rounds n r) : Rounds (n + 1) (r + 1)

def Rounds.sources : {n r : Nat} → Rounds n r → List OracleAnchor
  | _, _, .empty _ => []
  | _, _, .fold source _ _ _ tail => source :: tail.sources

def Rounds.views : {n r : Nat} → Rounds n r → List OracleAnchor
  | _, _, .empty _ => []
  | _, _, .fold _ view _ _ tail => view :: tail.views

/-- Location of the first word published by this suffix of the repeat. -/
def Rounds.First (prior current : PublishedWords.Table model) : {n r : Nat} → Rounds n r → Prop
  | _, _, .empty _ => True
  | _, _, .fold source _ word _ _ =>
    PublishedWords.PublishedAfter (row := .field extension) prior current source (List.ofFn word)

def Rounds.Installed {Aux : Type} (store : Store Aux) : {n r : Nat} → Rounds n r → Octic → Prop
  | _, _, .empty _, _ => True
  | _, _, .fold source view word beta tail, shift =>
    Nonempty (PublishedWords.RegisteredWord (row := .field extension) store.entries store.self source word store.provider) ∧
    Nonempty (VirtualStore.Registered store source view word beta shift) ∧ tail.Installed store (shift ^ 2)

theorem Rounds.transport {Aux n r} (rounds : Rounds n r) {before after : Store Aux}
    (frame : PublishedWords.PublicationFrame before after) (shift : Octic)
    (live : rounds.Installed before shift) : rounds.Installed after shift := by
  induction rounds generalizing shift with
  | empty => trivial
  | fold source view word beta tail ih =>
    obtain ⟨⟨parent⟩, ⟨virtual⟩, later⟩ := live
    exact ⟨parent.transport frame, virtual.transport frame, ih _ later⟩

def Rounds.endingShift : {n r : Nat} → Rounds n r → Octic → Octic
  | _, _, .empty _, shift => shift
  | _, _, .fold _ _ _ _ tail, shift => tail.endingShift (shift ^ 2)

/-- Terminal coefficients are supplied only after the publication loop.
The mathematical words and challenges were already fixed by the loop. -/
def Rounds.transcript {n r : Nat} (rounds : Rounds n r) (coefficients : List Octic) : Layers Octic n r :=
  match rounds with
  | .empty _ => .final coefficients
  | .fold _ _ word beta tail => .fold word beta (tail.transcript coefficients)

noncomputable def packed (n : Nat) (shift : Octic) (layers folds : List OracleAnchor) : LoopState :=
  .cons none (.cons none (.cons (concrete model FriBinding.layersSort.type layers)
    (.cons (concrete model FriBinding.layersSort.type folds) (.cons (concrete model .index (2 ^ n))
      (.cons (concrete model (.field extension) shift) (.cons (concrete model (.field extension)
        (RetainedDomain.root n)) .nil))))))

noncomputable def captures (service : Nat) : Values (FriBinding.Value model) roundSite.spec.captures :=
  .cons (concrete model (.field extension) ((2 : Octic)⁻¹ : Octic))
    (.cons (concrete model (.service FriScalarLoop.contract) service) .nil)

private theorem mask (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (n : Nat) (shift : Octic) (layers folds : List OracleAnchor) :
    maskValues 1 (context.mapScopes roundSite.spec.stateScopes) (packed n shift layers folds) =
      packed n shift layers folds := by
  change maskValues 1 ([[0], [0], [0,1], [0,1], [0,1], [0,1], [0,1]].map (List.map context.roles)) _ = _
  simp [packed, maskValues, Participant.restrict, receiver]

noncomputable abbrev callback (context : ProtocolContext) (service : Nat) :=
  roundSite.maskedIteration (FriSource.verifierAlgebra model) (FriSource.verifierTable model)
    context 1 (captures service)

def Returned {Aux : Type} (n r : Nat) (shift : Octic) (layers folds : List OracleAnchor)
    (prior : PublishedWords.Table model) (out : PIR.Outcome LoopState) (store : Store Aux) : Prop :=
  ∀ values, out = .returned values → ∃ rounds : Rounds (n + r) r,
    rounds.First prior store.provider.words ∧ rounds.Installed store shift ∧ store.self = 1 ∧ values =
      packed n (rounds.endingShift shift) (layers ++ rounds.sources) (folds ++ rounds.views)

variable {M : Type → Type} [Monad M] [LawfulMonad M] {Aux E : Type}
  (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
  (choose : PublishedWords.Chooser M model Aux E)

abbrev State (Aux : Type) :=
  OracleProtocol.State model checkedUnit.snapshot checkedUnit.domains checkedUnit.math (PublishedWords.State model Aux)
abbrev handler := PublishedWords.actionM checkedUnit.oracles network choose

set_option maxRecDepth 6000 in
private theorem callbackReturns [MonadAttach M] [LawfulMonadAttach M] (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (separate : 1 ≠ context.roles 0) (step n : Nat) (bound : n + 1 ≤ 5) (shift : Octic) (nz : shift ≠ 0)
    (layers folds : List OracleAnchor) (service : Nat) (before : State Aux) (role : before.oracle.self = 1) :
    Ensures (fun rec ↦ CommitIteration.Completed n shift layers folds before.oracle.provider.words rec.outcome rec.state.oracle)
      ((callback context service (packed (n + 1) shift layers folds) step).runM (handler network choose) before) := by
  unfold callback Bindings.RepeatSite.maskedIteration
  dsimp only
  rw [mask context receiver, PIR.runM_bind]
  refine Ensures.bind (P := fun rec ↦ CommitIteration.Completed n shift layers folds before.oracle.provider.words rec.outcome rec.state.oracle) ?_ ?_
  · apply OraclePublication.iterationOutcomes checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
      (PublishedWords.publishM choose) roundSite.site step
      (FriCommitRound.iteration model context step (CommitCaptures.roundState n shift layers folds service))
      (CommitIteration.Completed n shift layers folds before.oracle.provider.words) (fun _ _ eq ↦ by cases eq) before
    intro state same
    simpa only [same, PublishedWords.actionM] using CommitIteration.installed network choose context receiver separate step n bound shift nz layers folds service
      state (same ▸ role)
  · rintro ⟨out, after, events⟩ completed
    cases out with
    | stopped why => exact Zkc.MonadicPostcondition.pure _ _ (fun _ eq ↦ by cases eq)
    | returned values =>
      obtain ⟨source, word, beta, position, view, rfl, who, virtual, live⟩ := completed values rfl
      simp only [PIR.Execution.followM, PIR.Process.runM, pure_bind]
      apply Zkc.MonadicPostcondition.pure
      intro out eq
      have same := mask context receiver n (shift ^ 2) (layers ++ [source]) (folds ++ [view])
      change PIR.Outcome.returned (maskValues 1 _ (packed n (shift ^ 2) (layers ++ [source]) (folds ++ [view]))) = _ at eq
      rw [same] at eq
      cases eq
      exact ⟨source, word, beta, position, view, rfl, who, virtual, live⟩

/-- At any reached suffix of the installed repeat, all earlier base and
virtual handles survive the later iterations under the same participant.
Every word is fixed by its own send and every challenge follows that send. -/
theorem fromStep [MonadAttach M] [LawfulMonadAttach M]
    (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (n r step : Nat) (bound : n + r ≤ 5) (shift : Octic) (nz : shift ≠ 0)
    (layers folds : List OracleAnchor) (service : Nat) (before : State Aux) (role : before.oracle.self = 1) :
    Ensures (fun rec ↦ Returned n r shift layers folds before.oracle.provider.words rec.outcome rec.state.oracle)
      ((Finite.fold (callback context service) (List.range' step r)
        (packed (n+r) shift layers folds)).runM (handler network choose) before) := by
  induction r generalizing step shift layers folds before with
  | zero =>
    apply Zkc.MonadicPostcondition.pure
    intro values eq
    cases eq
    exact ⟨.empty n, trivial, trivial, role, by simp [Rounds.endingShift, Rounds.sources, Rounds.views]⟩
  | succ r ih =>
    rw [List.range'_succ, Finite.fold, PIR.runM_bind]
    refine Ensures.bind (P := fun rec ↦ CommitIteration.Completed (n+r) shift layers folds before.oracle.provider.words rec.outcome rec.state.oracle)
      (callbackReturns network choose context receiver separate step (n+r) bound shift nz layers folds service before role) ?_
    rintro ⟨out, after, events⟩ completed
    cases out with
    | stopped why => exact Zkc.MonadicPostcondition.pure _ _ (fun _ eq ↦ by cases eq)
    | returned values =>
      obtain ⟨source, word, beta, position, view, rfl, who, ⟨virtual⟩, ⟨parent⟩⟩ := completed values rfl
      simp only [PIR.Execution.followM]
      have tail := ih (step + 1) (by omega) (shift ^ 2) (pow_ne_zero _ nz)
        (layers ++ [source]) (folds ++ [view]) after who
      have frame := PublishedWords.processPublicationFrame checkedUnit.oracles network choose
        (Finite.fold (callback context service) (List.range' (step + 1) r)
          (packed (n+r) (shift ^ 2) (layers ++ [source]) (folds ++ [view]))) after
      apply Zkc.MonadicPostcondition.map (Zkc.MonadicPostcondition.conjunction tail frame)
      intro result both values returned
      obtain ⟨later, _, live, role, state⟩ := both.1 values returned
      exact ⟨.fold source view word beta later, position.transport both.2.words,
        ⟨parent.transport both.2, virtual.transport both.2, live⟩, role, by
          simpa only [Rounds.endingShift, Rounds.sources, Rounds.views, List.append_assoc, List.singleton_append]
            using state⟩

/-- The exact three-round source operation. Its typed inputs are the
obligation of Commit's ingress, including the verifier's shift and service. -/
theorem installed [MonadAttach M] [LawfulMonadAttach M]
    (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (env : Environment (FriBinding.Value model) roundSite.context) (shift : Octic) (nz : shift ≠ 0) (service : Nat)
    (inputs : Operands.eval env roundSite.operands = .cons (concrete model .index 3)
      ((packed 5 shift [] []).append (captures service)))
    (before : State Aux) (role : before.oracle.self = 1) :
    Ensures (fun rec ↦ Returned 2 3 shift [] [] before.oracle.provider.words rec.outcome rec.state.oracle)
      ((roundSite.iterations ((FriSource.verifierAlgebra model).meaning (FriSource.verifierTable model) context 1)
        env).runM (handler network choose) before) := by
  rw [roundSite.maskedIterations (FriSource.verifierAlgebra model) (FriSource.verifierTable model) context 1 env
    (concrete model .index 3) (packed 5 shift [] []) (captures service) inputs (by
      change ([0,1].map context.roles).contains 1 = true
      simp [receiver]) (ProtocolValue.toConcrete_ofConcrete (carriers := model.toCarriers) .index 3) (by decide),
    mask context receiver, List.range_eq_range']
  exact fromStep network choose context receiver separate 2 3 0 (by decide) shift nz [] [] service before role

end ZkcSecurity.ArkLib.Fri.CommitLoop
