module

public import ZkcArkLibExamples.Fri.CommitBody
public import ZkcExamples.Structured.FriCommitReply

@[expose] public section

/-! Relate the receiver's actual output tuple to the words it published.
The terminal message may be adversarial. Its length is checked after
receipt and the initial handle is selected from the real layer sequence. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitReturn
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource FriSourceViews FriSourceBodies FriCommitTerminal
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open FriCommitRound (roundSite)
open CommitLoop (State Rounds handler)
open OracleProtocol (concrete)

variable {M : Type → Type} [Monad M] [LawfulMonad M] [MonadAttach M] [LawfulMonadAttach M]
  {Aux E : Type} (network : PublishedWords.Table model →
    PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E) (choose : PublishedWords.Chooser M model Aux E)

private abbrev meaning (context : ProtocolContext) := (verifierAlgebra model).meaning (verifierTable model) context 1

private abbrev reply (cs : List Octic) :=
  Values.cons (Value := FriBinding.Value model) (ty := .vector extension) (concrete model (.vector extension) cs) .nil

set_option maxRecDepth 6000 in
omit [MonadAttach M] [LawfulMonadAttach M] in
private theorem received (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (separate : 1 ≠ context.roles 0) (live : Values (FriBinding.Value model) delivery.context) (before : State Aux) :
    PIR.Process.OnReturn (handler network choose) before ((meaning context).operation delivery.op
      (delivery.arguments.eval live.get) (delivery.callbacks.denote (meaning context)))
      (fun values _ ↦ ∃ cs : List Octic, values = reply cs) := by
  let receive := Participant.Action.receive (Value := model.Value) (services := services) (.vector extension)
    (qualifyProtocolSite context.applicationPrefix messageSite) (context.roles 0)
  have eq : (meaning context).operation delivery.op (delivery.arguments.eval live.get) (delivery.callbacks.denote (meaning context)) =
      .call (.ordinary receive) (fun cs ↦ .done (reply cs)) :=
    OracleProtocol.receiveConcrete (context := context) (owner := 1) (sender := 0) (site := messageSite)
      model separate.symm receiver _
  rw [eq]
  change PIR.Process.OnReturn _ _ ((PIR.Process.call (I := OracleProtocol.Interface model) (.ordinary receive) .done).bind
    (fun cs ↦ .done (reply cs))) _
  apply PIR.Process.OnReturn.bindAny
  intro cs state
  exact Zkc.MonadicPostcondition.pure _ _ (fun values eq ↦ ⟨cs, (PIR.Outcome.returned.inj eq).symm⟩)

/-- The first base word, its virtual child and the later rounds of this
Commit execution. Later base words can be chosen after previous challenges. -/
structure Publication where
  source : OracleAnchor
  view : OracleAnchor
  word : Fin 32 → Octic
  beta : Octic
  tail : Rounds 4 2
  coefficients : List Octic
  singleton : coefficients.length = 1

def Publication.rounds (pub : Publication) : Rounds 5 3 := .fold pub.source pub.view pub.word pub.beta pub.tail

def Publication.handles (pub : Publication) : FriBindingExecution.Handles :=
  ⟨pub.source, pub.source :: pub.tail.sources, pub.view :: pub.tail.views⟩

def Publication.output (pub : Publication) (shift : Octic) :=
  FriCommitTerminal.output model pub.source pub.handles.layers pub.handles.folds shift pub.coefficients

def Publication.Returned {Aux : Type} (pub : Publication) (prior : PublishedWords.Table model) (shift : Octic)
    (out : Values (FriBinding.Value model) protocol0Signature.outputs) (store : CommitIteration.Store Aux) : Prop :=
  out = pub.output shift ∧ pub.rounds.First prior store.provider.words ∧ pub.rounds.Installed store shift ∧ store.self = 1

def Result {Aux : Type} (prior : PublishedWords.Table model) (shift : Octic) (out : Values (FriBinding.Value model) protocol0Signature.outputs)
    (store : CommitIteration.Store Aux) : Prop := ∃ pub : Publication, pub.Returned prior shift out store

theorem Publication.mask (pub : Publication) (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (separate : 1 ≠ context.roles 0) (shift : Octic) :
    maskValues 1 (context.mapScopes protocol0Signature.outputScopes) (pub.output shift) = pub.output shift := by
  apply (maskValues_mapScopes context 1 1 protocol0Signature.outputScopes _ _).trans
  · rfl
  · intro scope member
    have used : ∀ s ∈ protocol0Signature.outputScopes, s = [0] ∨ s = [1] ∨ s = [0,1] := by decide +kernel
    rcases used scope member with rfl | rfl | rfl <;> simp [receiver, separate]

set_option maxRecDepth 6000 in
theorem terminal (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (prior : PublishedWords.Table model) (shift : Octic) (entry : Values (FriBinding.Value model) roundSite.context) (before : State Aux) (rounds : Rounds 5 3)
    (offset : entry.get FriCommitAdmission.shiftPort = concrete model (.field extension) shift)
    (rows : entry.get FriCommitAdmission.sizePort = concrete model .index 32)
    (count : entry.get FriCommitAdmission.countPort = concrete model .index 3)
    (position : rounds.First prior before.oracle.provider.words) (installed : rounds.Installed before.oracle shift) (role : before.oracle.self = 1) :
    PIR.Process.OnReturn (handler network choose) before (roundSite.next.denote ((verifierAlgebra model).meaning (verifierTable model) context 1)
      (Environment.prepend entry.get (CommitLoop.packed 2 (rounds.endingShift shift) rounds.sources rounds.views)))
      (fun out state ↦ ∃ pub : Publication, pub.rounds = rounds ∧ pub.Returned prior shift out state.oracle) := by
  cases rounds with
  | fold source view word beta tail =>
    let rounds := Rounds.fold source view word beta tail
    let loop := CommitLoop.packed 2 (rounds.endingShift shift) rounds.sources rounds.views
    let env := @Environment.prepend _ _ _ _ entry.get loop
    change PIR.Process.OnReturn _ _ (FriCommitRound.roundNext.denote (meaning context) env) _
    rw [delivery.exactRun]
    apply PIR.Process.OnReturn.bind (head := PublishedWords.withPublicationFrame checkedUnit.oracles network choose
      (delivery.retains (meaning context) env (handler network choose) before))
    rintro live state ⟨kept, frame⟩
    have layers : live.get layersPort = concrete model FriBinding.layersSort.type (source :: tail.sources) :=
      (kept (.there (.there .here))).trans rfl
    have views : live.get foldsPort = concrete model FriBinding.layersSort.type (view :: tail.views) :=
      (kept (.there (.there (.there .here)))).trans rfl
    have geometry (ty : Ty) (ref : Var roundSite.context ty) :
        live.get (delivery.inherited (ref.weakenPrefix roundSite.spec.state)) = entry.get ref :=
      (kept _).trans (Environment.prepend_weakenPrefix entry.get loop ref)
    rw [Region.denote_letOp_values]
    apply PIR.Process.OnReturn.bind (head := PublishedWords.withPublicationFrame checkedUnit.oracles network choose (received network choose context receiver separate live state))
    rintro message current ⟨⟨cs, rfl⟩, later⟩
    have self := later.registry.1.trans (frame.registry.1.trans role)
    have reg := rounds.transport later shift (rounds.transport frame shift installed)
    have endLaw := FriCommitReply.installed checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.readM
      (PublishedWords.publishM choose) current.oracle context receiver separate self live source tail.sources
      (view :: tail.views) shift layers views ((geometry _ _).trans offset) ((geometry _ _).trans rows)
      ((geometry _ _).trans count) cs current rfl
    rw [finish_exact]
    change PublishedWords.PublishedAfter (row := .field extension) prior before.oracle.provider.words source (List.ofFn word) at position
    have chronology := position.transport (frame.words.trans later.words)
    exact endLaw.weaken fun rec h out returned ↦
      ⟨⟨source, view, word, beta, tail, cs, (h.2 out returned).1⟩, rfl, (h.2 out returned).2,
       by rw [h.1]; exact chronology, by rw [h.1]; exact reg, h.1 ▸ self⟩

/-- Every returning receiver Commit exposes these six registered tables,
the original geometry, and one coefficient from its own terminal message. -/
theorem installed (context : ProtocolContext) (receiver : context.roles 1 = 1) (separate : 1 ≠ context.roles 0)
    (shift : Octic) (nz : shift ≠ 0) (service : Nat) (before : State Aux) (role : before.oracle.self = 1) :
    PIR.Process.OnReturn (handler network choose) before (invokeProtocol (verifierTable model) protocol0Signature
      context 1 (FriCommitAdmission.arguments model shift service)) (fun out state ↦ Result before.oracle.provider.words shift out state.oracle) := by
  rw [CommitBody.invokeReceiver context receiver shift service]
  apply PIR.Process.OnReturn.bind (middle := fun out state ↦ Result before.oracle.provider.words shift out state.oracle)
  · exact CommitBody.afterRounds network choose context receiver separate shift nz service before role (fun out state ↦ Result before.oracle.provider.words shift out state.oracle)
      (fun entry after rounds offset rows count position live self ↦
        (terminal network choose context receiver separate before.oracle.provider.words shift entry after rounds offset rows count position live self).weaken
          fun _ law out returned ↦ let ⟨pub, _, result⟩ := law out returned; ⟨pub, result⟩)
  · rintro out after ⟨pub, rfl, position, registered, self⟩
    have masked := pub.mask context receiver separate shift
    exact Zkc.MonadicPostcondition.pure _ _ (fun value eq ↦
      ⟨pub, (PIR.Outcome.returned.inj eq).symm.trans masked, position, registered, self⟩)

end ZkcSecurity.ArkLib.Fri.CommitReturn
