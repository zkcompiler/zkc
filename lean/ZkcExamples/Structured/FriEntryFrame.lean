module

public import Zkc.Source.Structured.CheckedFrames
public import ZkcExamples.Structured.FriLowDegreeCall

@[expose] public section

/-! Discharge the original root entry checks once, for every private word,
public shift and service. The callee and mark come from the admitted
source. The child still executes its own checks, including its exit. -/
set_option autoImplicit false
set_option maxRecDepth 6000
noncomputable section
namespace ZkcExamples.Structured.FriEntryFrame
open Zkc.Source Zkc.Source.Structured FriSource FriSourceBodies
open OracleProtocol (Frame advanceMarks withMarks)
open OraclePublication (CheckedCall)

abbrev snapshot := subject.unit.snapshot
def root : Frame :=
  let index := snapshot.definitions.findIdx (·.name == snapshot.entry)
  {invocation := ⟨index, []⟩, definition := index}
/-- Pair each lexical mark from the retained region with its dynamic label. -/
def markLabels (caller : FriPhaseCalls.Caller) (site : CallSite)
    (found : (caller.callMarks site).isSome := by decide +kernel) : List (String × String) :=
  ((caller.callMarks site).get found).map (fun label ↦
    (label, qualifyProtocolSite caller.context.applicationPrefix label))

def labels := markLabels ⟨{}, (FriPhaseCalls.schedule runBody.erase).get (by decide +kernel)⟩ rootSite

private theorem rootLabels : labels = [(rootSite.site, rootSite.site)] := by kernel_rfl

def checked : CheckedCall snapshot root (labels.map Prod.fst) protocol5Signature rootSite.site :=
  (CheckedCall.check snapshot root (labels.map Prod.fst) protocol5Signature rootSite.site).get (by decide +kernel)

variable {model : DomainModel} {Aux E A : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

theorem run (self : Fin 2) (privateWord : List (model.Field extension)) (shift : model.Field extension)
    (rounds queries service : Nat) (aux : Aux)
    (network : PublishedWords.Table model → PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : PublishedWords.Chooser m model Aux E) (body : PIR.Process (OracleProtocol.Interface model) A) :
    let state := (start self privateWord shift rounds queries service aux).state
    let handler := PublishedWords.actionM subject.unit.oracles network choose
    ((withMarks labels (.done ())).bind (fun _ ↦ OracleProtocol.enter model (.application protocol5Signature rootSite.site)
        body)).runM handler state = (do
      let result ← (body.bind fun value ↦ .call .leave fun _ ↦ .done value).runM handler
        {state with frame := checked.entered, parents := [checked.marked]}
      pure {result with events := [.mark rootSite.site] ++ result.events}) := by
  intro state handler
  have eqn := CheckedCall.run subject.unit.oracles (PublishedWords.liftM network) PublishedWords.readM
    (PublishedWords.publishM choose) state labels checked body
  have logged : labels.map (fun p ↦ OracleProtocol.Event.mark (E := E) p.2) = [.mark rootSite.site] := by
    rw [rootLabels]
    rfl
  rw [logged] at eqn
  exact eqn

/-- At the verifier entry the checked mark and application always reach the
selected low-degree body. Keep its complete record, its exit, and the final
caller mask when passing the result back to the root. -/
theorem verifier (shift : model.Field extension) (rounds queries service : Nat) (aux : Aux)
    (network : PublishedWords.Table model → PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : PublishedWords.Chooser m model Aux E) :
    let initial := (start (model := model) 1 [] shift rounds queries service aux).state
    let handler := PublishedWords.actionM subject.unit.oracles network choose
    let child := (FriLowDegreeCall.program model shift rounds queries service).bind fun out ↦
      .done (maskValues 1 (lowDegreeContext.mapScopes protocol5Signature.outputScopes) out)
    FriSource.verifier shift rounds queries service aux network choose = (do
      let result ← (child.bind fun value ↦ .call .leave fun _ ↦ .done value).runM handler
        {initial with frame := checked.entered, parents := [checked.marked]}
      let observed := {result with events := [OracleProtocol.Event.mark (E := E) rootSite.site] ++ result.events}
      observed.followM fun out ↦ (PIR.Process.done (I := OracleProtocol.Interface model)
        (maskValues 1 runSignature.outputScopes (.cons (out.get .here) .nil))).runM handler) := by
  intro initial handler child
  apply (FriLowDegreeCall.verifier model shift rounds queries service aux network choose).trans
  let call := (withMarks labels (.done ())).bind fun _ ↦
    OracleProtocol.enter model (.application protocol5Signature rootSite.site) child
  let finish := fun (out : Values (Component (verifierValue model)) protocol5Signature.outputs) ↦
    PIR.Process.done (I := OracleProtocol.Interface model) (maskValues 1 runSignature.outputScopes (.cons (out.get .here) .nil))
  change (call.bind finish).runM handler initial = _
  rw [PIR.runM_bind]
  have eqn := run 1 [] shift rounds queries service aux network choose child
  change call.runM handler initial = _ at eqn
  rw [eqn, bind_assoc]
  simp only [pure_bind]
  rfl

abbrev commit := FriSourceCalls.commitment
def commitLabels := markLabels FriLowDegreeCall.caller commit

def commitEntry : CheckedCall snapshot checked.entered (commitLabels.map Prod.fst) commit.signature commit.site :=
  (CheckedCall.check snapshot checked.entered (commitLabels.map Prod.fst) commit.signature commit.site).get
    (by decide +kernel)

/-- The actual first nested call in LowDegree reaches Commit. Its mark list
and role substitution are read from that caller's region. The parent stack
and the complete post-state of the selected body are visible to the suffix. -/
theorem commitCall (network : PublishedWords.Table model →
    PIR.MonadHandler m (participantInterfaceOn model.toCarriers) Aux E)
    (choose : PublishedWords.Chooser m model Aux E)
    (args : Values (FriBinding.Value model) commit.signature.inputs)
    (store : OracleRuntimeState model snapshot subject.unit.domains subject.unit.math (PublishedWords.State model Aux))
    (parents : List Frame) :
    let state : OracleProtocol.State model snapshot subject.unit.domains subject.unit.math (PublishedWords.State model Aux) :=
      ⟨store, checked.entered, parents⟩
    let handler := PublishedWords.actionM subject.unit.oracles network choose
    let child := invokeProtocol (verifierTable model) commit.signature (commit.childContext lowDegreeContext) 1 args
    (FriLowDegreeCall.caller.call commit args).runM handler state = (do
      let result ← (child.bind fun value ↦ .call .leave fun _ ↦ .done value).runM handler
        {state with frame := commitEntry.entered, parents := commitEntry.marked :: parents}
      pure {result with events := commitLabels.map (fun p ↦ OracleProtocol.Event.mark (E := E) p.2) ++ result.events}) := by
  intro state handler child
  exact CheckedCall.run subject.unit.oracles (PublishedWords.liftM network) PublishedWords.readM
    (PublishedWords.publishM choose) state commitLabels commitEntry child

end ZkcExamples.Structured.FriEntryFrame
