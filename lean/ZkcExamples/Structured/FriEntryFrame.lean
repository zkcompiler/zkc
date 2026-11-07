module

public import Zkc.Source.Structured.CheckedFrames
public import ZkcExamples.Structured.FriLowDegreeCall

@[expose] public section

/-! Discharge the original root entry checks once, for every private word,
public shift, caller and service. The callee and mark come from the admitted
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
abbrev labels := [(rootSite.site, rootSite.site)]

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
  exact CheckedCall.run subject.unit.oracles (PublishedWords.liftM network) PublishedWords.readM
    (PublishedWords.publishM choose) state labels checked body

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

end ZkcExamples.Structured.FriEntryFrame
