module

public import ZkcArkLibExamples.Fri.VirtualStore
public import ZkcExamples.Structured.FriCommitRound
public import Zkc.Source.Structured.OracleLocalAction
public import Zkc.Source.Structured.OracleVirtualInstallation
public import Zkc.Source.Structured.OracleQueryDerivation

@[expose] public section

/-! The Commit receiver constructs a virtual table from the earlier word
and the delivered challenge. Successful installation supplies the registry
used by the later verifier. Invalid or duplicate captures retain the source
handler's failure. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitVirtual
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open FriSource (extension checkedUnit)
open FriSourceBodies (oracle0Signature)
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open VirtualReads (kind)
variable {Aux E : Type}

noncomputable def foldCaptures (n : Nat) (source : OracleAnchor) (beta shift : Octic) :=
  VirtualReads.captures model source beta (2 ^ (n + 1)) (2 ^ n) shift
    (RetainedDomain.root (n + 1)) (shift⁻¹ : Octic) ((RetainedDomain.root (n + 1))⁻¹ : Octic) ((2 : Octic)⁻¹ : Octic)

private theorem rows (n : Nat) (source : OracleAnchor) (beta shift : Octic) :
    OracleExecution.declaredRows oracle0Signature (foldCaptures n source beta shift) = some (2 ^ n) := rfl

set_option maxRecDepth 6000 in
/-- The selected virtual operation checks its own bounds, freshness and
parent accessibility. Only a successful return yields the new view. The
older prefix is precisely the registry before this action. -/
theorem registered (n : Nat) (source : OracleAnchor) (word : Fin (2 ^ (n + 1)) → Octic) (beta shift : Octic)
    (site : OracleLocation) (roles : Nat → Nat) (receiver : roles 1 = 1)
    (before : OracleRuntimeState model checkedUnit.snapshot checkedUnit.domains checkedUnit.math
      (PublishedWords.State model Aux)) (self : before.self = 1)
    (parent : PublishedWords.RegisteredWord (row := .field extension) before.entries before.self source word before.provider) :
    let result := OracleExecution.operation model checkedUnit.oracles (OracleProcess.refusingBase (E := E))
      site 1 roles (.virtual oracle0Signature 0 [1]) (ProtocolValue.embedComponents (foldCaptures n source beta shift).present) before
    ∀ reply, result.outcome = .returned reply →
      reply = .cons (OracleProtocol.concrete model (.oracle kind) site.anchor) .nil ∧
      Nonempty (VirtualStore.Registered result.state source site.anchor word beta shift) ∧
      Nonempty (PublishedWords.RegisteredWord (row := .field extension) result.state.entries result.state.self source word result.state.provider) ∧ result.state.self = 1 := by
  have visible : OracleStore.visible before.self (roles 0) ([1].map roles) = true := by
    simp [OracleStore.visible, self, receiver]
  dsimp only
  intro reply success
  let op := OracleExecution.virtual_returned checkedUnit.oracles (OracleProcess.refusingBase (E := E))
    FriVirtualBody.installed oracle0Signature FriVirtualBody.selected FriVirtualBody.signature site roles
    0 [1] (foldCaptures n source beta shift) (2 ^ n) (rows n source beta shift) before 1 self.symm visible
  obtain ⟨replyEq, installed⟩ := op reply success
  have extended := OracleExecution.operation_extension model checkedUnit.oracles (OracleProcess.refusingBase (E := E))
    site 1 roles (.virtual oracle0Signature 0 [1]) (ProtocolValue.embedComponents (foldCaptures n source beta shift).present) before
  rw [installed] at extended ⊢
  refine ⟨replyEq, ?_, ⟨parent.afterExtension extended (.refl _)⟩, self⟩
  exact ⟨{
    older := before.entries
    newer := []
    holder := roles 0
    receivers := [1].map roles
    live := parent
    allowed := visible
    fresh := rfl
    entries := rfl }⟩

def constructionSites : List OracleLocation :=
  FriCommitRound.roundBody.erase.operations.filterMap fun op ↦ match op with
  | .oracle (.virtual ..) location => some location
  | _ => none

/-- This round has one virtual construction. Replacing it with a different
operation or adding a second occurrence invalidates the selection. -/
def constructionSite : OracleLocation := constructionSites.head (by
  have unique : constructionSites.length = 1 := by decide +kernel
  intro empty
  simp [empty] at unique)

noncomputable def request (context : ProtocolContext) (n : Nat) (source : OracleAnchor) (beta shift : Octic) :
    (OracleProtocol.Interface model).Op :=
  .oracle ⟨.virtual oracle0Signature 0 [1], constructionSite, 1, context.roles,
    ProtocolValue.embedComponents (foldCaptures n source beta shift).present⟩

/-- Install the virtual view at the actual dynamic construction occurrence.
A cursor refusal, unavailable capture or invalid shape cannot yield a view. -/
theorem sourceRegisters {M : Type → Type} [Monad M] [LawfulMonad M]
    (network : PublishedWords.Table model → PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
    (choose : PublishedWords.Chooser M model Aux E)
    (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (n : Nat) (source : OracleAnchor) (word : Fin (2 ^ (n + 1)) → Octic) (beta shift : Octic)
    (before : OracleProtocol.State model checkedUnit.snapshot checkedUnit.domains checkedUnit.math (PublishedWords.State model Aux))
    (self : before.oracle.self = 1)
    (parent : PublishedWords.RegisteredWord (row := .field extension) before.oracle.entries before.oracle.self source word before.oracle.provider) :
    let anchor := ({constructionSite with invocation := before.frame.invocation} : OracleLocation).anchor
    Std.Do.Internal.Ensures (fun record ↦ ∀ reply, record.outcome = .returned reply →
      reply = .cons (OracleProtocol.concrete model (.oracle kind) anchor) .nil ∧
      Nonempty (VirtualStore.Registered record.state.oracle source anchor word beta shift) ∧
      Nonempty (PublishedWords.RegisteredWord (row := .field extension) record.state.oracle.entries
        record.state.oracle.self source word record.state.oracle.provider) ∧ record.state.oracle.self = 1)
      (PublishedWords.actionM checkedUnit.oracles network choose (request context n source beta shift) before) := by
  dsimp only
  unfold PublishedWords.actionM
  rw [OraclePublication.actionM_local checkedUnit.oracles (PublishedWords.liftM network)
    PublishedWords.readM (PublishedWords.publishM choose) _ _ rfl]
  apply Zkc.MonadicPostcondition.pure
  dsimp only [request, OracleProtocol.handler]
  split
  · intro reply eq; cases eq
  · exact registered n source word beta shift _ context.roles receiver before.oracle self parent

end ZkcSecurity.ArkLib.Fri.CommitVirtual
