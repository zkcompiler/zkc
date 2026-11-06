module

public import ZkcArkLibExamples.Fri.VirtualWord
public import ZkcArkLibExamples.Fri.StoredWord

@[expose] public section

/-! A read of the registered Fold reaches two cells in the word fixed by
publication. All three requests retain their source locations, expansion
path and order in the actual store. -/
set_option autoImplicit false
set_option maxRecDepth 6000
namespace ZkcSecurity.ArkLib.Fri.VirtualStore
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcSecurity.Domains.KoalaBearModel (model)
open ZkcSecurity.Domains.KoalaBear (Octic)
open FriSource (checkedUnit extension)
open VirtualReads (kind)

abbrev Entries := OracleEntries model checkedUnit.snapshot checkedUnit.domains checkedUnit.math
abbrev Captures := Values model.Value FriSourceBodies.oracle0Signature.inputs.dropLast

def table (anchor : OracleAnchor) (rows holder : Nat) (receivers : List Nat)
    (captures : Captures) : OracleStoredTable model checkedUnit.snapshot checkedUnit.domains checkedUnit.math
      kind.answer :=
  ⟨anchor, rows, holder, receivers, .virtual FriVirtualBody.installed rfl captures⟩

theorem foldedCell {Aux E : Type} {m : Nat} (size : m + 1 ≤ 63)
    (domain : Domain.SmoothCosetFftDomain (m + 1) Octic) (shift : Octic)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point RetainedDomain.root shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → Octic) (beta : Octic) (index : Fin (2 ^ m))
    (older newer : Entries) (source anchor : OracleAnchor) (holder self : Nat) (receivers : List Nat)
    (state : PublishedWords.State model Aux) (live : StoredWord.Base (d := extension) older self source word state)
    (allowed : OracleStore.visible self holder receivers = true)
    (fresh : OracleStore.hasAnchor newer anchor = false) (location : OracleLocation)
    (expansion : List (OracleAnchor × OracleLocation)) (count : Nat) :
    let parent := Phases.publishedRequest extension anchor index.val location expansion
    let captures := VirtualReads.captures model source beta (2 ^ (m + 1)) (2 ^ m) shift
      (RetainedDomain.root (m + 1)) (shift⁻¹ : Octic) ((RetainedDomain.root (m + 1))⁻¹ : Octic) ((2 : Octic)⁻¹ : Octic)
    let entries := newer ++ (⟨kind.answer, table anchor (2 ^ m) holder receivers captures⟩ :: older)
    OracleStore.answer model (PublishedWords.read (E := E)) self entries parent (state, count) =
      ⟨.returned (ProximityGap.foldWord domain word 1 beta index), (state, count + 3),
        [.query parent,
         .query (parent.expand (VirtualReads.leftRequest source (lowIndex index).val)),
         .query (parent.expand (VirtualReads.rightRequest source (highIndex index).val))]⟩ := by
  dsimp only
  let parent := Phases.publishedRequest extension anchor index.val location expansion
  let handler : PIR.Handler (VirtualReads.readInterface model) (PublishedWords.State model Aux × Nat) (OracleEvent E) :=
    fun child current ↦ OracleStore.answer model PublishedWords.read self older (parent.expand child) current
  have child (position : Fin (2 ^ (m + 1))) (site : OracleLocation) (atCount : Nat) :=
    live.cell (E := E) position {site with invocation := location.invocation}
      (expansion ++ [(anchor, location)]) atCount
  have left := child (lowIndex index) (VirtualReads.leftRequest source (lowIndex index).val).location (count + 1)
  have right := child (highIndex index) (VirtualReads.rightRequest source (highIndex index).val).location (count + 2)
  have body := VirtualWord.runFold size domain shift geometry word beta index source handler left right
  have small : 2 ^ m < indexLimit := Nat.pow_lt_pow_right (by decide) (by omega : m < 64)
  have shape : OracleStore.validRows parent.kind (2 ^ m) = true := by
    simp [OracleStore.validRows, OracleKind.rows, parent, Phases.publishedRequest, small]
  rw [OracleStore.answerSkipNewer _ _ _ _ _ _ fresh]
  exact OracleStore.answerOfVirtual (PublishedWords.read (E := E)) self older parent (2 ^ m)
    holder receivers FriVirtualBody.installed rfl _ rfl allowed shape index.isLt (state, count)
    (ProximityGap.foldWord domain word 1 beta index) _ _ body

/-- The registered fold refers to this earlier publication. Preserve the
older entries captured when it was created even if newer tables now exist. -/
structure Registered {Aux : Type} {m : Nat}
    (runtime : OracleRuntimeState model checkedUnit.snapshot checkedUnit.domains checkedUnit.math
      (PublishedWords.State model Aux))
    (source anchor : OracleAnchor) (word : Fin (2 ^ (m + 1)) → Octic) (beta shift : Octic) where
  older : Entries
  newer : Entries
  holder : Nat
  receivers : List Nat
  live : StoredWord.Base (d := extension) older runtime.self source word runtime.provider
  allowed : OracleStore.visible runtime.self holder receivers = true
  fresh : OracleStore.hasAnchor newer anchor = false
  entries : runtime.entries = newer ++ (⟨kind.answer, table anchor (2 ^ m) holder receivers
    (VirtualReads.captures model source beta (2 ^ (m + 1)) (2 ^ m) shift (RetainedDomain.root (m + 1))
      (shift⁻¹ : Octic) ((RetainedDomain.root (m + 1))⁻¹ : Octic) ((2 : Octic)⁻¹ : Octic))⟩ :: older)

/-- An actual receiver query of the registered virtual handle obtains the
ArkLib fold. The frame supplies the invocation for all three reads. -/
theorem Registered.sourceQuery {M : Type → Type} [Monad M] [LawfulMonad M] {Aux E : Type} {m : Nat}
    (network : PublishedWords.Table model →
      PIR.MonadHandler M (participantInterfaceOn model.toCarriers) Aux E)
    (choose : PublishedWords.Chooser M model Aux E)
    (size : m + 1 ≤ 63) (domain : Domain.SmoothCosetFftDomain (m + 1) Octic) (shift : Octic)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), domain i = point RetainedDomain.root shift (m + 1) i)
    (word : Fin (2 ^ (m + 1)) → Octic) (beta : Octic) (index : Fin (2 ^ m))
    (source anchor : OracleAnchor)
    (state : OracleProtocol.State model checkedUnit.snapshot checkedUnit.domains checkedUnit.math
      (PublishedWords.State model Aux))
    (view : Registered state.oracle source anchor word beta shift)
    (self owner : Nat) (atSelf : self = state.oracle.self) (roles : Nat → Nat) (site : OracleLocation)
    (active : roles owner = state.oracle.self) :
    let parent := Phases.publishedRequest extension anchor index.val {site with invocation := state.frame.invocation} []
    PublishedWords.actionM checkedUnit.oracles network choose
        (OracleProtocol.tableQuery model (.field extension) none anchor index.val self owner roles site) state =
      pure (OraclePublication.cursorReply site state (.cons (some (ProtocolValue.ofConcrete (.field extension)
          (ProximityGap.foldWord domain word 1 beta index))) .nil)
        {state.oracle with queries := state.oracle.queries + 3}
        [.logical (.query parent),
         .logical (.query (parent.expand (VirtualReads.leftRequest source (lowIndex index).val))),
         .logical (.query (parent.expand (VirtualReads.rightRequest source (highIndex index).val)))]) := by
  subst self
  dsimp only
  apply OraclePublication.cursorCell checkedUnit.oracles (PublishedWords.liftM network) PublishedWords.read
    (PublishedWords.publishM choose) (.field extension) none anchor index.val owner roles site state
    active _ (state.oracle.provider, state.oracle.queries + 3)
    [.query _, .query _, .query _]
  rw [view.entries]
  exact foldedCell size domain shift geometry word beta index view.older view.newer source anchor view.holder
    state.oracle.self view.receivers state.oracle.provider view.live view.allowed view.fresh _ [] state.oracle.queries

end ZkcSecurity.ArkLib.Fri.VirtualStore
