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

end ZkcSecurity.ArkLib.Fri.VirtualStore
