module

public import ZkcSecurity.Realizations.Sumcheck.SourceFamilyProperties
public import ZkcSecurity.Realizations.Sumcheck.SourceTerminal

@[expose] public section

/-! Property consumers for actual source roots. The shared symbolic reduction
supplies shape, honest return and No; the nominal terminal helper supplies the
Boolean comparison. The two-table caller composes the same component twice. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.Realizations.Sumcheck.SourceRootProperties
open ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open Zkc.Source Zkc.Source.Structured ReferenceLibrary Zkc.Transcript Zkc.Obligations
open ZkcExamples.Structured SumcheckReferenceInstallation TableComponent SourceIteration
open SumcheckSourceSelections hiding field

variable (model : DomainModel) [fieldLaw : Fact (IsField (model.Field field))]
local instance : Field (model.Field field) := fieldLaw.out.toField
variable {Frame E P : Type} {Raw : E → Type}

def context (site : String) : ProtocolContext := ProtocolContext.enter {} site [0,1]

theorem context_distinct (site : String) : NormalForm.RosterDistinct (context site) 1 2 :=
  .ofSeparate (by change (0 : Nat) ≠ 1; decide) (by decide)

variable (selection : Selection) (site : String)
  (original : List (model.Field field)) (count handle : Nat) (scalar : model.Field field)
  (callerFrame : Frame) (shape : original.length = 2^count)
  (bounded : count ≤ maximum selection) (small : count < 64) (finite : original.length < indexLimit)

include callerFrame shape bounded small finite

/-- Shape preservation is independent of the truth of this scalar claim. -/
theorem one_present :
    PIR.Yields (fun out => ∃ accepted : Bool, out = some accepted)
      (SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle)) := by
  exact SourceFamily.one_present_bounded model (SourceFamilySelections.installed selection) site original count handle scalar callerFrame shape bounded small finite

/-- At every reached history a false represented claim returns false, stops,
or escapes only through the supplied reached-history collision law. -/
def one_no (absorb : Interface (Occurrence.signature model.toCarriers) E P Raw)
    (escape : EscapeJudgment E Raw)
    (steps : RepeatedComponent.NoContract
      (component model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
        (context site) handle) absorb escape (no model original callerFrame))
    (wrong : scalar ≠ original.sum) (history : List E) :
    Derivation absorb escape (fun _ out => out = some false) history
      (SourceRootReference.one model selection {} site (some original) (some scalar) (some count) (some handle)) := by
  exact SourceFamily.one_no_bounded model (SourceFamilySelections.installed selection) site original count handle scalar callerFrame shape bounded small finite absorb escape steps wrong history

/-- Conditional successful validator execution: the exception postcondition is
False. This does not construct honest-pair readback. The handler state and
complete accumulated history remain the WP arguments. -/
theorem one_honest {H : Type}
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (good : List E → Runtime model Frame → H → Prop)
    (steps : RepeatedComponent.HonestContract
      (component model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
        (context site) handle) handler (honest model good original callerFrame))
    (history : List E) (h : H)
    (initial : honest model good original callerFrame history count
      (encode model 0 (PrefixState.initial original count scalar callerFrame shape)) h) :
    PIR.WeakestPrecondition.satisfies
      ((SourceRootReference.one model selection {} site (some original) (some scalar)
        (some count) (some handle)).run handler h)
      (fun out _ _ => out = some true) (fun _ _ _ => False) history := by
  exact SourceFamily.one_honest model (SourceFamilySelections.installed selection) site original count handle scalar callerFrame shape bounded small finite handler good steps history h initial

/-- A sequential caller supplies an ordinary synchronization invariant for its
next component. Successful source execution preserves it with the reached history. -/
theorem one_honest_preserving {H : Type}
    (handler : PIR.Handler (Occurrence.signature model.toCarriers) H E)
    (good : List E → Runtime model Frame → H → Prop)
    (steps : RepeatedComponent.HonestContract
      (component model (source selection).payload.definitions (Occurrence.table model (source selection).payload)
        (context site) handle) handler (honest model good original callerFrame))
    (history : List E) (h : H)
    (initial : honest model good original callerFrame history count
      (encode model 0 (PrefixState.initial original count scalar callerFrame shape)) h)
    (after : H → List E → Prop)
    (finish : ∀ reached runtime final, honest model good original callerFrame reached 0 runtime final → after final reached) :
    PIR.WeakestPrecondition.satisfies
      ((SourceRootReference.one model selection {} site (some original) (some scalar)
        (some count) (some handle)).run handler h)
      (fun out final reached => out = some true ∧ after final reached) (fun _ _ _ => False) history := by
  exact SourceFamily.one_honest_preserving model (SourceFamilySelections.installed selection) site original count handle scalar callerFrame shape bounded small finite handler good steps history h initial after finish

end ZkcSecurity.Realizations.Sumcheck.SourceRootProperties
