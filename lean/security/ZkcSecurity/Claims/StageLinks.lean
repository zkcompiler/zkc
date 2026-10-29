module

public import ZkcSecurity.Claims.Subject

@[expose] public section

/-! Request-side links for actual Domain execution. Static admission, all-reply
source transport and byte/Domain transport are separate checked obligations.
They make no assertion about a native runtime outside the Lean model.
-/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcSecurity.Endpoint

namespace Subject
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  {art : Artifacts} {endpoint : Semantics} (subject : Subject F G art endpoint)

def ConstructionChecked : Prop :=
  checkCompiled subject.compiled.imported art.participant = .ok () ∧
  select subject.compiled.imported art.participant = some subject.compiled.selection ∧
  subject.compiled.selection.check subject.compiled.imported art.participant = true ∧
  subject.compiled.selection.publics = art.publics ∧
  SourceOccurrences.check art.original subject.compiled.context art.participant = .ok () ∧
  subject.compiled.SourceConnection (F := F) (G := G)

theorem constructionChecked : subject.ConstructionChecked :=
  ⟨subject.compiled.compiled, subject.compiled.selected, subject.compiled.checked, subject.compiled.publics,
    subject.compiled.occurrences, subject.connection⟩

def LoweringChecked (subject : Subject F G art .executableBytes) : Prop :=
  art.program = some subject.lowering.validator ∧
  Zkc.Executable.checkLowering Zkc.Executable.installed art.participant subject.lowering.validator =
    .ok subject.lowering.lowered ∧
  (∀ name ∈ Zkc.Executable.Instruction.helpers art.participant.instructions,
    Zkc.Executable.Prepared Zkc.Executable.installed subject.lowering.validator
      (helperTable subject.compiled.imported.program F G) name) ∧
  (∀ call ∈ Zkc.Construction.Instruction.callList art.participant.instructions,
    Zkc.Executable.HelperSorted (helperTable subject.compiled.imported.program F G) call.1 call.2) ∧
  (∀ statement : art.Statement F G, subject.lowering.validator.admits (encodeValues statement) = true) ∧
  BytePruning art subject.compiled F G subject.lowering.validator subject.lowering.lowered

theorem loweringChecked (subject : Subject F G art .executableBytes) : subject.LoweringChecked :=
  ⟨subject.lowering.program, subject.lowering.accepted, subject.lowering.prepared,
    subject.lowering.sorted, subject.lowering.admits, subject.lowering.pruning⟩

def constructionLink : Obligation :=
  ⟨"construction.checked", "admitted IR and selected participant", subject.ConstructionChecked, .infrastructure⟩

/-- Keep the subject index before reducing the fixed connection proposition.
Two subject references may share a participant; their stage links still belong
to their respective subjects. Proofs use the same method-independent meaning. -/
def SourceConnectionChecked : Prop :=
  ConnectionAdmission.Required subject.compiled.imported.program
    subject.compiled.selection.context .validator art.participant

def sourceConnectionLink : Obligation :=
  ⟨"construction.source_connection", "complete source-to-participant correspondence",
    subject.SourceConnectionChecked, .infrastructure⟩

def loweringLink (subject : Subject F G art .executableBytes) : Obligation :=
  ⟨"lowering.interpreted_bytes", "checked Lean executable validator", subject.LoweringChecked, .infrastructure⟩

def stageLinks : List Obligation :=
  match endpoint with
  | .idealMeaning => [subject.constructionLink, subject.sourceConnectionLink]
  | .executableBytes => [subject.constructionLink, subject.sourceConnectionLink, subject.loweringLink]

/-- Omitted proofs keep a receipt open; these proofs discharge exactly the
interpreted-stage links already carried by the admitted subject. -/
def stageLinkProofs (index : Fin subject.stageLinks.length) :
    Option (PLift (subject.stageLinks.get index).goal) := by
  cases endpoint with
  | idealMeaning =>
    match index with
    | ⟨0, _⟩ => exact some ⟨subject.constructionChecked⟩
    | ⟨1, _⟩ => exact subject.compiled.sourceConnection
    | ⟨n + 2, impossible⟩ => exact False.elim (by simp [stageLinks] at impossible)
  | executableBytes =>
    match index with
    | ⟨0, _⟩ => exact some ⟨subject.constructionChecked⟩
    | ⟨1, _⟩ => exact subject.compiled.sourceConnection
    | ⟨2, _⟩ => exact some ⟨subject.loweringChecked⟩
    | ⟨n + 3, impossible⟩ => exact False.elim (by simp [stageLinks] at impossible)

end Subject
end ZkcSecurity.Claims
