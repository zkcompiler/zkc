module

public import ZkcSecurity.Claims.Subject

@[expose] public section

/-! Request-side links for the actual interpreted compiled verifier. These
links are proved by admission and lowering, independently of endpoint families.
They make no assertion about a native runtime or source-to-IR correspondence.
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
  subject.compiled.selection.publics = art.publics

theorem constructionChecked : subject.ConstructionChecked :=
  ⟨subject.compiled.compiled, subject.compiled.selected, subject.compiled.checked, subject.compiled.publics⟩

def LoweringChecked (subject : Subject F G art .executableBytes) : Prop :=
  art.program = some subject.lowering.validator ∧
  Zkc.Executable.checkLowering Zkc.Executable.installed art.participant subject.lowering.validator =
    .ok subject.lowering.lowered ∧
  (∀ name ∈ Zkc.Executable.Instruction.helpers art.participant.instructions,
    Zkc.Executable.Prepared Zkc.Executable.installed subject.lowering.validator
      (helperTable subject.compiled.imported.program F G) name) ∧
  (∀ call ∈ Zkc.Executable.Instruction.callList art.participant.instructions,
    Zkc.Executable.HelperSorted (helperTable subject.compiled.imported.program F G) call.1 call.2) ∧
  ∀ statement : art.Statement F G, subject.lowering.validator.admits (encodeValues statement) = true

theorem loweringChecked (subject : Subject F G art .executableBytes) : subject.LoweringChecked :=
  ⟨subject.lowering.program, subject.lowering.accepted, subject.lowering.prepared,
    subject.lowering.sorted, subject.lowering.admits⟩

def constructionLink : Obligation :=
  ⟨"construction.checked", "admitted IR and selected participant", subject.ConstructionChecked, .infrastructure⟩

def loweringLink (subject : Subject F G art .executableBytes) : Obligation :=
  ⟨"lowering.interpreted_bytes", "checked Lean executable validator", subject.LoweringChecked, .infrastructure⟩

def stageLinks : List Obligation :=
  match endpoint with
  | .idealMeaning => [subject.constructionLink]
  | .executableBytes => [subject.constructionLink, subject.loweringLink]

/-- Omitted proofs keep a receipt open; these proofs discharge exactly the
interpreted-stage links already carried by the admitted subject. -/
def stageLinkProofs (index : Fin subject.stageLinks.length) :
    Option (PLift (subject.stageLinks.get index).goal) := by
  cases endpoint with
  | idealMeaning =>
    match index with
    | ⟨0, _⟩ => exact some ⟨subject.constructionChecked⟩
    | ⟨n + 1, impossible⟩ => exact False.elim (by simp [stageLinks] at impossible)
  | executableBytes =>
    match index with
    | ⟨0, _⟩ => exact some ⟨subject.constructionChecked⟩
    | ⟨1, _⟩ => exact some ⟨subject.loweringChecked⟩
    | ⟨n + 2, impossible⟩ => exact False.elim (by simp [stageLinks] at impossible)

end Subject
end ZkcSecurity.Claims
