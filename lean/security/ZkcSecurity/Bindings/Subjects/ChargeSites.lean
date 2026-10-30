module

public import ZkcSecurity.Bindings.Subjects.PairValidator
public import Zkc.Source.Structured.Labels

@[expose] public section

/-! Source-labelled charge selection. The frontend encodes each explicit label
as lowercase UTF-8 hex. Selection compares the complete source call path with
retained templates and then reuses the checked native occurrence selector.
No author supplies a length prefix, encoded native path or occurrence ordinal.
-/
set_option autoImplicit false
namespace ZkcSecurity.Claims.Domain.ChargeSite
open Zkc.Source Zkc.Construction
open Zkc.Source.Structured (encodedLabel)

def sourcePath (template : Template) : Option (List String) := do
  let ["query", _, site, _, _, _, _] := template.event | none
  let calls ← template.steps.foldlM (fun path step =>
    if step.kind = "apply" then some (path ++ [step.site])
    else if step.kind = "repeat" then some path else none) []
  return calls ++ [site]

/-- A structural parser keeps closed selector proofs reducible in the kernel;
`String.splitOn` uses an iterator implementation that is opaque there. -/
def labelParts : List Char → List Char → List String → List String
  | [], current, previous => (String.ofList current.reverse :: previous).reverse
  | char :: rest, current, previous =>
      if char = '.' then labelParts rest [] (String.ofList current.reverse :: previous)
      else labelParts rest (char :: current) previous

/-- Discovery alone carries no security evidence. Duplicate or malformed paths
remain unresolved, even if their printed native names happen to agree. -/
def resolveLabel (occurrences : List Domain.ChallengeOccurrence) (label : String) : Option String := do
  let parts := labelParts label.toList [] []
  if parts.any String.isEmpty then none else do
    let [occurrence] := occurrences.filter (fun item =>
      sourcePath item.template == some (parts.map encodedLabel)) | none
    occurrence.template.querySite?

/-- Check the derived occurrence against both the admitted participant and its
selected construction policy. The caller supplies only the source label. -/
def selectLabel {art : ZkcSecurity.Endpoint.Domain.Artifacts}
    (compiled : ZkcSecurity.Endpoint.Domain.Compiled art) (label : String) :
    Except String (Domain.ChargeSite compiled) := do
  let some native := resolveLabel (Domain.challengeOccurrences art.participant.instructions) label
    | throw "charge-source-label"
  select compiled label native

end ZkcSecurity.Claims.Domain.ChargeSite
