module

public import ZkcExamples.Structured.Generated.Connections.Gkr
public import ZkcSecurity.Realizations.Gkr.CanonicalSource
public import ZkcSecurity.Source.RootPublic

@[expose] public section

/-! The shared root installation transports the actual occurrence properties
at arbitrary incoming histories, retaining every complete returned source row. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalReading
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Obligations
open ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Obligations ZkcSecurity.Source
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev Result (F G : Type) := Values (Component (uniformCarriers F G).Value)
  GkrSourceViews.program.payload.entry.outputs × Original.State (uniformCarriers F G)
def output : Var GkrSourceViews.program.payload.entry.outputs .boolean := .here
abbrev root := ZkcExamples.Structured.Generated.Connections.Gkr.validator
abbrev routing := ZkcExamples.Structured.Generated.Connections.Gkr.validatorRouting

def inputs (runtime : Source.Invocation F) := SourceValidator.inputs (G := G) { runtime with handle := 7 }
def occurrence (runtime : Source.Invocation F) :=
  Occurrence.participant (ringModel F G) GkrSourceViews.program 1 (inputs (G := G) runtime)
def physical (runtime : Source.Invocation F) (history : Domain.History (uniformCarriers F G)) :=
  Domain.inputFrame ZkcExamples.Structured.Generated.Connections.Gkr.context
    ((Domain.encodeValues (Canonical.statement (ringModel F G) runtime)).getD []) history

def presented (runtime : Source.Invocation F) (history : Domain.History (uniformCarriers F G)) :=
  RootConnection.publicPresentation root (ringModel F G) (physical runtime history)

def acceptance (result : Result F G) : Option Bool := result.1.get output

variable [Fintype F] [SampleableType F]
attribute [local instance] OccurrenceReading.rawSampleable

def price : ENNReal := SourceValidator.price (F := F)

def rejected
    (statement : (Canonical.subject (ringModel F G)).validatorArtifacts.Statement (ringModel F G))
    (wrong : (Canonical.validatorSubject (ringModel F G)).FalseStatement statement)
    (history : Domain.History (uniformCarriers F G)) :
    Derivation NominalDomain.interface (boundedEscape (fun _ _ => price (F := F)))
      (fun _ result => acceptance result ≠ some true) history
      (presented (Canonical.invocation (ringModel F G) statement 7) history) := by
  let runtime := Canonical.invocation (ringModel F G) statement 7
  exact RootPublic.rejects_inputFrame root rfl (ringModel F G) (inputs runtime) (price (F := F))
    ((Domain.encodeValues (Canonical.statement (ringModel F G) runtime)).getD []) history _ rfl
    (by rfl) (fun result => result.get output ≠ some true) []
    (CanonicalSource.rejected statement 7 wrong [])

omit [SampleableType F] in
theorem costs (runtime : Source.Invocation F) (history : Domain.History (uniformCarriers F G)) :
    Typed.ChargedCostBound NominalDomain.interface (fun _ _ => price (F := F))
      (presented (G := G) runtime history) history (40 * price (F := F)) := by
  exact RootPublic.cost_inputFrame root rfl (ringModel F G) (inputs runtime) (price (F := F))
    ((Domain.encodeValues (Canonical.statement (ringModel F G) runtime)).getD []) history _ rfl
    (by rfl) [] _ (SourceValidator.costs { runtime with handle := 7 } [])

#print axioms rejected
#print axioms costs
end ZkcSecurity.Realizations.Gkr.CanonicalReading
