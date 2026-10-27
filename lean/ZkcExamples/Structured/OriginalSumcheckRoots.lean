module

public import ZkcExamples.Structured.OriginalSumcheckInstances

@[expose] public section

/-! Root call assembly for the actual occurrence-aware original participants.
The root syntax selects the original declaration and caller prefix. Its helper
continuations retain the full original semantics, including absent inputs. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
noncomputable section
namespace ZkcExamples.Structured.OriginalSumcheckRoots
open Zkc.Source Zkc.Source.Structured
open OriginalSumcheckLibrary OriginalSumcheckInstances SumcheckVerifierBodies

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem singleton_eta {Value : Ty → Type} {ty : Ty} (out : Values Value [ty]) :
    Values.cons (out.get .here) .nil = out := by
  cases out with | cons value out => cases out; rfl

/-- The full output mask is explicit, rather than a scalar-only readback. -/
abbrev call (payload : UnitPayload) (maximum : Nat) (context : ProtocolContext)
    (outputs : List (List Nat)) (point : Option (List F)) (claim : Option F) (count service : Option Nat) :=
  (OriginalSumcheckLibrary.reduce payload maximum context (context.roles 1) []
    (verifierInputs (G := G) point claim count service)).bind
      (fun result => .done (maskValues (context.roles 1) (context.mapScopes outputs) result))

namespace Small
abbrev payload := OriginalSumcheckInstances.Small.payload
abbrev definition := OriginalSumcheckInstances.Small.reduceDefinition
abbrev root := OriginalSumcheckInstances.Small.rootDefinition
abbrev context := OriginalSumcheckInstances.Small.context

def protocolPrefix := Generated.Original.SmallSumcheck.protocolPrefix (F := F) (G := G)

abbrev reduce (point : Option (List F)) (claim : Option F) (count service : Option Nat) :=
  call (G := G) payload Generated.Original.SmallSumcheck.maximum context definition.outputScopes point claim count service

theorem root_body : root.body = Generated.Bindings.SmallSumcheckInputs.protocol1Body :=
  Generated.Original.SmallSumcheck.root_body.trans Generated.Original.SmallSumcheck.source_body

theorem call_binding (point : Option (List F)) (claim : Option F) (count service : Option Nat) :
    invokeProtocol (protocolPrefix (F := F) (G := G)) definition.signature context 1
      (verifierInputs point claim count service) = reduce point claim count service :=
  Generated.Original.SmallSumcheck.library_call_binding "label_726564756365" point claim count service

abbrev check (entries : Option (List F))
    (result : Values (Component (assignment F G)) reduceOutputs) :=
  Generated.Original.SmallSumcheck.checkContinuation (helpers payload) entries result

def rootProcess (entries : Option (List F)) (claim : Option F) (count service : Option Nat) :=
  Generated.Original.SmallSumcheck.realized (G := G) entries claim count service

theorem root_lookup (args : Values (Component (assignment F G)) root.inputs) :
    invokeProtocol (Occurrence.table (ringModel F G) payload) root.signature {} 1 args =
      root.denoteWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn
        protocolPrefix Occurrence.iterations {} 1 args :=
  Generated.Original.SmallSumcheck.root_lookup args

theorem body_binding
    (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))
    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G)))
    (entries : Option (List F)) (claim : Option F) (count service : Option Nat) :
    Generated.Original.SmallSumcheck.sourceBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) actions tables.toOn 1
        protocols {} Occurrence.iterations)
      ((.cons entries (.cons claim (.cons count (.cons service .nil)))) : Values (Component (assignment F G)) root.inputs).get =
      Generated.Original.SmallSumcheck.process tables protocols entries claim count service :=
  Generated.Original.SmallSumcheck.body_binding tables protocols entries claim count service

set_option backward.isDefEq.respectTransparency false in
theorem root_binding (entries : Option (List F)) (claim : Option F) (count service : Option Nat) :
    Occurrence.participant (ringModel F G) OriginalSumcheckInstances.Small.imported.program 1
      (.cons entries (.cons claim (.cons count (.cons service .nil)))) =
      rootProcess entries claim count service :=
  Generated.Original.SmallSumcheck.participant_binding entries claim count service
end Small

namespace Two
abbrev payload := OriginalSumcheckInstances.Two.payload
abbrev definition := OriginalSumcheckInstances.Two.reduceDefinition
abbrev root := OriginalSumcheckInstances.Two.rootDefinition
abbrev leftContext := OriginalSumcheckInstances.Two.leftContext
abbrev rightContext := OriginalSumcheckInstances.Two.rightContext

def protocolPrefix := Generated.Original.TwoSums.protocolPrefix (F := F) (G := G)

abbrev reduce (site : String) (point : Option (List F)) (claim : Option F) (count service : Option Nat) :=
  call (G := G) payload Generated.Original.TwoSums.maximum (({} : ProtocolContext).enter site [0, 1])
    definition.outputScopes point claim count service

theorem call_binding (site : String) (point : Option (List F)) (claim : Option F) (count service : Option Nat) :
    invokeProtocol (protocolPrefix (F := F) (G := G)) definition.signature
      (({} : ProtocolContext).enter site [0, 1]) 1 (verifierInputs point claim count service) =
      reduce site point claim count service :=
  Generated.Original.TwoSums.library_call_binding site point claim count service

abbrev checkWith (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))
    (entries : Option (List F)) (result : Values (Component (assignment F G)) reduceOutputs) :=
  Generated.Original.TwoSums.checkContinuation tables entries result

def bothHelper : Helper := Generated.Original.TwoSums.terminalHelper

abbrev combine (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))
    (left right : Values (Component (assignment F G)) [.boolean]) :=
  Generated.Original.TwoSums.terminalCalculation tables left right

def rootProcess (left right : Option (List F)) (leftClaim rightClaim : Option F)
    (count service : Option Nat) :=
  Generated.Original.TwoSums.realized (G := G) left right leftClaim rightClaim count service

theorem root_body : root.body = Generated.Bindings.TwoSumsInputs.protocol1Body :=
  Generated.Original.TwoSums.root_body.trans Generated.Original.TwoSums.source_body

theorem root_lookup (args : Values (Component (assignment F G)) root.inputs) :
    invokeProtocol (Occurrence.table (ringModel F G) payload) root.signature {} 1 args =
      root.denoteWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn
        protocolPrefix Occurrence.iterations {} 1 args :=
  Generated.Original.TwoSums.root_lookup args

theorem body_binding
    (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))
    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G)))
    (left right : Option (List F)) (leftClaim rightClaim : Option F) (count service : Option Nat) :
    Generated.Original.TwoSums.sourceBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) actions tables.toOn 1
        protocols {} Occurrence.iterations)
      ((.cons left (.cons right (.cons leftClaim (.cons rightClaim (.cons count (.cons service .nil)))))) : Values (Component (assignment F G)) root.inputs).get =
      Generated.Original.TwoSums.process tables protocols left right leftClaim rightClaim count service :=
  Generated.Original.TwoSums.body_binding tables protocols left right leftClaim rightClaim count service

set_option backward.isDefEq.respectTransparency false in
theorem root_binding (left right : Option (List F)) (leftClaim rightClaim : Option F)
    (count service : Option Nat) :
    Occurrence.participant (ringModel F G) OriginalSumcheckInstances.Two.imported.program 1
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim
        (.cons count (.cons service .nil)))))) =
      rootProcess left right leftClaim rightClaim count service :=
  Generated.Original.TwoSums.participant_binding left right leftClaim rightClaim count service
end Two

end ZkcExamples.Structured.OriginalSumcheckRoots
