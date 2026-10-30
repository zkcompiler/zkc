module

public import ZkcExamples.Structured.GkrSourceLaws
public import ZkcExamples.Structured.Generated.Presentations.Gkr
public import Zkc.Source.Structured.CommonAdapter

public section

/-! Exact associations for the admitted producer's circuit and combination
helpers. These expose their actual bodies for independent realization proofs;
an association alone asserts neither a mathematical value nor completeness.
-/

namespace ZkcSecurity.Realizations.Gkr.ProducerHelpers
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

variable {F G : Type} [CommRing F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The actual admitted producer, including missing inputs and all its stops.
The absent acceptance output belongs to the verifier role. -/
@[expose] noncomputable def producer (inputs outputs add mul : Option (List F))
    (layers selector width handle : Option Nat) :
    PIR.Process (CommonAdapter.commonInterface F G) (Option Bool) :=
  ((GkrSourceViews.program.participant F G 0
    (.cons inputs (.cons outputs (.cons add (.cons mul (.cons layers (.cons selector
      (.cons width (.cons handle .nil))))))))).bind
        fun result => .done (result.get .here)).interpret CommonAdapter.project

/-- The complete current producer body, with the original optional inputs,
role masks and every stopped execution retained. -/
theorem producer_binding (inputs outputs add mul : Option (List F))
    (layers selector width handle : Option Nat) :
    producer (G := G) inputs outputs add mul layers selector width handle =
      ((Generated.Presentations.Gkr.Root.gkrBody.denote
        (participantMeaningWith (.silent _) (participantActions F G)
          (Zkc.Source.Structured.plainHelpers (F := F) (G := G) GkrSourceViews.unit) 0
          (GkrSourceViews.unit.plainProtocolTable F G) {})
        (maskValues 0 (GkrSourceBodies.gkrSignature.inputScopes)
          (.cons inputs (.cons outputs (.cons add (.cons mul (.cons layers (.cons selector
            (.cons width (.cons handle .nil))))))))).get).bind
          (fun result => .done ((maskValues 0 GkrSourceBodies.gkrSignature.outputScopes result).get .here))).interpret
            CommonAdapter.project := by
  let args : Values (Component (assignment F G)) GkrSourceBodies.gkrSignature.inputs :=
    .cons inputs (.cons outputs (.cons add (.cons mul (.cons layers (.cons selector
      (.cons width (.cons handle .nil)))))))
  have view := (GkrSourceViews.unit.protocolTable_forgetSites (F := F) (G := G)
    GkrSourceBodies.gkrSignature {} 0 args).trans
    (protocol_invoke_body_view (.silent _) (participantActions F G)
      (Zkc.Source.Structured.plainHelpers (F := F) (G := G) GkrSourceViews.unit)
      GkrSourceViews.unit.protocols GkrSourceViews.unit.protocolsLinked
      GkrSourceViews.gkrDefinition GkrSourceViews.gkr_member
      Generated.Presentations.Gkr.Root.gkrBody Generated.Presentations.Gkr.Root.gkrBody_raw {} 0 args)
  exact (congrArg (fun process : PIR.Process (participantInterface F G)
      (Values (Component (assignment F G)) GkrSourceBodies.gkrSignature.outputs) =>
    (process.bind fun result => .done (result.get .here)).interpret CommonAdapter.project)
    view).trans (by
      apply congrArg (PIR.Process.interpret CommonAdapter.project)
      exact PIR.Process.bind_assoc _ _ _)

set_option maxRecDepth 20000 in
structured_associations GkrSourceViews
  [helper34 := GkrSourceBodies.helper34, helper36 := GkrSourceBodies.helper36,
    helper57 := GkrSourceBodies.helper57, helper69 := GkrSourceBodies.helper69,
    helper70 := GkrSourceBodies.helper70]

end ZkcSecurity.Realizations.Gkr.ProducerHelpers
