module

public import ZkcExamples.Structured.Generated.Scalar.SumcheckRepacked
public import ZkcExamples.Structured.SumcheckPendingLaws

@[expose] public section

/-! Checked associations of the mathematical library with the admitted source. -/
namespace ZkcExamples.Structured.Generated.Scalar.SumcheckRepackedLibrary
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcExamples.Structured.Generated.Scalar.SumcheckRepacked
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

abbrev pendingDefinition : CheckedDefinition := payload.definitions.get ⟨4, by decide +kernel⟩
abbrev pendingHelper : Helper := (⟨"zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper)
def pendingBody : Region dialect pendingHelper.inputs pendingHelper.outputs :=
  (.letOp (.mark "s0") .nil .nil (.letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil (.ret (.cons .here (.cons (.there .here) .nil)))))
theorem pending_closed (args : Values (assignment F G) pendingHelper.inputs) :
    invoke ((plainHelpers (F := F) (G := G) payload).closed) pendingHelper args =
      pendingBody.denote (Evaluation.meaning ((.silent _)) ((plainHelpers (F := F) (G := G) payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as ((.silent _)) payload.definitions payload.linked
    pendingDefinition (List.get_mem _ _) (⟨"zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) rfl pendingBody rfl args

theorem pending_pattern : pendingBody = SumcheckPendingBodies.pendingBody := by kernel_rfl

theorem pending_body : BodyIn payload.definitions SumcheckPendingBodies.pendingHelper SumcheckPendingBodies.pendingBody :=
  ⟨pendingDefinition, List.get_mem _ _, rfl, by kernel_rfl⟩

abbrev openClaimDefinition : CheckedDefinition := payload.definitions.get ⟨14, by decide +kernel⟩
abbrev openClaimHelper : Helper := (⟨"zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper)
def openClaimBody : Region dialect openClaimHelper.inputs openClaimHelper.outputs :=
  (.ret (.cons .here (.cons (.there .here) .nil)))
theorem openClaim_closed (args : Values (assignment F G) openClaimHelper.inputs) :
    invoke ((plainHelpers (F := F) (G := G) payload).closed) openClaimHelper args =
      openClaimBody.denote (Evaluation.meaning ((.silent _)) ((plainHelpers (F := F) (G := G) payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as ((.silent _)) payload.definitions payload.linked
    openClaimDefinition (List.get_mem _ _) (⟨"zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) rfl openClaimBody rfl args

theorem openClaim_pattern : openClaimBody = SumcheckPendingBodies.openClaimBody := by kernel_rfl

theorem openClaim_body : BodyIn payload.definitions SumcheckPendingBodies.openClaimHelper SumcheckPendingBodies.openClaimBody :=
  ⟨openClaimDefinition, List.get_mem _ _, rfl, by kernel_rfl⟩

abbrev atPrefixDefinition : CheckedDefinition := payload.definitions.get ⟨19, by decide +kernel⟩
abbrev atPrefixHelper : Helper := (⟨"zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper)
def atPrefixBody : Region dialect atPrefixHelper.inputs atPrefixHelper.outputs :=
  (.ret (.cons .here (.cons (.there .here) .nil)))
theorem atPrefix_closed (args : Values (assignment F G) atPrefixHelper.inputs) :
    invoke ((plainHelpers (F := F) (G := G) payload).closed) atPrefixHelper args =
      atPrefixBody.denote (Evaluation.meaning ((.silent _)) ((plainHelpers (F := F) (G := G) payload).closed)) args.get :=
  Evaluation.definitions_invoke_body_view_as ((.silent _)) payload.definitions payload.linked
    atPrefixDefinition (List.get_mem _ _) (⟨"zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) rfl atPrefixBody rfl args

theorem atPrefix_pattern : atPrefixBody = SumcheckPendingBodies.atPrefixBody := by kernel_rfl

theorem atPrefix_body : BodyIn payload.definitions SumcheckPendingBodies.atPrefixHelper SumcheckPendingBodies.atPrefixBody :=
  ⟨atPrefixDefinition, List.get_mem _ _, rfl, by kernel_rfl⟩

theorem claims : SumcheckPendingLaws.Bodies payload.definitions := ⟨pending_body, openClaim_body, atPrefix_body⟩

theorem reduce_body : Reduce.bodyBody = SumcheckVerifierBodies.reduceBody Reduce.roundMaximum := by kernel_rfl
theorem round_body : Reduce.roundBody = SumcheckVerifierBodies.roundBody := by kernel_rfl

end ZkcExamples.Structured.Generated.Scalar.SumcheckRepackedLibrary
