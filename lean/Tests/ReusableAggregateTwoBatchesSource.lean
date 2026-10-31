module

public import Tests.ReusableAggregateTwoBatchesData
public import Tests.ReusableAggregateTwoBatchesBodies
public import ZkcExamples.Structured.BatchOpeningConnection
public import Zkc.Protocols.TableMembership.BatchProtocolInstallation
public import Zkc.Source.Structured.BodyBindings
public import Zkc.Source.Structured.UnitViews
public meta import ZkcTools.StructuredSource.Association

@[expose] public section

/-! Exact source views for the fresh TwoBatches capture. Helper bodies are
installed from the reusable family; the root is checked against its full raw
source, including both batches and every ordered output. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace Tests.ReusableAggregateTwoBatchesSource
open Zkc.Source Zkc.Source.Structured
open Zkc.Protocols.TableMembership

/-- The current renderer preserves the same nominal record identity as the
helper family. Admission still checks these names against the new full source. -/
abbrev names := ZkcExamples.Structured.BatchOpeningConnection.names

abbrev protocolNames := ZkcExamples.Structured.BatchOpeningConnection.protocolNames
abbrev batchSignature := BatchSource.runSignature "koala-bear" names protocolNames

abbrev batchTy := Ty.sequence (BatchSource.openingTy "koala-bear" names)

abbrev pairSignature := ReusableAggregateTwoBatchesBodies.pairSignature

abbrev pairBody := ReusableAggregateTwoBatchesBodies.pairBody

structured_views ReusableAggregateTwoBatchesData.snapshot
  helpers [
    checkOpening := (BatchSource.checkOpeningHelper "koala-bear" names, BatchSource.checkOpeningBody "koala-bear" names),
    batchStep := (BatchSource.batchStepHelper "koala-bear" names, BatchSource.batchStepBody "koala-bear" names),
    batchValues := (BatchSource.batchValuesHelper "koala-bear" names, BatchSource.batchValuesBody "koala-bear" names),
    formula := (BatchSource.formulaHelper "koala-bear" names, BatchSource.formulaBody "koala-bear" names),
    mathematicalAdmission := (BatchSource.mathematicalAdmissionHelper "koala-bear" names, BatchSource.mathematicalAdmissionBody "koala-bear" names),
    checkBatch := (BatchSource.checkBatchHelper "koala-bear" names, BatchSource.checkBatchBody "koala-bear" names)
  ]
  protocols [run := (batchSignature, BatchSource.runBody "koala-bear" names protocolNames),
    pair := (pairSignature, pairBody)]

theorem bodies : BatchSource.Bodies unit.definitions "koala-bear" names := by
  bind_structured_bodies

def batchSource : Template.Association unit batchSignature
    (BatchSource.runBody "koala-bear" names protocolNames) := by
  derive_source_association

end Tests.ReusableAggregateTwoBatchesSource
