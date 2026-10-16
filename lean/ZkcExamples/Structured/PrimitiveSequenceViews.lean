module

public import ZkcExamples.Structured.PrimitiveSequenceData
public import Zkc.Source.Structured.Linking
public import Zkc.Source.Structured.ClosedProfile

@[expose] public section

/-! Transparent typed views of complete retained original-stage constructor data.
Every view has an exact raw-body equality; the whole snapshot is kernel-admitted.
The original exporter and constructor renderer remain executable trust boundaries. -/

namespace ZkcExamples.Structured.PrimitiveSequenceViews
open Zkc.Source Zkc.Source.Structured
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option smartUnfolding false

def program : ClosedProgram :=
  (checkClosed PrimitiveSequenceData.snapshot).toOption.get (by decide +kernel)
def imported : ClosedImported PrimitiveSequenceData.snapshot := ⟨program, rfl⟩

set_option smartUnfolding true in
def entryBody : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index] [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil))))))))

theorem entry_exact : program.payload.entry.raw = entryBody.erase := rfl

def appendSummaryDefinition : CheckedDefinition :=
  (program.payload.definitions.find? (·.name == "s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279")).get (by decide +kernel)

abbrev appendSummaryHelper : Helper := ⟨"s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279", .local, [.vector "bls12-381.fr", .field "bls12-381.fr", .index], [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"]⟩

set_option smartUnfolding true in
def appendSummaryBody : Region dialect [.vector "bls12-381.fr", .field "bls12-381.fr", .index] [.vector "bls12-381.fr", .index, .index, .index, .field "bls12-381.fr", .boolean, .boolean, .vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorLength "bls12-381.fr")) (.cons .here .nil) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.exec (.indexAdd)) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr")) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.mark "s7") .nil .nil <|
  .letOp (.exec (.indexDiv)) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.mark "s9") .nil .nil <|
  .letOp (.exec (.indexMod)) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .nil <|
  .letOp (.mark "s11") .nil .nil <|
  .letOp (.exec (.indexConstant 1)) .nil .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.exec (.indexSub)) (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s14") .nil .nil <|
  .letOp (.exec (.vectorSum "bls12-381.fr")) (.cons (.there (.there (.there (.there .here)))) .nil) .nil <|
  .letOp (.mark "s16") .nil .nil <|
  .letOp (.exec (.vectorEqual "bls12-381.fr")) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .letOp (.mark "s18") .nil .nil <|
  .letOp (.exec (.fieldEqual "bls12-381.fr")) (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil)) .nil <|
  .letOp (.mark "s20") .nil .nil <|
  .letOp (.exec (.vectorEmpty "bls12-381.fr")) .nil .nil <|
  .ret (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there .here))) (.cons (.there (.there .here)) (.cons (.there .here) (.cons .here .nil))))))))

theorem appendSummary_exact : appendSummaryDefinition.raw = appendSummaryBody.erase := rfl

end ZkcExamples.Structured.PrimitiveSequenceViews
