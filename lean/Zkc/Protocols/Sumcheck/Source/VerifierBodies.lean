module

public import Zkc.Source.Structured.ProtocolOperations
public import Zkc.Protocols.Sumcheck.Source.HelperBodies
public import Zkc.Protocols.Sumcheck.Source.PendingBodies

@[expose] public section

/-! Typed source patterns used by the Sumcheck mathematical library.
Applicability requires complete typed body equality in the admitted source;
names and signatures alone provide no law. Generated scalar library associations
prove these equalities in the kernel. -/
namespace ZkcExamples.Structured.SumcheckVerifierBodies
open Zkc.Source Zkc.Source.Structured

abbrev reduceInputs : List Ty :=
  [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]

abbrev reduceOutputs : List Ty :=
  [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"]

/-- The repeat-carried slots, which precede the unchanged outer SSA environment. -/
abbrev repeatState : List Ty :=
  [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"]

/-- The exact source repeat occurrence. -/
abbrev repeatSite : String := "s18"

/-- Exact callback guard occurrence 0. -/
abbrev roundGuardSite0 : String := "s27"

/-- The actual service input coordinate, before any local SSA extension. -/
abbrev serviceInput : String := "input_6"

abbrev repeatSpec (maximum : Nat) : RepeatSpec :=
  ⟨repeatState, [.service "random.bls12-381.fr/0"], [0, 1],
    [[0], [0], [0], [0], [1], [1]], maximum⟩

/-- The state positions the retained return reads, in output order. -/
abbrev reduceReturnIndices : List Nat := [3, 0, 1, 2, 4, 5]

/-- The retained return permutation of the repeat's state, for any value family. -/
def reduceReturnValues {Value : Ty → Type} (state : Values Value repeatState) :
    Values Value reduceOutputs :=
  .cons (state.get (.there (.there (.there .here)))) (.cons (state.get .here) (.cons (state.get (.there .here)) (.cons (state.get (.there (.there .here))) (.cons (state.get (.there (.there (.there (.there .here))))) (.cons (state.get (.there (.there (.there (.there (.there .here)))))) .nil)))))

/-- The retained return of the repeat's state. -/
def reduceReturn (tail : List Ty) : Region protocolDialect (repeatState ++ tail)
    reduceOutputs :=
  .letOp (.mark "s48") .nil .nil <|
  .letOp (.localCall SumcheckPendingBodies.atPrefixHelper rfl 1 "s48") (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)) .nil <|
  .ret (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons .here (.cons (.there .here) .nil))))))

/-- One iteration of the repeat: every retained operation, with its site mark. -/
def roundBody : Region protocolDialect
    (.index :: (repeatState ++ [.service "random.bls12-381.fr/0"])) repeatState :=
  .letOp (.mark "s19") .nil .nil <|
  .letOp (.localCall SumcheckHelperBodies.sumsHelper rfl 0 "s19") (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .letOp (.mark "label_726f756e64_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "label_726f756e64_1") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_1") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s27") .nil .nil <|
  .letOp (.guard 1 "s27") (.cons .here .nil) .nil <|
  .letOp (.mark "label_6368616c6c656e6765") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil) .nil <|
  .letOp (.mark "label_64656c6976657279_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "s32") .nil .nil <|
  .letOp (.localCall MapFirstBodies.firstHelper rfl 0 "s32") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons .here .nil)))) .nil <|
  .letOp (.mark "s34") .nil .nil <|
  .letOp (.localCall SumcheckHelperBodies.appendHelper rfl 0 "s34") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s36") .nil .nil <|
  .letOp (.localCall SumcheckHelperBodies.appendHelper rfl 1 "s36") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldConstant "bls12-381.fr" 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldSubtract "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))))))

/-- The whole body, with the repeat maximum as a parameter. -/
def reduceBody (maximum : Nat) : Region protocolDialect [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]
    [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke MapFirstBodies.widthHelper) rfl) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .indexEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.guard 0 "s3") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke MapFirstBodies.variablesHelper) rfl) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.localCall MapFirstBodies.lessHelper rfl 0 "s5") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate .booleanEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.guard 0 "s8") (.cons .here .nil) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.localCall SumcheckHelperBodies.emptyHelper rfl 0 "s10") .nil .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.localCall SumcheckPendingBodies.openClaimHelper rfl 1 "s12") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .nil)) .nil <|
  .letOp (.mark "s18") .nil .nil <|
  .letOp (.repeat (repeatSpec maximum) "s18") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there .here)) (.cons .here (.cons (.there .here) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil)))))))) (.cons roundBody .nil) <|
  reduceReturn _

end ZkcExamples.Structured.SumcheckVerifierBodies
