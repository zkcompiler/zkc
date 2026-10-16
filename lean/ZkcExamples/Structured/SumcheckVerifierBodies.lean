module

public import Zkc.Source.Structured.ProtocolOperations
public import ZkcExamples.Structured.SumcheckHelperBodies

@[expose] public section

/-! One literal callback and maximum-parameterized full Reduce body. Original
complete-source clients establish their own raw-tree associations separately. -/
namespace ZkcExamples.Structured.SumcheckVerifierBodies
open Zkc.Source Zkc.Source.Structured
open MapFirstBodies (widthHelper variablesHelper lessHelper firstHelper)
open SumcheckHelperBodies (emptyHelper sumsHelper appendHelper)

abbrev reduceInputs : List Ty :=
  [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .index,
    .service "random.bls12-381.fr/0"]

abbrev reduceOutputs : List Ty :=
  [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index,
    .vector "bls12-381.fr", .field "bls12-381.fr"]

/-- The six repeat-carried slots precede the unchanged outer SSA environment. -/
abbrev repeatState : List Ty :=
  [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr",
    .vector "bls12-381.fr", .field "bls12-381.fr"]

/-- Return pointP first, residual entries second, then dimensions/columns,
pointV and the verifier claim. This is the actual retained return permutation. -/
def reduceReturn (tail : List Ty) : Region protocolDialect (repeatState ++ tail)
    reduceOutputs :=
  .ret (.cons (.there (.there (.there .here))) (.cons .here
    (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there (.there .here))))
        (.cons (.there (.there (.there (.there (.there .here))))) .nil))))))

abbrev repeatSpec (maximum : Nat) : RepeatSpec :=
  ⟨repeatState, [.service "random.bls12-381.fr/0"], [0, 1],
    [[0], [0], [0], [0], [1], [1]], maximum⟩

abbrev roundTailInputs : List Ty :=
  [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index,
    .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .boolean,
    .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"]

/-- The literal final calculations and selectors, with the older SSA context retained. -/
def roundTail (rest : List Ty) : Region protocolDialect (roundTailInputs ++ rest) repeatState :=
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

abbrev roundGuardInputs : List Ty :=
  [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr",
    .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] ++
    (.index :: (repeatState ++ [.service "random.bls12-381.fr/0"]))

/-- The literal region following the two restricted receive results. -/
def roundGuard : Region protocolDialect roundGuardInputs repeatState :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons .here .nil)) .nil <|
  .letOp (.mark "s24") .nil .nil <|
  .letOp (.guard 1 "s24") (.cons .here .nil) .nil <|
  .letOp (.mark "label_6368616c6c656e6765") .nil .nil <|
  .letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil) .nil <|
  .letOp (.mark "label_64656c6976657279_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil <|
  .letOp (.mark "s29") .nil .nil <|
  .letOp (.localCall firstHelper rfl 0 "s29") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons .here .nil)))) .nil <|
  .letOp (.mark "s31") .nil .nil <|
  .letOp (.localCall appendHelper rfl 0 "s31") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.there (.there (.there .here))) .nil)) .nil <|
  .letOp (.mark "s33") .nil .nil <|
  .letOp (.localCall appendHelper rfl 1 "s33") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil)) .nil <|
  roundTail _

/-- All original operations, including skipped prover work and internal marks. -/
def roundBody : Region protocolDialect
    (.index :: (repeatState ++ [.service "random.bls12-381.fr/0"])) repeatState :=
  .letOp (.mark "s16") .nil .nil <|
  .letOp (.localCall sumsHelper rfl 0 "s16") (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .letOp (.mark "label_726f756e64_0") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_0") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
  .letOp (.mark "label_726f756e64_1") .nil .nil <|
  .letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726f756e64_1") (.cons (.there (.there (.there .here))) .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil <|
  roundGuard

def reduceBody (maximum : Nat) : Region protocolDialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"] [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke widthHelper) rfl) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexEqual) rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.guard 0 "s3") (.cons .here .nil) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke variablesHelper) rfl) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil))) .nil <|
  .letOp (.mark "s5") .nil .nil <|
  .letOp (.localCall lessHelper rfl 0 "s5") (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanConstant false) rfl) .nil .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.booleanEqual) rfl) (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.mark "s8") .nil .nil <|
  .letOp (.guard 0 "s8") (.cons .here .nil) .nil <|
  .letOp (.mark "s10") .nil .nil <|
  .letOp (.localCall emptyHelper rfl 0 "s10") .nil .nil <|
  .letOp (.mark "s12") .nil .nil <|
  .letOp (.localCall emptyHelper rfl 1 "s12") .nil .nil <|
  .letOp (.mark "s15") .nil .nil <|
  .letOp (.repeat (repeatSpec maximum) "s15") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)))))))) (.cons roundBody .nil) <|
  reduceReturn _

end ZkcExamples.Structured.SumcheckVerifierBodies
