module

public import Zkc.Source.Structured.ProtocolOperations
public import ZkcExamples.Structured.SumcheckHelperBodies

@[expose] public section

/-! Literal full signatures and typed bodies. The corresponding Views module
proves admission of the complete original snapshot. -/
namespace ZkcExamples.Structured.SumcheckReduceBodies
open Zkc.Source Zkc.Source.Structured

abbrev mapHelper := MapFirstBodies.mapHelper
abbrev mapBody := MapFirstBodies.mapBody

abbrev tableHelper := MapFirstBodies.tableHelper
abbrev tableBody := MapFirstBodies.tableBody

abbrev shapeHelper := MapFirstBodies.shapeHelper
abbrev shapeBody := MapFirstBodies.shapeBody

abbrev lessHelper := MapFirstBodies.lessHelper
abbrev lessBody := MapFirstBodies.lessBody

abbrev rowsHelper := MapFirstBodies.rowsHelper
abbrev rowsBody := MapFirstBodies.rowsBody

abbrev widthHelper := MapFirstBodies.widthHelper
abbrev widthBody := MapFirstBodies.widthBody

abbrev variablesHelper := MapFirstBodies.variablesHelper
abbrev variablesBody := MapFirstBodies.variablesBody

abbrev emptyHelper := SumcheckHelperBodies.emptyHelper
abbrev emptyBody := SumcheckHelperBodies.emptyBody

abbrev sumsHelper := SumcheckHelperBodies.sumsHelper
abbrev sumsBody := SumcheckHelperBodies.sumsBody

abbrev halvesHelper := MapFirstBodies.halvesHelper
abbrev halvesBody := MapFirstBodies.halvesBody

abbrev firstHelper := MapFirstBodies.firstHelper
abbrev firstBody := MapFirstBodies.firstBody

abbrev interpolateHelper := MapFirstBodies.interpolateHelper
abbrev interpolateBody := MapFirstBodies.interpolateBody

abbrev appendHelper := SumcheckHelperBodies.appendHelper
abbrev appendBody := SumcheckHelperBodies.appendBody

abbrev valuesHelper := MapFirstBodies.valuesHelper
abbrev valuesBody := MapFirstBodies.valuesBody

def runSignature : ProtocolSignature where
  name := "zkl_cf3586ba980b617860654dacf2506dd277a78d1dcf5b84bcc6376225e7fe4f45"
  roles := ["role00000000", "role00000001"]
  inputs := [.vector "bls12-381.fr", .index, .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]
  outputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"]
  inputScopes := [[0], [0], [1], [0, 1], [1]]
  outputScopes := [[0], [0], [1], [1]]

def reduceSignature : ProtocolSignature where
  name := "zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d"
  roles := ["role00000000", "role00000001"]
  inputs := [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"]
  outputs := [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"]
  inputScopes := [[0], [0], [0], [1], [0, 1], [1]]
  outputScopes := [[0], [0], [0], [0], [1], [1]]

/-- The six repeat-carried slots precede the unchanged outer SSA environment. -/
abbrev repeatState : List Ty :=
  [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr",
    .vector "bls12-381.fr", .field "bls12-381.fr"]

/-- Return pointP first, residual entries second, then dimensions/columns,
pointV and the verifier claim. This is the actual retained return permutation. -/
def reduceReturn (tail : List Ty) : Region protocolDialect (repeatState ++ tail)
    reduceSignature.outputs :=
  .ret (.cons (.there (.there (.there .here))) (.cons .here
    (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there (.there .here))))
        (.cons (.there (.there (.there (.there (.there .here))))) .nil))))))

def reduceBody : Region protocolDialect [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"] [.vector "bls12-381.fr", .vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .field "bls12-381.fr"] :=
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
  .letOp (.repeat ⟨[.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.service "random.bls12-381.fr/0"], [0, 1], [[0], [0], [0], [0], [1], [1]], 4⟩ "s15") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)))))))) (.cons (
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
  .ret (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))))))) .nil) <|
  reduceReturn _

def runBody : Region protocolDialect [.vector "bls12-381.fr", .index, .field "bls12-381.fr", .index, .service "random.bls12-381.fr/0"] [.vector "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] :=
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.indexConstant 1) rfl) .nil .nil <|
  .letOp (.mark "s1") .nil .nil <|
  .letOp (.localCall tableHelper rfl 0 "s1") (.cons (.there .here) (.cons (.there (.there .here)) (.cons .here .nil))) .nil <|
  .letOp (.mark "s3") .nil .nil <|
  .letOp (.protocolApply reduceSignature [0, 1] "s3") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))))) .nil <|
  .letOp (.mark "") .nil .nil <|
  .letOp (.calculate (.invoke valuesHelper) rfl) (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) .nil))) .nil <|
  .ret (.cons (.there .here) (.cons .here (.cons (.there (.there (.there (.there (.there .here))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) .nil))))

end ZkcExamples.Structured.SumcheckReduceBodies
