module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.NativePrograms.Variants.SchnorrEarlyChallengeData

@[expose] public section

/-! Generated typed bodies and phased admission. -/
namespace ZkcExamples.NativePrograms.Variants.SchnorrEarlyChallengeInputs
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

def protocol0Signature : ProtocolSignature := (⟨"s13h7363686e6f72725f666f726d7322h4561726c794368616c6c656e676550726f746f636f6c", ["role00000000", "role00000001"], [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")], [.boolean], [[0, 1], [0, 1], [0], [0], [1]], [[1]]⟩ : ProtocolSignature)
def protocol0Body : Region protocolDialect protocol0Signature.inputs protocol0Signature.outputs :=
  (.letOp (.mark "s0") .nil .nil (.letOp (.draw 0 "bls12-381.fr" "s0") (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "label_6368616c6c656e6765") .nil .nil (.letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there .here)) (.cons (.there .here) .nil)) .nil (.letOp (.mark "label_636f6d6d69746d656e74_0") .nil .nil (.letOp (.exchange (.group "bls12-381.g1") 0 1 "label_636f6d6d69746d656e74_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.group "bls12-381.g1") [1]) (.cons .here .nil) .nil (.letOp (.mark "label_64656c6976657279_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldMultiply "bls12-381.fr") rfl) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldAdd "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there .here))))))) (.cons .here .nil)) .nil (.letOp (.mark "label_726573706f6e7365_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726573706f6e7365_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.groupAdd "bls12-381.g1") rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.groupEqual "bls12-381.g1") rfl) (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))))))))))))))))))))))))))))))

structured_views ZkcExamples.NativePrograms.Variants.SchnorrEarlyChallengeData.snapshot
  helpers []
  protocols [protocol0]

end
end ZkcExamples.NativePrograms.Variants.SchnorrEarlyChallengeInputs
