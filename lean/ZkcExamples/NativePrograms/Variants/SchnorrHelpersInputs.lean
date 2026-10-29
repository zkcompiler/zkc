module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.NativePrograms.Variants.SchnorrHelpersData

@[expose] public section

/-! Generated typed bodies and phased admission. -/
namespace ZkcExamples.NativePrograms.Variants.SchnorrHelpersInputs
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev helper0Helper : Helper := (⟨"s13h7363686e6f72725f666f726d738h726573706f6e7365", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)
def helper0Body : Region dialect helper0Helper.inputs helper0Helper.outputs :=
  (.letOp (.fieldMultiply "bls12-381.fr") (.cons (.there .here) (.cons (.there (.there .here)) .nil)) .nil (.letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))

abbrev helper1Helper : Helper := (⟨"s13h7363686e6f72725f666f726d738h6571756174696f6e", .math, [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩ : Helper)
def helper1Body : Region dialect helper1Helper.inputs helper1Helper.outputs :=
  (.letOp (.groupScale "bls12-381.g1" "bls12-381.fr") (.cons .here (.cons (.there (.there (.there (.there .here)))) .nil)) .nil (.letOp (.groupScale "bls12-381.g1" "bls12-381.fr") (.cons (.there (.there .here)) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil (.letOp (.groupAdd "bls12-381.g1") (.cons (.there (.there (.there (.there .here)))) (.cons .here .nil)) .nil (.letOp (.groupEqual "bls12-381.g1") (.cons (.there (.there .here)) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))))

def protocol0Signature : ProtocolSignature := (⟨"s13h7363686e6f72725f666f726d7315h48656c7065727350726f746f636f6c", ["role00000000", "role00000001"], [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")], [.boolean], [[0, 1], [0, 1], [0], [0], [1]], [[1]]⟩ : ProtocolSignature)
def protocol0Body : Region protocolDialect protocol0Signature.inputs protocol0Signature.outputs :=
  (.letOp (.mark "s0") .nil .nil (.letOp (.draw 0 "bls12-381.fr" "s0") (.cons (.there (.there (.there .here))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.groupScale "bls12-381.g1" "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.mark "label_636f6d6d69746d656e74_0") .nil .nil (.letOp (.exchange (.group "bls12-381.g1") 0 1 "label_636f6d6d69746d656e74_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.group "bls12-381.g1") [1]) (.cons .here .nil) .nil (.letOp (.mark "label_6368616c6c656e6765") .nil .nil (.letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil) .nil (.letOp (.mark "label_64656c6976657279_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.invoke (⟨"s13h7363686e6f72725f666f726d738h726573706f6e7365", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons .here (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil))) .nil (.letOp (.mark "label_726573706f6e7365_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_726573706f6e7365_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.invoke (⟨"s13h7363686e6f72725f666f726d738h6571756174696f6e", .math, [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩ : Helper)) rfl) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.cons (.there (.there (.there (.there (.there (.there .here)))))) (.cons (.there (.there (.there (.there (.there .here))))) (.cons .here .nil))))) .nil (.ret (.cons .here .nil))))))))))))))))))))))))

structured_views ZkcExamples.NativePrograms.Variants.SchnorrHelpersData.snapshot
  helpers [helper0, helper1]
  protocols [protocol0]

end
end ZkcExamples.NativePrograms.Variants.SchnorrHelpersInputs
