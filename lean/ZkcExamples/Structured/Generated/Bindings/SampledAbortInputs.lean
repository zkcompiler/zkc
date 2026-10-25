module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.Generated.Bindings.SampledAbortData

@[expose] public section

/-! Generated typed bodies and phased admission. -/
namespace ZkcExamples.Structured.Generated.Bindings.SampledAbortInputs
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev helper0Helper : Helper := (⟨"zkf_fe5e2a3c5bbade8b5ce48ffd090142e127cc04ea947d1766a7f847161f657190", .math, [(.field "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩ : Helper)
def helper0Body : Region dialect helper0Helper.inputs helper0Helper.outputs :=
  (.letOp (.fieldEqual "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil (.ret (.cons .here .nil)))

def protocol0Signature : ProtocolSignature := (⟨"s7h6578616d706c6512h53616d706c656441626f7274", ["role00000000", "role00000001"], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")], [.boolean], [[0, 1], [0], [0], [1]], [[1]]⟩ : ProtocolSignature)
def protocol0Body : Region protocolDialect protocol0Signature.inputs protocol0Signature.outputs :=
  (.letOp (.mark "") .nil .nil (.letOp (.statement "s7h6578616d706c655h457175616c" [(.field "bls12-381.fr"), (.field "bls12-381.fr")] ["role00000001", "role00000000"] 0) (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "s0") .nil .nil (.letOp (.draw 0 "bls12-381.fr" "s0") (.cons (.there (.there .here)) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldConstant "bls12-381.fr" 0) rfl) .nil .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.fieldEqual "bls12-381.fr") rfl) (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.booleanConstant false) rfl) .nil .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate .booleanEqual rfl) (.cons (.there .here) (.cons .here .nil)) .nil (.letOp (.mark "s6") .nil .nil (.letOp (.guard 0 "s6") (.cons .here .nil) .nil (.letOp (.mark "label_636f6d6d69746d656e74_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 0 1 "label_636f6d6d69746d656e74_0") (.cons (.there (.there (.there (.there (.there .here))))) .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [1]) (.cons .here .nil) .nil (.letOp (.mark "label_6368616c6c656e6765") .nil .nil (.letOp (.draw 1 "bls12-381.fr" "label_6368616c6c656e6765") (.cons (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil) .nil (.letOp (.mark "label_64656c6976657279_0") .nil .nil (.letOp (.exchange (.field "bls12-381.fr") 1 0 "label_64656c6976657279_0") (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.restrict (.field "bls12-381.fr") [0]) (.cons .here .nil) .nil (.letOp (.mark "") .nil .nil (.letOp (.calculate (.booleanConstant true) rfl) .nil .nil (.ret (.cons .here .nil))))))))))))))))))))))))))))

structured_views ZkcExamples.Structured.Generated.Bindings.SampledAbortData.snapshot
  helpers [helper0]
  protocols [protocol0]

end
end ZkcExamples.Structured.Generated.Bindings.SampledAbortInputs
