module { "protocol.module"() ({
"protocol.func"() ({
^entry(%a: tensor<4x!algebra.field<"bls12-381.fr">>, %b: tensor<4x!algebra.field<"bls12-381.fr">>, %x: !algebra.field<"bls12-381.fr">):
 %pa = "poly.from_coefficients"(%a) : (tensor<4x!algebra.field<"bls12-381.fr">>) -> !poly.polynomial<"bls12-381.fr", 1>
 %pb = "poly.from_coefficients"(%b) : (tensor<4x!algebra.field<"bls12-381.fr">>) -> !poly.polynomial<"bls12-381.fr", 1>
 %product = "poly.multiply"(%pa, %pb) : (!poly.polynomial<"bls12-381.fr", 1>, !poly.polynomial<"bls12-381.fr", 1>) -> !poly.polynomial<"bls12-381.fr", 1>
 %coefficients = "poly.coefficients"(%product) : (!poly.polynomial<"bls12-381.fr", 1>) -> tensor<7x!algebra.field<"bls12-381.fr">>
 %values = "poly.evaluate_domain"(%product) {points=["3", "10395434478220956956328808592063228334810757406296085889024", "52435875175126190479447740508185965837690552500527637822603658699938581184510", "52435875175126190469052306029965008881361743908464409487792901293642495295489"]} : (!poly.polynomial<"bls12-381.fr", 1>) -> tensor<4x!algebra.field<"bls12-381.fr">>
 %interpolant = "poly.interpolate"(%values) {points=["3", "10395434478220956956328808592063228334810757406296085889024", "52435875175126190479447740508185965837690552500527637822603658699938581184510", "52435875175126190469052306029965008881361743908464409487792901293642495295489"]} : (tensor<4x!algebra.field<"bls12-381.fr">>) -> !poly.polynomial<"bls12-381.fr", 1>
 %interpolated = "poly.coefficients"(%interpolant) : (!poly.polynomial<"bls12-381.fr", 1>) -> tensor<4x!algebra.field<"bls12-381.fr">>
 %formal = "poly.evaluate"(%product, %x) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 %finite = "poly.evaluate"(%interpolant, %x) : (!poly.polynomial<"bls12-381.fr", 1>, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
 "protocol.return"(%coefficients, %interpolated, %values, %formal, %finite) : (tensor<7x!algebra.field<"bls12-381.fr">>, tensor<4x!algebra.field<"bls12-381.fr">>, tensor<4x!algebra.field<"bls12-381.fr">>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
}) {sym_name="main", function_type=(tensor<4x!algebra.field<"bls12-381.fr">>, tensor<4x!algebra.field<"bls12-381.fr">>, !algebra.field<"bls12-381.fr">) -> (tensor<7x!algebra.field<"bls12-381.fr">>, tensor<4x!algebra.field<"bls12-381.fr">>, tensor<4x!algebra.field<"bls12-381.fr">>, !algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), roles=["Solo"], input_roles=[["Solo"],["Solo"],["Solo"]], output_roles=[["Solo"],["Solo"],["Solo"],["Solo"],["Solo"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
