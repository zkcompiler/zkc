"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "logical_record", "m::State", []], "affine", false, [["flag", ["bool"], ["data", ["A", "B"]]]], ["A", "B"], "zkl_resource_7cb03957bac6c8b651930fef74196de3580ef2a0bed2979d402452c3f451ceeb"]], [["s1h6d3h52756e", [["state", ["nominal", "logical_record", "m::State", []], ["role00000000", "role00000001"], 0 : ui64, 3 : ui64, ["product", ["role00000000", "role00000001"], [["data", ["role00000000", "role00000001"]]]]]], [["result", ["bool"], ["role00000000", "role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]]]], [["m::State", "acbb424947d3ce10211cdac71a9577e38fcd16f15dcbb2925723bc33a5d388dd"]]]}> ({
    "protocol.func"() <{contracts = [], function_type = (!runtime.capability<resource_unit, "zkl_resource_7cb03957bac6c8b651930fef74196de3580ef2a0bed2979d402452c3f451ceeb">, !runtime.capability<resource_unit, "zkl_resource_7cb03957bac6c8b651930fef74196de3580ef2a0bed2979d402452c3f451ceeb">, i1) -> i1, input_roles = [["role00000000"], ["role00000001"], ["role00000000", "role00000001"]], origin = ["m::Run", []], output_roles = [["role00000000", "role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s1h6d3h52756e"}> ({
    ^bb0(%arg0: !runtime.capability<resource_unit, "zkl_resource_7cb03957bac6c8b651930fef74196de3580ef2a0bed2979d402452c3f451ceeb">, %arg1: !runtime.capability<resource_unit, "zkl_resource_7cb03957bac6c8b651930fef74196de3580ef2a0bed2979d402452c3f451ceeb">, %arg2: i1):
      %0 = "protocol.branch"(%arg2) <{alternatives = ["then", "else"], output_roles = [["role00000000", "role00000001"]], roles = ["role00000000", "role00000001"], site = "s1"}> ({
        %2 = "arith.constant"() <{value = true}> : () -> i1
        "protocol.yield"(%2) : (i1) -> ()
      }, {
        %1 = "arith.constant"() <{value = false}> : () -> i1
        "protocol.yield"(%1) : (i1) -> ()
      }) : (i1) -> i1
      "protocol.return"(%0) : (i1) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

