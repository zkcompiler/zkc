"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "logical_record", "m::State", []], "affine", false, [["flag", ["bool"], ["data", ["A", "B"]]]], ["A", "B"], "zkl_resource_da0889530ba2eef21e67d8f06b4e44b9a590fd0c7015c126908c7bb5d577d115"]], [["s1h6d3h52756e", [["state", ["nominal", "logical_record", "m::State", []], ["role00000000", "role00000001"], 0 : ui64, 3 : ui64, ["product", ["role00000000", "role00000001"], [["data", ["role00000000", "role00000001"]]]]]], [["result", ["bool"], ["role00000000", "role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000000", "role00000001"]]]]]], [["m::State", "c5d2d714a2e37334ab2de8484abb8a6609104576b45f28f52d062a347af4f5b4"]]]}> ({
    "protocol.func"() <{contracts = [], function_type = (!runtime.capability<resource_unit, "zkl_resource_da0889530ba2eef21e67d8f06b4e44b9a590fd0c7015c126908c7bb5d577d115">, !runtime.capability<resource_unit, "zkl_resource_da0889530ba2eef21e67d8f06b4e44b9a590fd0c7015c126908c7bb5d577d115">, i1) -> i1, input_roles = [["role00000000"], ["role00000001"], ["role00000000", "role00000001"]], origin = ["m::Run", []], output_roles = [["role00000000", "role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s1h6d3h52756e"}> ({
    ^bb0(%arg0: !runtime.capability<resource_unit, "zkl_resource_da0889530ba2eef21e67d8f06b4e44b9a590fd0c7015c126908c7bb5d577d115">, %arg1: !runtime.capability<resource_unit, "zkl_resource_da0889530ba2eef21e67d8f06b4e44b9a590fd0c7015c126908c7bb5d577d115">, %arg2: i1):
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

