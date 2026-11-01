"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "logical_record", "m::State", []], "affine", false, [["flag", ["bool"]]]]], [["s1h6d3h52756e", [["state", ["nominal", "logical_record", "m::State", []], ["role00000000", "role00000001"], 0 : ui64, 3 : ui64]], [["result", ["bool"], ["role00000000", "role00000001"], 0 : ui64, 1 : ui64]]]]]}> ({
    "protocol.func"() <{contracts = [], function_type = (!runtime.capability<resource_unit, "zkl_resource_64df998cedfc9d6d50336e770ea8599a43e87d1576b14ea47999f531bc0c841e">, !runtime.capability<resource_unit, "zkl_resource_64df998cedfc9d6d50336e770ea8599a43e87d1576b14ea47999f531bc0c841e">, i1) -> i1, input_roles = [["role00000000"], ["role00000001"], ["role00000000", "role00000001"]], origin = ["m::Run", []], output_roles = [["role00000000", "role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s1h6d3h52756e"}> ({
    ^bb0(%arg0: !runtime.capability<resource_unit, "zkl_resource_64df998cedfc9d6d50336e770ea8599a43e87d1576b14ea47999f531bc0c841e">, %arg1: !runtime.capability<resource_unit, "zkl_resource_64df998cedfc9d6d50336e770ea8599a43e87d1576b14ea47999f531bc0c841e">, %arg2: i1):
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

