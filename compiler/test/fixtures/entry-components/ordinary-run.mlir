"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "logical_record", "components::State", []], "ordinary", false, [["statement", ["index"]], ["witness", ["index"]], ["empty", ["unit"]]]]], [["s10h636f6d706f6e656e74735h526f756e64", [["state", ["nominal", "logical_record", "components::State", []], ["role00000000", "role00000001"], 0 : ui64, 2 : ui64]], [["result", ["bool"], ["role00000001"], 0 : ui64, 1 : ui64]]]]]}> ({
    "protocol.func"() <{contracts = [], function_type = (ui64, ui64) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000000"]], origin = ["components::Round", []], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s10h636f6d706f6e656e74735h526f756e64"}> ({
    ^bb0(%arg0: ui64, %arg1: ui64):
      %0 = "protocol.exchange"(%arg1) <{receiver = "role00000001", sender = "role00000000", site = "label_7265636569766564_0"}> : (ui64) -> ui64
      %1 = "protocol.restrict_roles"(%0) <{roles = ["role00000001"]}> : (ui64) -> ui64
      %2 = "data.index_equal"(%1, %arg0) : (ui64, ui64) -> i1
      "protocol.return"(%2) : (i1) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

