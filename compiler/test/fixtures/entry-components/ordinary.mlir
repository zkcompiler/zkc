"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>, source_declarations = [[[["nominal", "logical_record", "components::State", []], "ordinary", false, [["statement", ["index"], ["data", ["P", "V"]]], ["witness", ["index"], ["data", ["P"]]], ["empty", ["unit"], ["data", ["V"]]]], ["P", "V"], unit]], [["s10h636f6d706f6e656e74735h526f756e64", [["state", ["nominal", "logical_record", "components::State", []], ["role00000000", "role00000001"], 0 : ui64, 2 : ui64, ["product", ["role00000000", "role00000001"], [["data", ["role00000000", "role00000001"]], ["data", ["role00000000"]], ["data", ["role00000001"]]]]]], [["result", ["bool"], ["role00000001"], 0 : ui64, 1 : ui64, ["data", ["role00000001"]]]]]], [["components::State", "a83a14b2f0accd44e58e3fcc3a1060bb3eb4bc4022d53143f6d2e9b969dcbd3a"]]]}> ({
    "protocol.func"() <{contracts = [], function_type = (ui64, ui64) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000000"]], origin = ["components::Round", []], output_roles = [["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s10h636f6d706f6e656e74735h526f756e64"}> ({
    ^bb0(%arg0: ui64, %arg1: ui64):
      %0 = "protocol.exchange"(%arg1) <{receiver = "role00000001", sender = "role00000000", site = "label_7265636569766564_0"}> : (ui64) -> ui64
      %1 = "protocol.restrict_roles"(%0) <{roles = ["role00000001"]}> : (ui64) -> ui64
      %2 = "data.index_equal"(%1, %arg0) : (ui64, ui64) -> i1
      "protocol.return"(%2) : (i1) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

