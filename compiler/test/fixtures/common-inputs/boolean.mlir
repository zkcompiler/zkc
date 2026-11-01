"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [], function_type = (i1, i1) -> i1, input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"]], origin = ["m::Run", []], output_roles = [["role00000000", "role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s1h6d3h52756e"}> ({
    ^bb0(%arg0: i1, %arg1: i1):
      %0 = "protocol.branch"(%arg0, %arg1) <{alternatives = ["then", "else"], output_roles = [["role00000000", "role00000001"]], roles = ["role00000000", "role00000001"], site = "s1"}> ({
      ^bb0(%arg3: i1):
        %2 = "protocol.branch"(%arg3) <{alternatives = ["then", "else"], output_roles = [["role00000000", "role00000001"]], roles = ["role00000000", "role00000001"], site = "branch_2_s1_arm_4_then_s2"}> ({
          %4 = "arith.constant"() <{value = true}> : () -> i1
          "protocol.yield"(%4) : (i1) -> ()
        }, {
          %3 = "arith.constant"() <{value = false}> : () -> i1
          "protocol.yield"(%3) : (i1) -> ()
        }) : (i1) -> i1
        "protocol.yield"(%2) : (i1) -> ()
      }, {
      ^bb0(%arg2: i1):
        %1 = "arith.constant"() <{value = false}> : () -> i1
        "protocol.yield"(%1) : (i1) -> ()
      }) : (i1, i1) -> i1
      "protocol.return"(%0) : (i1) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

