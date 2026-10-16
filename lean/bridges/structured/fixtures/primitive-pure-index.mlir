"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [], function_type = (ui64) -> i1, input_roles = [["role00000000"]], output_roles = [["role00000000"]], roles = ["role00000000", "role00000001"], sym_name = "s18h7072696d69746976655f6578616d706c65739h50757265496e646578"}> ({
    ^bb0(%arg0: ui64):
      %0 = "data.index"() <{value = "0"}> : () -> ui64
      %1 = "data.index_equal"(%arg0, %0) : (ui64, ui64) -> i1
      "protocol.return"(%1) : (i1) -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

