"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "protocol.func"() <{contracts = [], function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"]], output_roles = [["role00000000"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "s6h73616d706c653h52756e"}> ({
    ^bb0(%arg4: !algebra.field<"bls12-381.fr">, %arg5: !algebra.field<"bls12-381.fr">):
      %3:2 = "protocol.apply"(%arg4, %arg5) <{callee = @zkl_1029dffd30597bc82f81c8cfdb80d2ccd06b8fc9301525510f4cb8960568b1b0, roles = ["role00000000", "role00000001"], site = "s0"}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.return"(%3#0, %3#1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"]], output_roles = [["role00000000"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_1029dffd30597bc82f81c8cfdb80d2ccd06b8fc9301525510f4cb8960568b1b0"}> ({
    ^bb0(%arg2: !algebra.field<"bls12-381.fr">, %arg3: !algebra.field<"bls12-381.fr">):
      %2:2 = "protocol.apply"(%arg2, %arg3) <{callee = @zkl_f39ed99e9ca380a5675dcf66974ff8ba662cf37425e869e7bb6fe866ef82d479, roles = ["role00000001", "role00000000"], site = "s0"}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">)
      "protocol.apply"() <{callee = @s6h73616d706c657h4f627365727665, roles = ["role00000000", "role00000001"], site = "s3"}> : () -> ()
      "protocol.return"(%2#1, %2#0) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">), input_roles = [["role00000000", "role00000001"], ["role00000000", "role00000001"]], output_roles = [["role00000000"], ["role00000001"]], roles = ["role00000000", "role00000001"], sym_name = "zkl_f39ed99e9ca380a5675dcf66974ff8ba662cf37425e869e7bb6fe866ef82d479"}> ({
    ^bb0(%arg0: !algebra.field<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">):
      %0 = "algebra.field_add"(%arg0, %arg1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %1 = "algebra.field_multiply"(%arg0, %arg1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      "protocol.return"(%0, %1) : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> ()
    }) : () -> ()
    "protocol.func"() <{contracts = [], function_type = () -> (), input_roles = [], output_roles = [], roles = ["role00000000", "role00000001"], sym_name = "s6h73616d706c657h4f627365727665"}> ({
      "protocol.return"() : () -> ()
    }) : () -> ()
  }) : () -> ()
}) : () -> ()

