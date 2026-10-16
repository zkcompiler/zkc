"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.empty", implementation = "", sym_name = "zkl_binding_10"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "field.equal", implementation = "", sym_name = "zkl_binding_9"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.equal", implementation = "", sym_name = "zkl_binding_8"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.sum", implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.sub", implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.mod", implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.div", implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.append", implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.add", implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{contracts = [], function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"], ["role00000000"]], roles = ["role00000000"], sym_name = "s18h7072696d69746976655f6578616d706c65738h53657175656e6365"}> ({
    ^bb0(%arg3: !algebra.field_vector<"bls12-381.fr">, %arg4: !algebra.field<"bls12-381.fr">, %arg5: ui64):
      %12:8 = "protocol.local_call"(%arg3, %arg4, %arg5) <{callee = @s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">)
      "protocol.return"(%12#0, %12#1, %12#2, %12#3, %12#4, %12#5, %12#6, %12#7) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">), sym_name = "s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: !algebra.field<"bls12-381.fr">, %arg2: ui64):
      %0 = "algebra.exec.vector_length"(%arg0) <{binding = @zkl_binding_0, parameters = [], site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
      %1 = "algebra.exec.index_constant"() <{binding = @zkl_binding_1, parameters = ["1"], site = "s2"}> : () -> ui64
      %2 = "algebra.exec.index_add"(%0, %1) <{binding = @zkl_binding_2, parameters = [], site = "s3"}> : (ui64, ui64) -> ui64
      %3 = "algebra.exec.vector_append"(%arg0, %arg1) <{binding = @zkl_binding_3, parameters = [], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field_vector<"bls12-381.fr">
      %4 = "algebra.exec.index_div"(%2, %arg2) <{binding = @zkl_binding_4, parameters = [], site = "s7"}> : (ui64, ui64) -> ui64
      %5 = "algebra.exec.index_mod"(%2, %arg2) <{binding = @zkl_binding_5, parameters = [], site = "s9"}> : (ui64, ui64) -> ui64
      %6 = "algebra.exec.index_constant"() <{binding = @zkl_binding_1, parameters = ["1"], site = "s11"}> : () -> ui64
      %7 = "algebra.exec.index_sub"(%2, %6) <{binding = @zkl_binding_6, parameters = [], site = "s12"}> : (ui64, ui64) -> ui64
      %8 = "algebra.exec.vector_sum"(%3) <{binding = @zkl_binding_7, parameters = [], site = "s14"}> : (!algebra.field_vector<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
      %9 = "algebra.exec.vector_equal"(%arg0, %3) <{binding = @zkl_binding_8, parameters = [], site = "s16"}> : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> i1
      %10 = "algebra.exec.field_equal"(%8, %arg1) <{binding = @zkl_binding_9, parameters = [], site = "s18"}> : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> i1
      %11 = "algebra.exec.vector_empty"() <{binding = @zkl_binding_10, parameters = [], site = "s20"}> : () -> !algebra.field_vector<"bls12-381.fr">
      "local.return"(%3, %4, %5, %7, %8, %9, %10, %11) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64, ui64, !algebra.field<"bls12-381.fr">, i1, i1, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s18h7072696d69746976655f6578616d706c657314h617070656e645f73756d6d617279", []]} : () -> ()
  }) : () -> ()
}) : () -> ()

