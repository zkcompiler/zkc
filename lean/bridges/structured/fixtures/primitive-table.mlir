"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "local.binding"() <{arguments = [], contract = "index.mul", implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.less", implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.div", implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.equal", implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.mod", implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"], ["role00000000"], ["role00000000"]], roles = ["role00000000"], sym_name = "s18h7072696d69746976655f6578616d706c65739h4d616b655461626c65"}> ({
    ^bb0(%arg23: !algebra.field_vector<"bls12-381.fr">, %arg24: ui64, %arg25: ui64):
      %27:3 = "protocol.local_call"(%arg23, %arg24, %arg25) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      "protocol.return"(%27#0, %27#1, %27#2) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a"}> ({
    ^bb0(%arg20: !algebra.field_vector<"bls12-381.fr">, %arg21: ui64, %arg22: ui64):
      %26 = "local.apply"(%arg20, %arg21, %arg22) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.if"(%26) <{site = "s1"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s1_reject"}> : () -> ()
      }) : (i1) -> ()
      "local.return"(%arg20, %arg21, %arg22) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655"}> ({
    ^bb0(%arg5: !algebra.field_vector<"bls12-381.fr">, %arg6: ui64, %arg7: ui64):
      %8 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %9 = "local.apply"(%8, %arg7) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      %10 = "local.if"(%9, %arg6) <{site = "s3"}> ({
      ^bb0(%arg19: ui64):
        %24 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : () -> ui64
        %25 = "local.apply"(%arg19, %24) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s5"}> : (ui64, ui64) -> i1
        "local.yield"(%25) : (i1) -> ()
      }, {
      ^bb0(%arg18: ui64):
        %23 = "local.bool_constant"() <{site = "s7", value = false}> : () -> i1
        "local.yield"(%23) : (i1) -> ()
      }) : (i1, ui64) -> i1
      %11 = "local.if"(%10, %arg5, %arg7) <{site = "s11"}> ({
      ^bb0(%arg16: !algebra.field_vector<"bls12-381.fr">, %arg17: ui64):
        %19 = "algebra.exec.vector_length"(%arg16) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %20 = "algebra.exec.index_mod"(%19, %arg17) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (ui64, ui64) -> ui64
        %21 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : () -> ui64
        %22 = "algebra.exec.index_equal"(%20, %21) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (ui64, ui64) -> i1
        "local.yield"(%22) : (i1) -> ()
      }, {
      ^bb0(%arg14: !algebra.field_vector<"bls12-381.fr">, %arg15: ui64):
        %18 = "local.bool_constant"() <{site = "s17", value = false}> : () -> i1
        "local.yield"(%18) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64) -> i1
      %12 = "local.if"(%11, %arg5, %arg6, %arg7) <{site = "s22"}> ({
      ^bb0(%arg11: !algebra.field_vector<"bls12-381.fr">, %arg12: ui64, %arg13: ui64):
        %14 = "algebra.exec.vector_length"(%arg11) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %15 = "algebra.exec.index_div"(%14, %arg13) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (ui64, ui64) -> ui64
        %16 = "local.apply"(%arg12) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773, site = "s25"}> : (ui64) -> ui64
        %17 = "algebra.exec.index_equal"(%15, %16) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (ui64, ui64) -> i1
        "local.yield"(%17) : (i1) -> ()
      }, {
      ^bb0(%arg8: !algebra.field_vector<"bls12-381.fr">, %arg9: ui64, %arg10: ui64):
        %13 = "local.bool_constant"() <{site = "s28", value = false}> : () -> i1
        "local.yield"(%13) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.return"(%12) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "local.func"() <{function_type = (ui64, ui64) -> i1, sym_name = "s3h7a6b637h696e64696365734h6c657373"}> ({
    ^bb0(%arg3: ui64, %arg4: ui64):
      %7 = "algebra.exec.index_less"(%arg3, %arg4) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (ui64, ui64) -> i1
      "local.return"(%7) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "local.func"() <{function_type = (ui64) -> ui64, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773"}> ({
    ^bb0(%arg0: ui64):
      %0 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : () -> ui64
      %1 = "local.apply"(%arg0, %0) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      "local.if"(%1) <{site = "s2"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s2_reject"}> : () -> ()
      }) : (i1) -> ()
      %2 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : () -> ui64
      %3 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : () -> ui64
      %4 = "local.for"(%3, %arg0, %2) <{site = "s6"}> ({
      ^bb0(%arg1: ui64, %arg2: ui64):
        %5 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : () -> ui64
        %6 = "algebra.exec.index_mul"(%arg2, %5) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
        "local.yield"(%6) : (ui64) -> ()
      }) : (ui64, ui64, ui64) -> ui64
      "local.return"(%4) : (ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
  }) : () -> ()
}) : () -> ()

