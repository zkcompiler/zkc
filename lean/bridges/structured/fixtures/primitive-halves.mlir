"builtin.module"() ({
  "protocol.module"() <{profile = #protocol.profile<protocol>}> ({
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.split", implementation = "", sym_name = "zkl_binding_7"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.mul", implementation = "", sym_name = "zkl_binding_6"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.less", implementation = "", sym_name = "zkl_binding_5"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.div", implementation = "", sym_name = "zkl_binding_4"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.equal", implementation = "", sym_name = "zkl_binding_3"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.mod", implementation = "", sym_name = "zkl_binding_2"}> : () -> ()
    "local.binding"() <{arguments = ["bls12-381.fr"], contract = "vector.length", implementation = "", sym_name = "zkl_binding_1"}> : () -> ()
    "local.binding"() <{arguments = [], contract = "index.constant", implementation = "", sym_name = "zkl_binding_0"}> : () -> ()
    "protocol.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">), input_roles = [["role00000000"], ["role00000000"], ["role00000000"]], output_roles = [["role00000000"], ["role00000000"]], roles = ["role00000000"], sym_name = "s18h7072696d69746976655f6578616d706c657311h5461626c6548616c766573"}> ({
    ^bb0(%arg26: !algebra.field_vector<"bls12-381.fr">, %arg27: ui64, %arg28: ui64):
      %30:3 = "protocol.local_call"(%arg26, %arg27, %arg28) <{callee = @zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a, role = "role00000000", site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64)
      %31:2 = "protocol.local_call"(%30#0, %30#1, %30#2) <{callee = @zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087, role = "role00000000", site = "s2"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      "protocol.return"(%31#0, %31#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, ui64, ui64), sym_name = "zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a"}> ({
    ^bb0(%arg23: !algebra.field_vector<"bls12-381.fr">, %arg24: ui64, %arg25: ui64):
      %29 = "local.apply"(%arg23, %arg24, %arg25) <{callee = @zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655, site = "s0"}> : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.if"(%29) <{site = "s1"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s1_reject"}> : () -> ()
      }) : (i1) -> ()
      "local.return"(%arg23, %arg24, %arg25) : (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561725h7461626c65", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1, sym_name = "zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655"}> ({
    ^bb0(%arg8: !algebra.field_vector<"bls12-381.fr">, %arg9: ui64, %arg10: ui64):
      %11 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %12 = "local.apply"(%11, %arg10) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      %13 = "local.if"(%12, %arg9) <{site = "s3"}> ({
      ^bb0(%arg22: ui64):
        %27 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s4"}> : () -> ui64
        %28 = "local.apply"(%arg22, %27) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s5"}> : (ui64, ui64) -> i1
        "local.yield"(%28) : (i1) -> ()
      }, {
      ^bb0(%arg21: ui64):
        %26 = "local.bool_constant"() <{site = "s7", value = false}> : () -> i1
        "local.yield"(%26) : (i1) -> ()
      }) : (i1, ui64) -> i1
      %14 = "local.if"(%13, %arg8, %arg10) <{site = "s11"}> ({
      ^bb0(%arg19: !algebra.field_vector<"bls12-381.fr">, %arg20: ui64):
        %22 = "algebra.exec.vector_length"(%arg19) <{binding = @zkl_binding_1, parameters = [], site = "s12"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %23 = "algebra.exec.index_mod"(%22, %arg20) <{binding = @zkl_binding_2, parameters = [], site = "s13"}> : (ui64, ui64) -> ui64
        %24 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s14"}> : () -> ui64
        %25 = "algebra.exec.index_equal"(%23, %24) <{binding = @zkl_binding_3, parameters = [], site = "s15"}> : (ui64, ui64) -> i1
        "local.yield"(%25) : (i1) -> ()
      }, {
      ^bb0(%arg17: !algebra.field_vector<"bls12-381.fr">, %arg18: ui64):
        %21 = "local.bool_constant"() <{site = "s17", value = false}> : () -> i1
        "local.yield"(%21) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64) -> i1
      %15 = "local.if"(%14, %arg8, %arg9, %arg10) <{site = "s22"}> ({
      ^bb0(%arg14: !algebra.field_vector<"bls12-381.fr">, %arg15: ui64, %arg16: ui64):
        %17 = "algebra.exec.vector_length"(%arg14) <{binding = @zkl_binding_1, parameters = [], site = "s23"}> : (!algebra.field_vector<"bls12-381.fr">) -> ui64
        %18 = "algebra.exec.index_div"(%17, %arg16) <{binding = @zkl_binding_4, parameters = [], site = "s24"}> : (ui64, ui64) -> ui64
        %19 = "local.apply"(%arg15) <{callee = @s3h7a6b6311h6d756c74696c696e6561724h726f7773, site = "s25"}> : (ui64) -> ui64
        %20 = "algebra.exec.index_equal"(%18, %19) <{binding = @zkl_binding_3, parameters = [], site = "s26"}> : (ui64, ui64) -> i1
        "local.yield"(%20) : (i1) -> ()
      }, {
      ^bb0(%arg11: !algebra.field_vector<"bls12-381.fr">, %arg12: ui64, %arg13: ui64):
        %16 = "local.bool_constant"() <{site = "s28", value = false}> : () -> i1
        "local.yield"(%16) : (i1) -> ()
      }) : (i1, !algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> i1
      "local.return"(%15) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561729h6861735f7368617065", []]} : () -> ()
    "local.func"() <{function_type = (ui64, ui64) -> i1, sym_name = "s3h7a6b637h696e64696365734h6c657373"}> ({
    ^bb0(%arg6: ui64, %arg7: ui64):
      %10 = "algebra.exec.index_less"(%arg6, %arg7) <{binding = @zkl_binding_5, parameters = [], site = "s0"}> : (ui64, ui64) -> i1
      "local.return"(%10) : (i1) -> ()
    }) {logical_origin = ["s3h7a6b637h696e64696365734h6c657373", []]} : () -> ()
    "local.func"() <{function_type = (ui64) -> ui64, sym_name = "s3h7a6b6311h6d756c74696c696e6561724h726f7773"}> ({
    ^bb0(%arg3: ui64):
      %3 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["64"], site = "s0"}> : () -> ui64
      %4 = "local.apply"(%arg3, %3) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s1"}> : (ui64, ui64) -> i1
      "local.if"(%4) <{site = "s2"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s2_reject"}> : () -> ()
      }) : (i1) -> ()
      %5 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["1"], site = "s3"}> : () -> ui64
      %6 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s5"}> : () -> ui64
      %7 = "local.for"(%6, %arg3, %5) <{site = "s6"}> ({
      ^bb0(%arg4: ui64, %arg5: ui64):
        %8 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["2"], site = "s7"}> : () -> ui64
        %9 = "algebra.exec.index_mul"(%arg5, %8) <{binding = @zkl_binding_6, parameters = [], site = "s8"}> : (ui64, ui64) -> ui64
        "local.yield"(%9) : (ui64) -> ()
      }) : (ui64, ui64, ui64) -> ui64
      "local.return"(%7) : (ui64) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561724h726f7773", []]} : () -> ()
    "local.func"() <{function_type = (!algebra.field_vector<"bls12-381.fr">, ui64, ui64) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">), sym_name = "zkl_46021cb00c22207246296c081a0fe3ef9fa4e1d20f4a866fd01bfa4b37888087"}> ({
    ^bb0(%arg0: !algebra.field_vector<"bls12-381.fr">, %arg1: ui64, %arg2: ui64):
      %0 = "algebra.exec.index_constant"() <{binding = @zkl_binding_0, parameters = ["0"], site = "s0"}> : () -> ui64
      %1 = "local.apply"(%0, %arg1) <{callee = @s3h7a6b637h696e64696365734h6c657373, site = "s2"}> : (ui64, ui64) -> i1
      "local.if"(%1) <{site = "s3"}> ({
        "local.yield"() : () -> ()
      }, {
        "local.stop"() <{reason = "reject", site = "s3_reject"}> : () -> ()
      }) : (i1) -> ()
      %2:2 = "algebra.exec.vector_split"(%arg0) <{binding = @zkl_binding_7, parameters = [], site = "s5"}> : (!algebra.field_vector<"bls12-381.fr">) -> (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">)
      "local.return"(%2#0, %2#1) : (!algebra.field_vector<"bls12-381.fr">, !algebra.field_vector<"bls12-381.fr">) -> ()
    }) {logical_origin = ["s3h7a6b6311h6d756c74696c696e6561726h68616c766573", []]} : () -> ()
  }) : () -> ()
}) : () -> ()

