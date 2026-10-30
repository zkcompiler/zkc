!U = !data.variant<#data.identity<["tuple", []]>, [#data.alternative<"value">]>
module { "protocol.module"() ({
  "protocol.func"() ({ ^entry(%a:!U,%b:!U):
    "protocol.return"(%b,%a) : (!U,!U)->()
  }) {sym_name="swap",origin=["swap",[]],function_type=(!U,!U)->(!U,!U),roles=["A","B"],input_roles=[["A","B"],["A","B"]],output_roles=[["A","B"],["A","B"]]} : ()->()
  "protocol.func"() ({ ^entry(%a:!U,%b:!U):
    %r:2 = protocol.apply @swap(%a,%b) {roles=["V","P"],site="zero"} : (!U,!U)->(!U,!U)
    "protocol.return"(%r#0,%r#1) : (!U,!U)->()
  }) {sym_name="main",origin=["main",[]],function_type=(!U,!U)->(!U,!U),roles=["P","V"],input_roles=[["P","V"],["P","V"]],output_roles=[["P","V"],["P","V"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
