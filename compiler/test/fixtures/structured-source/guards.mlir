module { "protocol.module"() ({
"protocol.func"() ({ ^entry(%flag:i1):
  protocol.guard %flag {owner="P",site="check"}
  "protocol.return"(%flag) : (i1)->()
}) {sym_name="main",origin=["main",[]],function_type=(i1)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
