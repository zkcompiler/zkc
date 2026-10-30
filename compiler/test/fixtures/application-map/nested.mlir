module { "protocol.module"() ({
  func.func private @flip(%a:i1,%b:i1)->(i1,i1) {
    %both = arith.andi %a,%b : i1
    return %b,%both : i1,i1
  }
  "protocol.func"() ({ ^entry(%a:i1,%b:i1):
    "protocol.return"(%b,%a) : (i1,i1)->()
  }) {sym_name="empty",origin=["empty",[]],function_type=(i1,i1)->(i1,i1),roles=["A","B"],input_roles=[["A","B"],["A","B"]],output_roles=[["A","B"],["A","B"]]} : ()->()
  "protocol.func"() ({ ^entry(%a:i1,%b:i1):
    protocol.guard %a {owner="A",site="check"}
    %r:2 = protocol.apply @empty(%b,%a) {roles=["B","A"],site="inner"} : (i1,i1)->(i1,i1)
    %p:2 = func.call @flip(%r#0,%r#1) : (i1,i1)->(i1,i1)
    "protocol.return"(%p#0,%p#1) : (i1,i1)->()
  }) {sym_name="child",origin=["child",[]],function_type=(i1,i1)->(i1,i1),roles=["A","B"],input_roles=[["A","B"],["A","B"]],output_roles=[["A","B"],["A","B"]]} : ()->()
  "protocol.func"() ({
    "protocol.return"() : ()->()
  }) {sym_name="zero",origin=["zero",[]],function_type=()->(),roles=["A","B"],input_roles=[],output_roles=[]} : ()->()
  "protocol.func"() ({ ^entry(%n:ui64,%x:i1,%y:i1):
    %a:2 = protocol.apply @child(%x,%y) {roles=["P","V"],site="first"} : (i1,i1)->(i1,i1)
    %b:2 = protocol.apply @child(%y,%x) {roles=["V","P"],site="second"} : (i1,i1)->(i1,i1)
    protocol.apply @zero() {roles=["P","V"],site="empty"} : ()->()
    "protocol.repeat"(%n,%x,%y) ({ ^body(%i:ui64,%cx:i1,%cy:i1):
      %r:2 = protocol.apply @empty(%cx,%cy) {roles=["P","V"],site="iteration"} : (i1,i1)->(i1,i1)
      "protocol.yield"() : ()->()
    }) {site="loop",carried=0:i64,maximum=2:i64,roles=["P","V"],carried_roles=[]} : (ui64,i1,i1)->()
    "protocol.return"(%a#0,%b#1) : (i1,i1)->()
  }) {sym_name="main",origin=["main",[]],function_type=(ui64,i1,i1)->(i1,i1),roles=["P","V"],input_roles=[["P","V"],["P","V"],["P","V"]],output_roles=[["P","V"],["P","V"]]} : ()->()
  "protocol.func"() ({ ^entry(%a:i1,%b:i1):
    protocol.guard %a {owner="Reader",site="dormant"}
    "protocol.return"(%b) : (i1)->()
  }) {sym_name="unused",origin=["unused",[]],function_type=(i1,i1)->i1,roles=["Reader","Writer"],input_roles=[["Reader","Writer"],["Reader","Writer"]],output_roles=[["Reader","Writer"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
