module { "protocol.module"() ({
 "protocol.func"() ({ ^entry(%choice:i1,%position:ui64,%upper:ui64,%go:i1):
   "protocol.branch"(%choice,%position,%upper,%go) ({
   ^then(%index:ui64,%bound:ui64,%enabled:i1):
     %less = "data.index_less"(%index,%bound) : (ui64,ui64)->i1
     protocol.guard %less {site="then_bound",owner="V"}
     protocol.guard %enabled {site="then_after",owner="V"}
     "protocol.yield"() : ()->()
   }, {
   ^else(%index:ui64,%bound:ui64,%enabled:i1):
     %less = "data.index_less"(%index,%bound) : (ui64,ui64)->i1
     protocol.guard %less {site="else_bound",owner="V"}
     "protocol.yield"() : ()->()
   }) {site="choose",roles=["P","V"],output_roles=[],alternatives=["then","else"]} : (i1,ui64,ui64,i1)->()
   protocol.guard %go {site="after",owner="V"}
   "protocol.return"() : ()->()
 }) {sym_name="main",function_type=(i1,ui64,ui64,i1)->(),roles=["P","V"],input_roles=[["P","V"],["V"],["V"],["V"]],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
