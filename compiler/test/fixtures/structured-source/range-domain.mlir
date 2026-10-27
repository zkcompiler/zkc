module { "protocol.module"() ({
  "data.domain"() ({
  ^entry(%lower:ui64,%upper:ui64):
    %items = "data.domain_range"(%lower,%upper) : (ui64,ui64)->!data.domain<ui64>
    "data.domain_yield"(%items) : (!data.domain<ui64>)->()
  }) {sym_name="items",sym_visibility="private",function_type=(ui64,ui64)->!data.domain<ui64>} : ()->()
  func.func private @step(%state:ui64,%item:ui64,%lower:ui64,%upper:ui64)->ui64 {
    func.return %item : ui64
  }
  "protocol.func"() ({
  ^entry(%lower:ui64,%upper:ui64,%seed:ui64):
    %result = "algebra.finite_fold"(%lower,%upper,%seed) {domain=@items,step=@step} : (ui64,ui64,ui64)->ui64
    "protocol.return"(%result) : (ui64)->()
  }) {sym_name="main",origin=["main",[]],function_type=(ui64,ui64,ui64)->ui64,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
