!V = !data.field_vector<"bls12-381.fr">
module {
  "protocol.module"() ({
    func.func private @length(%values: !V) -> ui64 {
      %size = "data.dim"(%values) {axis=0:i64} : (!V)->ui64
      func.return %size : ui64
    }
    func.func private @choose(%outer:i1, %inner:i1, %left:!V, %right:!V) -> (!V,ui64) {
      %values, %size = "data.branch"(%outer,%inner,%left,%right) ({
      ^then(%condition:i1,%a:!V,%b:!V):
        %selected = "data.branch"(%condition,%a,%b) ({
        ^then(%x:!V,%y:!V):
          "data.yield"(%x) : (!V)->()
        }, {
        ^else(%x:!V,%y:!V):
          "data.yield"(%y) : (!V)->()
        }) {alternatives=["then","else"]} : (i1,!V,!V)->!V
        %count = func.call @length(%selected) : (!V)->ui64
        "data.yield"(%selected,%count) : (!V,ui64)->()
      }, {
      ^else(%condition:i1,%a:!V,%b:!V):
        %count = func.call @length(%b) : (!V)->ui64
        "data.yield"(%b,%count) : (!V,ui64)->()
      }) {alternatives=["then","else"]} : (i1,i1,!V,!V)->(!V,ui64)
      func.return %values,%size : !V,ui64
    }
    "protocol.func"() ({
    ^entry(%outer:i1,%inner:i1,%left:!V,%right:!V):
      %first,%size = func.call @choose(%outer,%inner,%left,%right) : (i1,i1,!V,!V)->(!V,ui64)
      %second,%other = func.call @choose(%inner,%outer,%right,%left) : (i1,i1,!V,!V)->(!V,ui64)
      "protocol.return"(%first,%size,%second,%other) : (!V,ui64,!V,ui64)->()
    }) {sym_name="main",origin=["main",[]],function_type=(i1,i1,!V,!V)->(!V,ui64,!V,ui64),
        roles=["P"],input_roles=[["P"],["P"],["P"],["P"]],output_roles=[["P"],["P"],["P"],["P"]]} : ()->()
  }) {profile=#protocol.profile<protocol>} : ()->()
}
