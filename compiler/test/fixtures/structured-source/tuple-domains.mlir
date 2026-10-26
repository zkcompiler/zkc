!F = !algebra.field<"bls12-381.fr">
!V = !algebra.field_vector<"bls12-381.fr">
module { "protocol.module"() ({
  "data.domain"() ({
  ^entry(%xs:!V,%ys:!V):
    %left = "data.domain_elements"(%xs) : (!V)->!data.domain<!F>
    %right = "data.domain_elements"(%ys) : (!V)->!data.domain<!F>
    %pairs = "data.domain_product"(%left,%right) : (!data.domain<!F>,!data.domain<!F>)->!data.domain<!F,!F>
    "data.domain_yield"(%pairs) : (!data.domain<!F,!F>)->()
  }) {sym_name="pairs",sym_visibility="private",function_type=(!V,!V)->!data.domain<!F,!F>} : ()->()
  func.func private @calculation(%state:!F,%a:!F,%b:!F,%xs:!V,%ys:!V)->!F {
    %ten = "algebra.constant"() {value="10"} : ()->!F
    %shifted = "algebra.field_multiply"(%state,%ten) : (!F,!F)->!F
    %difference = "algebra.field_subtract"(%a,%b) : (!F,!F)->!F
    %next = "algebra.field_add"(%shifted,%difference) : (!F,!F)->!F
    func.return %next : !F
  }
  func.func private @step(%scope:!runtime.scope,%state:!F,%a:!F,%b:!F,%xs:!V,%ys:!V)->!exec.outcome<(!F)>
      attributes {no_inline,runtime.origin=["step",[]]} {
    %result = "exec.compute"(%scope,%state,%a,%b,%xs,%ys) {callee=@calculation,site="calculate"}
        : (!runtime.scope,!F,!F,!F,!V,!V)->!exec.outcome<(!F)>
    "exec.dispatch"(%result)[^done,^stopped] : (!exec.outcome<(!F)>)->()
  ^done(%value:!F):
    %returned = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
    func.return %returned : !exec.outcome<(!F)>
  ^stopped(%cause:!exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<(!F)>
    func.return %failure : !exec.outcome<(!F)>
  }
  func.func private @fold(%scope:!runtime.scope,%xs:!V,%ys:!V,%seed:!F)->!exec.outcome<(!F)>
      attributes {no_inline,runtime.origin=["fold",[]]} {
    %result = "exec.fold"(%scope,%xs,%ys,%seed) {domain=@pairs,step=@step,site="fold"}
        : (!runtime.scope,!V,!V,!F)->!exec.outcome<(!F)>
    "exec.dispatch"(%result)[^done,^stopped] : (!exec.outcome<(!F)>)->()
  ^done(%value:!F):
    %returned = "exec.returned"(%value) : (!F)->!exec.outcome<(!F)>
    func.return %returned : !exec.outcome<(!F)>
  ^stopped(%cause:!exec.stop):
    %failure = "exec.failed"(%cause) : (!exec.stop)->!exec.outcome<(!F)>
    func.return %failure : !exec.outcome<(!F)>
  }
  "protocol.func"() ({
  ^entry(%xs:!V,%ys:!V,%seed:!F):
    %result = "protocol.local_call"(%xs,%ys,%seed) {callee=@fold,role="P",site="local"} : (!V,!V,!F)->!F
    "protocol.return"(%result) : (!F)->()
  }) {sym_name="main",origin=["main",[]],function_type=(!V,!V,!F)->!F,roles=["P"],input_roles=[["P"],["P"],["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
