!F = !algebra.field<"bls12-381.fr">
module { "protocol.module"() ({
  func.func private @first(%x:!F,%ignored:!F) -> !F {
    func.return %x : !F
  }
  func.func private @nested(%x:!F,%y:!F) -> !F {
    %r = func.call @first(%x,%y) : (!F,!F)->!F
    func.return %r : !F
  }
  func.func private @split(%x:!F,%y:!F) -> (!F,!F) {
    func.return %x,%y : !F,!F
  }
  func.func private @constant(%ignored:!F) -> !F {
    %five = "algebra.constant"() {value="5"} : ()->!F
    func.return %five : !F
  }
  "protocol.func"() ({
  ^entry(%x:!F,%y:!F):
    %a = func.call @nested(%x,%y) : (!F,!F)->!F
    %b:2 = func.call @split(%x,%y) : (!F,!F)->(!F,!F)
    %c = func.call @constant(%y) : (!F)->!F
    "protocol.return"(%a,%b#0,%b#1,%c) : (!F,!F,!F,!F)->()
  }) {sym_name="main",origin=["main",[]],function_type=(!F,!F)->(!F,!F,!F,!F),roles=["P","V"],input_roles=[["P"],["V"]],output_roles=[["P"],["P"],["V"],["P","V"]]} : ()->()
  "protocol.func"() ({
  ^entry(%x:!F):
    "protocol.return"(%x) : (!F)->()
  }) {sym_name="other",origin=["other",[]],function_type=(!F)->!F,roles=["Reader","Writer","Auditor"],input_roles=[["Auditor"]],output_roles=[["Auditor"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
