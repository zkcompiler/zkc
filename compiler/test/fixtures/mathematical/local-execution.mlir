module {
"protocol.module"() ({
  "local.binding"() {sym_name="add", contract="field.add", arguments=["bls12-381.fr"], implementation=""} : () -> ()
  "local.binding"() {sym_name="require", contract="control.require", arguments=[], implementation=""} : () -> ()
  local.func @leaf(%x: !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr"> attributes {logical_origin=["leaf", []]} {
    %v = "algebra.exec.field_add"(%x, %x) {binding=@add, parameters=[], site="twice"} : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    local.return %v : !algebra.field<"bls12-381.fr">
  }
  local.func @work(%x: !algebra.field<"bls12-381.fr">, %resource: !local.capability<"rng:bls12-381.fr">, %go: i1) -> (!algebra.field<"bls12-381.fr">, !local.capability<"rng:bls12-381.fr">) attributes {logical_origin=["work", []]} {
    "local.if"(%go) ({
      "local.yield"() : () -> ()
    }, {
      "local.yield"() : () -> ()
    }) {site="authored_branch"} : (i1) -> ()
    %v = local.apply @leaf(%x) {site="nested"} : (!algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    local.return %v, %resource : !algebra.field<"bls12-381.fr">, !local.capability<"rng:bls12-381.fr">
  }
  local.func @check(%go: i1) attributes {logical_origin=["check", []]} {
    "local.exec.require"(%go) {binding=@require, parameters=[], site="required"} : (i1) -> ()
    local.return
  }
  "protocol.func"() ({
  ^entry(%x: !algebra.field<"bls12-381.fr">, %resource: !local.capability<"rng:bls12-381.fr">, %go: i1):
    %sum = algebra.field_add %x, %x : (!algebra.field<"bls12-381.fr">, !algebra.field<"bls12-381.fr">) -> !algebra.field<"bls12-381.fr">
    protocol.guard %go {owner="P", site="before_work"}
    "protocol.local_call"(%go) {callee=@check, role="P", site="first_check"} : (i1) -> ()
    "protocol.local_call"(%go) {callee=@check, role="P", site="second_check"} : (i1) -> ()
    %done:2 = "protocol.local_call"(%sum, %resource, %go) {callee=@work, role="P", site="work"} : (!algebra.field<"bls12-381.fr">, !local.capability<"rng:bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">, !local.capability<"rng:bls12-381.fr">)
    %sent = protocol.exchange %done#0 {sender="P", receiver="V", site="send"} : !algebra.field<"bls12-381.fr">
    "protocol.return"(%sent, %done#1) : (!algebra.field<"bls12-381.fr">, !local.capability<"rng:bls12-381.fr">) -> ()
  }) {sym_name="main", function_type=(!algebra.field<"bls12-381.fr">, !local.capability<"rng:bls12-381.fr">, i1) -> (!algebra.field<"bls12-381.fr">, !local.capability<"rng:bls12-381.fr">), roles=["P", "V"], input_roles=[["P"],["P"],["P"]], output_roles=[["P", "V"],["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> ()
}
