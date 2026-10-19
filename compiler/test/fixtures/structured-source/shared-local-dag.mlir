module { "protocol.module"() ({
local.func private @l0(%x:i1) -> i1 attributes {logical_origin=["l0",[]]} { local.return %x : i1 }
local.func private @l1(%x:i1) -> i1 attributes {logical_origin=["l1",[]]} {
  %a = local.apply @l0(%x) {site="a"} : (i1)->i1
  %b = local.apply @l0(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l2(%x:i1) -> i1 attributes {logical_origin=["l2",[]]} {
  %a = local.apply @l1(%x) {site="a"} : (i1)->i1
  %b = local.apply @l1(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l3(%x:i1) -> i1 attributes {logical_origin=["l3",[]]} {
  %a = local.apply @l2(%x) {site="a"} : (i1)->i1
  %b = local.apply @l2(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l4(%x:i1) -> i1 attributes {logical_origin=["l4",[]]} {
  %a = local.apply @l3(%x) {site="a"} : (i1)->i1
  %b = local.apply @l3(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l5(%x:i1) -> i1 attributes {logical_origin=["l5",[]]} {
  %a = local.apply @l4(%x) {site="a"} : (i1)->i1
  %b = local.apply @l4(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l6(%x:i1) -> i1 attributes {logical_origin=["l6",[]]} {
  %a = local.apply @l5(%x) {site="a"} : (i1)->i1
  %b = local.apply @l5(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l7(%x:i1) -> i1 attributes {logical_origin=["l7",[]]} {
  %a = local.apply @l6(%x) {site="a"} : (i1)->i1
  %b = local.apply @l6(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l8(%x:i1) -> i1 attributes {logical_origin=["l8",[]]} {
  %a = local.apply @l7(%x) {site="a"} : (i1)->i1
  %b = local.apply @l7(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l9(%x:i1) -> i1 attributes {logical_origin=["l9",[]]} {
  %a = local.apply @l8(%x) {site="a"} : (i1)->i1
  %b = local.apply @l8(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l10(%x:i1) -> i1 attributes {logical_origin=["l10",[]]} {
  %a = local.apply @l9(%x) {site="a"} : (i1)->i1
  %b = local.apply @l9(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l11(%x:i1) -> i1 attributes {logical_origin=["l11",[]]} {
  %a = local.apply @l10(%x) {site="a"} : (i1)->i1
  %b = local.apply @l10(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l12(%x:i1) -> i1 attributes {logical_origin=["l12",[]]} {
  %a = local.apply @l11(%x) {site="a"} : (i1)->i1
  %b = local.apply @l11(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l13(%x:i1) -> i1 attributes {logical_origin=["l13",[]]} {
  %a = local.apply @l12(%x) {site="a"} : (i1)->i1
  %b = local.apply @l12(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l14(%x:i1) -> i1 attributes {logical_origin=["l14",[]]} {
  %a = local.apply @l13(%x) {site="a"} : (i1)->i1
  %b = local.apply @l13(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l15(%x:i1) -> i1 attributes {logical_origin=["l15",[]]} {
  %a = local.apply @l14(%x) {site="a"} : (i1)->i1
  %b = local.apply @l14(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l16(%x:i1) -> i1 attributes {logical_origin=["l16",[]]} {
  %a = local.apply @l15(%x) {site="a"} : (i1)->i1
  %b = local.apply @l15(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l17(%x:i1) -> i1 attributes {logical_origin=["l17",[]]} {
  %a = local.apply @l16(%x) {site="a"} : (i1)->i1
  %b = local.apply @l16(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l18(%x:i1) -> i1 attributes {logical_origin=["l18",[]]} {
  %a = local.apply @l17(%x) {site="a"} : (i1)->i1
  %b = local.apply @l17(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l19(%x:i1) -> i1 attributes {logical_origin=["l19",[]]} {
  %a = local.apply @l18(%x) {site="a"} : (i1)->i1
  %b = local.apply @l18(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func private @l20(%x:i1) -> i1 attributes {logical_origin=["l20",[]]} {
  %a = local.apply @l19(%x) {site="a"} : (i1)->i1
  %b = local.apply @l19(%a) {site="b"} : (i1)->i1
  local.return %b : i1
}
local.func @top(%x:i1) -> i1 attributes {logical_origin=["top",[]]} {
  %r = local.apply @l20(%x) {site="r"} : (i1)->i1
  local.return %r : i1
}
"protocol.func"() ({ ^entry(%flag:i1):
  %r = "protocol.local_call"(%flag) {callee=@top,role="P",site="call"} : (i1)->i1
  "protocol.return"(%r) : (i1)->()
}) {sym_name="main",function_type=(i1)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
