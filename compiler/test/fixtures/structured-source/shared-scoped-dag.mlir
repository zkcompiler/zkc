module { "protocol.module"() ({
func.func private @l0(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l0",[]]} {

%done = "exec.returned"(%a0) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>

}
func.func private @l1(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l1",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l0,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l0,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l2(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l2",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l1,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l1,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l3(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l3",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l2,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l2,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l4(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l4",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l3,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l3,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l5(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l5",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l4,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l4,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l6(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l6",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l5,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l5,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l7(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l7",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l6,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l6,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l8(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l8",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l7,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l7,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l9(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l9",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l8,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l8,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l10(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l10",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l9,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l9,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l11(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l11",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l10,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l10,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l12(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l12",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l11,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l11,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l13(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l13",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l12,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l12,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l14(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l14",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l13,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l13,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l15(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l15",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l14,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l14,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l16(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l16",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l15,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l15,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l17(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l17",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l16,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l16,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l18(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l18",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l17,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l17,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l19(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l19",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l18,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l18,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func private @l20(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["l20",[]]} {
%a_attempt = "func.call"(%scope,%a0) {callee=@l19,runtime.site="a"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%a_attempt)[^a,^failed] : (!exec.outcome<(i1)>)->()
^a(%a:i1):
%b_attempt = "func.call"(%scope,%a) {callee=@l19,runtime.site="b"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%b_attempt)[^b,^failed] : (!exec.outcome<(i1)>)->()
^b(%b:i1):
%done = "exec.returned"(%b) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
func.func @top(%scope:!runtime.scope,%a0:i1)->!exec.outcome<(i1)> attributes {no_inline,runtime.origin=["top",[]]} {
%value_attempt = "func.call"(%scope,%a0) {callee=@l20,runtime.site="r"} : (!runtime.scope,i1)->!exec.outcome<(i1)>
"exec.dispatch"(%value_attempt)[^value,^failed] : (!exec.outcome<(i1)>)->()
^value(%r:i1):
%done = "exec.returned"(%r) : (i1)->!exec.outcome<(i1)>
func.return %done : !exec.outcome<(i1)>
^failed(%reason:!exec.stop):
%failure = "exec.failed"(%reason) : (!exec.stop)->!exec.outcome<(i1)>
func.return %failure : !exec.outcome<(i1)>
}
"protocol.func"() ({ ^entry(%flag:i1):
  %r = "protocol.local_call"(%flag) {callee=@top,role="P",site="call"} : (i1)->i1
  "protocol.return"(%r) : (i1)->()
}) {sym_name="main",origin=["main",[]],function_type=(i1)->i1,roles=["P"],input_roles=[["P"]],output_roles=[["P"]]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
