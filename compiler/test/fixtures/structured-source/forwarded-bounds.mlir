!F = !algebra.field<"bls12-381.fr">
!V = !data.field_vector<"bls12-381.fr">
module {
  "protocol.module"() ({
    "data.domain"() ({
    ^entry(%xs: !V, %ys: !V):
      %d = "data.domain_indices"(%xs) {axis = 0 : i64} : (!V) -> !data.domain<ui64>
      "data.domain_yield"(%d) : (!data.domain<ui64>) -> ()
    }) {sym_name = "items", sym_visibility = "private", function_type = (!V, !V) -> !data.domain<ui64>} : () -> ()
    func.func private @permute(%xs: !V, %ys: !V, %i: ui64) -> (!V, ui64, !V, !V) {
      func.return %ys, %i, %xs, %xs : !V, ui64, !V, !V
    }
    func.func private @forward(%xs: !V, %ys: !V, %i: ui64) -> (!V, ui64) {
      %p:4 = func.call @permute(%xs, %ys, %i) : (!V, !V, ui64) -> (!V, ui64, !V, !V)
      func.return %p#3, %p#1 : !V, ui64
    }
    func.func private @read(%xs: !V, %i: ui64) -> !F attributes {data.preconditions = [#data.index_bound<1, 0, 0>]} {
      %v = "data.bounded_at"(%xs, %i) : (!V, ui64) -> !F
      func.return %v : !F
    }
    func.func private @step(%state: !F, %i: ui64, %xs: !V, %ys: !V) -> !F attributes {data.preconditions = [#data.index_bound<1, 2, 0>]} {
      %forward:2 = func.call @forward(%xs, %ys, %i) : (!V, !V, ui64) -> (!V, ui64)
      %v = func.call @read(%forward#0, %forward#1) : (!V, ui64) -> !F
      %next = algebra.field_add %state, %v : (!F, !F) -> !F
      func.return %next : !F
    }
    "protocol.func"() ({
    ^entry(%xs: !V, %ys: !V, %seed: !F):
      %r = "data.finite_fold"(%xs, %ys, %seed) {domain = @items, step = @step} : (!V, !V, !F) -> !F
      "protocol.return"(%r) : (!F) -> ()
    }) {sym_name = "main",origin=["main",[]], function_type = (!V, !V, !F) -> !F, roles = ["P"], input_roles = [["P"], ["P"], ["P"]], output_roles = [["P"]]} : () -> ()
  }) {profile = #protocol.profile<protocol>} : () -> ()
}
