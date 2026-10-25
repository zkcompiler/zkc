module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%n: ui64, %x: !algebra.field<"bls12-381.fr">):
   %record = "data.make"(%n, %x) {alternative="record"} : (ui64, !algebra.field<"bls12-381.fr">) -> !data.variant<"variant:5b227a6b632e76617269616e742f30222c5b22537472756374757265645265636f7264222c227265636f7264222c22696e646578222c226669656c643a626c7331322d3338312e6672222c5b2232222c2233225d2c5b2231222c2234225d2c5b2235225d2c5b2230222c2236225d5d5d">
   %count = "data.get"(%record) {index=0:i64} : (!data.variant<"variant:5b227a6b632e76617269616e742f30222c5b22537472756374757265645265636f7264222c227265636f7264222c22696e646578222c226669656c643a626c7331322d3338312e6672222c5b2232222c2233225d2c5b2231222c2234225d2c5b2235225d2c5b2230222c2236225d5d5d">) -> ui64
   %value = "data.get"(%record) {index=1:i64} : (!data.variant<"variant:5b227a6b632e76617269616e742f30222c5b22537472756374757265645265636f7264222c227265636f7264222c22696e646578222c226669656c643a626c7331322d3338312e6672222c5b2232222c2233225d2c5b2231222c2234225d2c5b2235225d2c5b2230222c2236225d5d5d">) -> !algebra.field<"bls12-381.fr">
   %zero = "data.index"() {value="0"} : () -> ui64
   %empty = "algebra.array_from_elements"() : () -> !algebra.field_array<"bls12-381.fr", 0>
   %positive = "data.index_less"(%zero, %count) : (ui64, ui64) -> i1
   "protocol.return"(%record, %value, %positive, %empty) : (!data.variant<"variant:5b227a6b632e76617269616e742f30222c5b22537472756374757265645265636f7264222c227265636f7264222c22696e646578222c226669656c643a626c7331322d3338312e6672222c5b2232222c2233225d2c5b2231222c2234225d2c5b2235225d2c5b2230222c2236225d5d5d">, !algebra.field<"bls12-381.fr">, i1, !algebra.field_array<"bls12-381.fr", 0>) -> ()
 }) {sym_name="main", function_type=(ui64, !algebra.field<"bls12-381.fr">) -> (!data.variant<"variant:5b227a6b632e76617269616e742f30222c5b22537472756374757265645265636f7264222c227265636f7264222c22696e646578222c226669656c643a626c7331322d3338312e6672222c5b2232222c2233225d2c5b2231222c2234225d2c5b2235225d2c5b2230222c2236225d5d5d">, !algebra.field<"bls12-381.fr">, i1, !algebra.field_array<"bls12-381.fr", 0>), roles=["P"], input_roles=[["P"],["P"]], output_roles=[["P"],["P"],["P"],["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
