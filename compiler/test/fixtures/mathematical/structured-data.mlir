module { "protocol.module"() ({
 "protocol.func"() ({
 ^entry(%n: ui64, %x: !algebra.field<"bls12-381.fr">):
   %record = "data.make"(%n, %x) {alternative="record"} : (ui64, !algebra.field<"bls12-381.fr">) -> !data.variant<#data.identity<["atom", "StructuredRecord"]>, [#data.alternative<"record", [ui64, !algebra.field<"bls12-381.fr">]>]>
   %count = "data.get"(%record) {index=0:i64} : (!data.variant<#data.identity<["atom", "StructuredRecord"]>, [#data.alternative<"record", [ui64, !algebra.field<"bls12-381.fr">]>]>) -> ui64
   %value = "data.get"(%record) {index=1:i64} : (!data.variant<#data.identity<["atom", "StructuredRecord"]>, [#data.alternative<"record", [ui64, !algebra.field<"bls12-381.fr">]>]>) -> !algebra.field<"bls12-381.fr">
   %zero = "data.index"() {value=0 : ui64} : () -> ui64
   %empty = "data.array_from_elements"() : () -> !data.field_array<"bls12-381.fr", 0>
   %positive = "data.index_less"(%zero, %count) : (ui64, ui64) -> i1
   "protocol.return"(%record, %value, %positive, %empty) : (!data.variant<#data.identity<["atom", "StructuredRecord"]>, [#data.alternative<"record", [ui64, !algebra.field<"bls12-381.fr">]>]>, !algebra.field<"bls12-381.fr">, i1, !data.field_array<"bls12-381.fr", 0>) -> ()
 }) {sym_name="main", function_type=(ui64, !algebra.field<"bls12-381.fr">) -> (!data.variant<#data.identity<["atom", "StructuredRecord"]>, [#data.alternative<"record", [ui64, !algebra.field<"bls12-381.fr">]>]>, !algebra.field<"bls12-381.fr">, i1, !data.field_array<"bls12-381.fr", 0>), roles=["P"], input_roles=[["P"],["P"]], output_roles=[["P"],["P"],["P"],["P"]]} : () -> ()
}) {profile=#protocol.profile<protocol>} : () -> () }
