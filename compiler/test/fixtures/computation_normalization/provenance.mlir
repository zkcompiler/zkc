!F = !algebra.field<"bls12-381.fr">
!A = !data.field_array<"bls12-381.fr", 2>
!P = !poly.polynomial<"bls12-381.fr", 1>
module { "protocol.module"() ({
 func.func private @leaf(%a:!F,%b:!F)->(!F,!F,!F) {
   %dead = algebra.field_multiply %a,%b : (!F,!F)->!F
   %first = algebra.field_multiply %a,%b : (!F,!F)->!F
   %second = algebra.field_multiply %a,%b : (!F,!F)->!F
   %difference = algebra.field_subtract %second,%first : (!F,!F)->!F
   func.return %difference,%first,%second : !F,!F,!F
 }
 func.func private @raw(%a:!F,%b:!F)->(!F,!F,!F) {
   %r:3 = func.call @leaf(%b,%a) : (!F,!F)->(!F,!F,!F)
   %s:3 = func.call @leaf(%a,%b) : (!F,!F)->(!F,!F,!F)
   func.return %r#0,%s#2,%r#1 : !F,!F,!F
 }
 func.func private @expanded(%a:!F,%b:!F)->(!F,!F,!F) {
   %dead0 = algebra.field_multiply %b,%a : (!F,!F)->!F
   %first0 = algebra.field_multiply %b,%a : (!F,!F)->!F
   %second0 = algebra.field_multiply %b,%a : (!F,!F)->!F
   %difference0 = algebra.field_subtract %second0,%first0 : (!F,!F)->!F
   %dead1 = algebra.field_multiply %a,%b : (!F,!F)->!F
   %first1 = algebra.field_multiply %a,%b : (!F,!F)->!F
   %second1 = algebra.field_multiply %a,%b : (!F,!F)->!F
   %difference1 = algebra.field_subtract %second1,%first1 : (!F,!F)->!F
   func.return %difference0,%second1,%first0 : !F,!F,!F
 }
 func.func private @mixed_leaf(%a:!F,%b:!F)->(!F,!P,!F) {
   %dead = algebra.field_multiply %a,%b : (!F,!F)->!F
   %first = algebra.field_multiply %a,%b : (!F,!F)->!F
   %second = algebra.field_multiply %a,%b : (!F,!F)->!F
   %table = "data.array_from_elements"(%first,%second) : (!F,!F)->!A
   %p = "poly.from_coefficients"(%table) : (!A)->!P
   func.return %first,%p,%second : !F,!P,!F
 }
 func.func private @mixed_raw(%a:!F,%b:!F,%x:!F)->(!F,!F,!F) {
   %r:3 = func.call @mixed_leaf(%b,%a) : (!F,!F)->(!F,!P,!F)
   %value = "poly.evaluate"(%r#1,%x) : (!P,!F)->!F
   func.return %r#0,%value,%r#2 : !F,!F,!F
 }
 func.func private @mixed_expanded(%a:!F,%b:!F,%x:!F)->(!F,!F,!F) {
   %dead = algebra.field_multiply %b,%a : (!F,!F)->!F
   %first = algebra.field_multiply %b,%a : (!F,!F)->!F
   %second = algebra.field_multiply %b,%a : (!F,!F)->!F
   %table = "data.array_from_elements"(%first,%second) : (!F,!F)->!A
   %p = "poly.from_coefficients"(%table) : (!A)->!P
   %value = "poly.evaluate"(%p,%x) : (!P,!F)->!F
   func.return %first,%value,%second : !F,!F,!F
 }
 func.func private @polynomial(%a:!F,%b:!F,%x:!F)->(!F,!F) {
   %dead = algebra.field_multiply %a,%b : (!F,!F)->!F
   %table = "data.array_from_elements"(%a,%b) : (!F,!F)->!A
   %p = "poly.from_coefficients"(%table) : (!A)->!P
   %square = "poly.multiply"(%p,%p) : (!P,!P)->!P
   %value = "poly.evaluate"(%square,%x) : (!P,!F)->!F
   %after = algebra.field_subtract %value,%a : (!F,!F)->!F
   func.return %value,%after : !F,!F
 }
 func.func private @normalized(%a:!F,%b:!F,%x:!F)->(!F,!F) {
   %dead = algebra.field_multiply %a,%b : (!F,!F)->!F
   %table = "data.array_from_elements"(%a,%b) : (!F,!F)->!A
   %bx = algebra.field_multiply %b,%x : (!F,!F)->!F
   %p = algebra.field_add %bx,%a : (!F,!F)->!F
   %value = algebra.field_multiply %p,%p : (!F,!F)->!F
   %after = algebra.field_subtract %value,%a : (!F,!F)->!F
   func.return %value,%after : !F,!F
 }
 func.func private @reconstruct(%a:!F,%b:!F,%x:!F)->!F {
   %product = algebra.field_multiply %a,%b : (!F,!F)->!F
   %p = "poly.constant"(%product) : (!F)->!P
   %value = "poly.evaluate"(%p,%x) : (!P,!F)->!F
   func.return %value : !F
 }
 func.func private @reconstructed(%a:!F,%b:!F,%x:!F)->!F {
   %product = algebra.field_multiply %a,%b : (!F,!F)->!F
   func.return %product : !F
 }
 func.func private @projection(%a:!F,%b:!F)->!F {
   %table = "data.array_from_elements"(%a,%b) : (!F,!F)->!A
   %value = "data.array_at"(%table) {index=0:i64} : (!A)->!F
   func.return %value : !F
 }
 func.func private @cache(%table:!A,%a:!F,%b:!F,%x:!F)->(!F,!F,!A) {
   %p = "poly.from_coefficients"(%table) : (!A)->!P
   %first = "poly.evaluate"(%p,%x) : (!P,!F)->!F
   %cut = algebra.field_multiply %a,%b : (!F,!F)->!F
   %second = "poly.evaluate"(%p,%x) : (!P,!F)->!F
   %coeffs = "poly.coefficients"(%p) : (!P)->!A
   func.return %first,%second,%coeffs : !F,!F,!A
 }
 func.func private @tables(%table:!A,%x:!F)->(!A,!A,!F,!A) {
   %p = "poly.interpolate"(%table) {points=[#algebra.literal<!algebra.field<"bls12-381.fr">, 0 : ui255>,#algebra.literal<!algebra.field<"bls12-381.fr">, 1 : ui255>]} : (!A)->!P
   %coeffs = "poly.coefficients"(%p) : (!P)->!A
   %domain = "poly.evaluate_domain"(%p) {points=[#algebra.literal<!algebra.field<"bls12-381.fr">, 2 : ui255>,#algebra.literal<!algebra.field<"bls12-381.fr">, 3 : ui255>]} : (!P)->!A
   %m = "poly.mle"(%table) : (!A)->!P
   %fix = "poly.fix"(%m,%x) : (!P,!F)->!poly.polynomial<"bls12-381.fr",0>
   %value = "poly.evaluate"(%fix) : (!poly.polynomial<"bls12-381.fr",0>)->!F
   %fixed = "poly.fix_table"(%table,%x) : (!A,!F)->!data.field_array<"bls12-381.fr",1>
   %dead = "poly.evaluate"(%p,%x) : (!P,!F)->!F
   %padded = "data.array_from_elements"(%value,%value) : (!F,!F)->!A
   func.return %coeffs,%domain,%value,%padded : !A,!A,!F,!A
 }
 func.func private @coefficients(%table:!data.field_array<"bls12-381.fr",4>,%x:!F)->(!A,!A,!F) {
   %m = "poly.mle"(%table) : (!data.field_array<"bls12-381.fr",4>)->!poly.polynomial<"bls12-381.fr",2>
   %sum = "poly.sum_suffix"(%m) {count=1:i64} : (!poly.polynomial<"bls12-381.fr",2>)->!P
   %coeffs = "poly.coefficients"(%sum) : (!P)->!A
   %fixed = "poly.fix_table"(%table,%x) : (!data.field_array<"bls12-381.fr",4>,!F)->!A
   %value = "poly.evaluate"(%sum,%x) : (!P,!F)->!F
   func.return %coeffs,%fixed,%value : !A,!A,!F
 }
 func.func private @convolution(%a:!F,%b:!F,%x:!F)->!data.field_array<"bls12-381.fr",4> {
   %table = "data.array_from_elements"(%a,%b) : (!F,!F)->!A
   %p = "poly.from_coefficients"(%table) : (!A)->!P
   %c = "poly.constant"(%x) : (!F)->!P
   %sum = "poly.add"(%p,%c) : (!P,!P)->!P
   %product = "poly.multiply"(%sum,%p) : (!P,!P)->!P
   %coeffs = "poly.coefficients"(%product) : (!P)->!data.field_array<"bls12-381.fr",4>
   func.return %coeffs : !data.field_array<"bls12-381.fr",4>
 }
 "protocol.func"() ({ "protocol.return"() : ()->() })
 {sym_name="main",function_type=()->(),roles=["P"],input_roles=[],output_roles=[]} : ()->()
}) {profile=#protocol.profile<protocol>} : ()->() }
