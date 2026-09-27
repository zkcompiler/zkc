// Reused arithmetic from examples/protocols/air-oracle/air-permutation.pir.
module {
  use zkc::algebra::{CharacteristicNotTwo, ExtensionField, Field, Indices, TwoAdicField, Vector};
  use zkc::algebra;
  use zkc::core;
  use zkc::oracle::{Commitments, OpeningStates, VectorCommitment};
  use zkc::oracle;
  use zkc::pcs::{Commitment, OpeningState, Proof};
  use zkc::poly::{Polynomial};
  use zkc::poly;
  use zkc::random::{IndexRandomness, Rng};
  use zkc::random;
  library(namespace="zkc.examples", name="air", version="1", resolution="source-v1");

  pub fn PrepareAlgorithm<F: domain Field>(
    values: Vector<F::Element>
  ) -> (Polynomial<F>, Vector<F::Element>) requires (TwoAdicField(F)) {
    let (value0) = zkc::algebra::vector_length_check::<F>(values) attributes ("8");
    zkc::core::require(value0);
    let (value2) = zkc::algebra::constant::<F>() attributes ("1");
    let (value3) = zkc::poly::coset_interpolate::<F>(values, value2);
    let (value4) = zkc::algebra::constant::<F>() attributes ("3");
    let (value5) = zkc::algebra::index_constant() attributes ("32");
    let (value6) = zkc::poly::coset_evaluate::<F>(value3, value4, value5);
    return (value3, value6);
  }

  pub fn InterleaveAlgorithm<F: domain Field>(
    a: Vector<F::Element>,
    b: Vector<F::Element>
  ) -> (Vector<F::Element>) requires (Field(F)) {
    let (value0) = zkc::algebra::vector_interleave::<F>(a, b);
    return (value0);
  }

  pub fn LiftVectorAlgorithm<F: domain Field>(
    value: Vector<F::BaseField::Element>
  ) -> (Vector<F::Element>) requires (ExtensionField(F)) {
    let (value0) = zkc::algebra::vector_embed::<F>(value);
    return (value0);
  }

  pub fn LiftScalarAlgorithm<F: domain Field>(value: F::BaseField::Element) -> (F::Element) requires (
    ExtensionField(F)
  ) {
    let (value0) = zkc::algebra::embed::<F>(value);
    return (value0);
  }

  pub fn LiftPolynomialAlgorithm<F: domain Field>(value: Polynomial<F::BaseField>) -> (Polynomial<F>) requires (
    ExtensionField(F),
    Field(F::BaseField)
  ) {
    let (value0) = zkc::poly::coefficients::<F::BaseField>(value);
    let (value1) = zkc::algebra::vector_embed::<F>(value0);
    let (value2) = zkc::poly::from_coefficients::<F>(value1);
    return (value2);
  }

  pub fn AuxiliaryAlgorithm<F: domain Field>(
    values: Vector<F::BaseField::Element>,
    beta: F::Element
  ) -> (Polynomial<F>, Vector<F::Element>, F::Element) requires (ExtensionField(F), TwoAdicField(F)) {
    let (value0) = zkc::algebra::vector_embed::<F>(values);
    let (value1) = zkc::algebra::index_constant() attributes ("8");
    let (value2) = zkc::algebra::vector_fill::<F>(beta, value1);
    let (value3) = zkc::algebra::vector_sub::<F>(value2, value0);
    let (value4) = zkc::algebra::vector_prefix_product::<F>(value3);
    let (value5) = zkc::algebra::index_constant() attributes ("7");
    let (value6) = zkc::algebra::vector_get::<F>(value4, value5);
    let (value7) = zkc::algebra::constant::<F>() attributes ("1");
    let (value8) = zkc::poly::coset_interpolate::<F>(value4, value7);
    let (value9) = zkc::algebra::constant::<F>() attributes ("3");
    let (value10) = zkc::algebra::index_constant() attributes ("32");
    let (value11) = zkc::poly::coset_evaluate::<F>(value8, value9, value10);
    return (value8, value11, value6);
  }

  pub fn QuotientsAlgorithm<F: domain Field>(
    left: Vector<F::Element>,
    right: Vector<F::Element>,
    sum_values: Vector<F::Element>,
    left_product: Vector<F::Element>,
    right_product: Vector<F::Element>,
    beta: F::Element,
    alpha: F::Element,
    left_terminal: F::Element,
    right_terminal: F::Element,
    initial: F::Element,
    final_value: F::Element,
    total: F::Element
  ) -> (Polynomial<F>, Polynomial<F>, Vector<F::Element>, Vector<F::Element>, Vector<F::Element>) requires (
    TwoAdicField(F)
  ) {
    let (value0) = zkc::algebra::index_constant() attributes ("32");
    let (value1) = zkc::algebra::constant::<F>() attributes ("3");
    let (value2) = zkc::poly::domain_points::<F>(value1, value0);
    let (value3) = zkc::algebra::index_constant() attributes ("4");
    let (value4) = zkc::algebra::vector_rotate::<F>(left, value3);
    let (value5) = zkc::algebra::index_constant() attributes ("4");
    let (value6) = zkc::algebra::vector_rotate::<F>(right, value5);
    let (value7) = zkc::algebra::index_constant() attributes ("4");
    let (value8) = zkc::algebra::vector_rotate::<F>(sum_values, value7);
    let (value9) = zkc::algebra::index_constant() attributes ("4");
    let (value10) = zkc::algebra::vector_rotate::<F>(left_product, value9);
    let (value11) = zkc::algebra::index_constant() attributes ("4");
    let (value12) = zkc::algebra::vector_rotate::<F>(right_product, value11);
    let (value13) = zkc::algebra::constant::<F>() attributes ("1");
    let (value14) = zkc::algebra::vector_fill::<F>(value13, value0);
    let (value15) = zkc::algebra::constant::<F>() attributes ("1");
    let (value16) = zkc::algebra::index_constant() attributes ("8");
    let (value17) = zkc::algebra::index_constant() attributes ("7");
    let (value18) = zkc::poly::domain_point::<F>(value15, value16, value17);
    let (value19) = zkc::algebra::vector_sub::<F>(value2, value14);
    let (value20) = zkc::algebra::vector_fill::<F>(value18, value0);
    let (value21) = zkc::algebra::vector_sub::<F>(value2, value20);
    let (value22) = zkc::algebra::vector_mul::<F>(value2, value2);
    let (value23) = zkc::algebra::vector_mul::<F>(value22, value22);
    let (value24) = zkc::algebra::vector_mul::<F>(value23, value23);
    let (value25) = zkc::algebra::vector_sub::<F>(value24, value14);
    let (value26) = zkc::algebra::vector_inverse::<F>(value19);
    let (value27) = zkc::algebra::vector_inverse::<F>(value25);
    let (value28) = zkc::algebra::vector_mul::<F>(value21, value27);
    let (value29) = zkc::algebra::vector_inverse::<F>(value21);
    let (value30) = zkc::algebra::constant::<F>() attributes ("0");
    let (value31) = zkc::algebra::vector_fill::<F>(value30, value0);
    let (value32) = zkc::algebra::vector_fill::<F>(initial, value0);
    let (value33) = zkc::algebra::vector_sub::<F>(value31, value32);
    let (value34) = zkc::algebra::vector_add::<F>(left, value33);
    let (value35) = zkc::algebra::constant::<F>() attributes ("0");
    let (value36) = zkc::algebra::vector_fill::<F>(value35, value0);
    let (value37) = zkc::algebra::vector_sub::<F>(value36, left);
    let (value38) = zkc::algebra::vector_add::<F>(value4, value37);
    let (value39) = zkc::algebra::constant::<F>() attributes ("0");
    let (value40) = zkc::algebra::vector_fill::<F>(value39, value0);
    let (value41) = zkc::algebra::constant::<F>() attributes ("1");
    let (value42) = zkc::algebra::vector_fill::<F>(value41, value0);
    let (value43) = zkc::algebra::vector_sub::<F>(value40, value42);
    let (value44) = zkc::algebra::vector_add::<F>(value38, value43);
    let (value45) = zkc::algebra::constant::<F>() attributes ("0");
    let (value46) = zkc::algebra::vector_fill::<F>(value45, value0);
    let (value47) = zkc::algebra::vector_fill::<F>(final_value, value0);
    let (value48) = zkc::algebra::vector_sub::<F>(value46, value47);
    let (value49) = zkc::algebra::vector_add::<F>(left, value48);
    let (value50) = zkc::algebra::constant::<F>() attributes ("0");
    let (value51) = zkc::algebra::vector_fill::<F>(value50, value0);
    let (value52) = zkc::algebra::vector_fill::<F>(beta, value0);
    let (value53) = zkc::algebra::constant::<F>() attributes ("0");
    let (value54) = zkc::algebra::vector_fill::<F>(value53, value0);
    let (value55) = zkc::algebra::vector_sub::<F>(value54, left);
    let (value56) = zkc::algebra::vector_add::<F>(value52, value55);
    let (value57) = zkc::algebra::vector_sub::<F>(value51, value56);
    let (value58) = zkc::algebra::vector_add::<F>(left_product, value57);
    let (value59) = zkc::algebra::constant::<F>() attributes ("0");
    let (value60) = zkc::algebra::vector_fill::<F>(value59, value0);
    let (value61) = zkc::algebra::vector_fill::<F>(beta, value0);
    let (value62) = zkc::algebra::constant::<F>() attributes ("0");
    let (value63) = zkc::algebra::vector_fill::<F>(value62, value0);
    let (value64) = zkc::algebra::vector_sub::<F>(value63, value4);
    let (value65) = zkc::algebra::vector_add::<F>(value61, value64);
    let (value66) = zkc::algebra::vector_mul::<F>(left_product, value65);
    let (value67) = zkc::algebra::vector_sub::<F>(value60, value66);
    let (value68) = zkc::algebra::vector_add::<F>(value10, value67);
    let (value69) = zkc::algebra::constant::<F>() attributes ("0");
    let (value70) = zkc::algebra::vector_fill::<F>(value69, value0);
    let (value71) = zkc::algebra::vector_fill::<F>(left_terminal, value0);
    let (value72) = zkc::algebra::vector_sub::<F>(value70, value71);
    let (value73) = zkc::algebra::vector_add::<F>(left_product, value72);
    let (value74) = zkc::algebra::constant::<F>() attributes ("0");
    let (value75) = zkc::algebra::vector_fill::<F>(value74, value0);
    let (value76) = zkc::algebra::vector_sub::<F>(value75, right);
    let (value77) = zkc::algebra::vector_add::<F>(sum_values, value76);
    let (value78) = zkc::algebra::constant::<F>() attributes ("0");
    let (value79) = zkc::algebra::vector_fill::<F>(value78, value0);
    let (value80) = zkc::algebra::vector_sub::<F>(value79, sum_values);
    let (value81) = zkc::algebra::vector_add::<F>(value8, value80);
    let (value82) = zkc::algebra::constant::<F>() attributes ("0");
    let (value83) = zkc::algebra::vector_fill::<F>(value82, value0);
    let (value84) = zkc::algebra::vector_sub::<F>(value83, value6);
    let (value85) = zkc::algebra::vector_add::<F>(value81, value84);
    let (value86) = zkc::algebra::constant::<F>() attributes ("0");
    let (value87) = zkc::algebra::vector_fill::<F>(value86, value0);
    let (value88) = zkc::algebra::vector_fill::<F>(total, value0);
    let (value89) = zkc::algebra::vector_sub::<F>(value87, value88);
    let (value90) = zkc::algebra::vector_add::<F>(sum_values, value89);
    let (value91) = zkc::algebra::constant::<F>() attributes ("0");
    let (value92) = zkc::algebra::vector_fill::<F>(value91, value0);
    let (value93) = zkc::algebra::vector_fill::<F>(beta, value0);
    let (value94) = zkc::algebra::constant::<F>() attributes ("0");
    let (value95) = zkc::algebra::vector_fill::<F>(value94, value0);
    let (value96) = zkc::algebra::vector_sub::<F>(value95, right);
    let (value97) = zkc::algebra::vector_add::<F>(value93, value96);
    let (value98) = zkc::algebra::vector_sub::<F>(value92, value97);
    let (value99) = zkc::algebra::vector_add::<F>(right_product, value98);
    let (value100) = zkc::algebra::constant::<F>() attributes ("0");
    let (value101) = zkc::algebra::vector_fill::<F>(value100, value0);
    let (value102) = zkc::algebra::vector_fill::<F>(beta, value0);
    let (value103) = zkc::algebra::constant::<F>() attributes ("0");
    let (value104) = zkc::algebra::vector_fill::<F>(value103, value0);
    let (value105) = zkc::algebra::vector_sub::<F>(value104, value6);
    let (value106) = zkc::algebra::vector_add::<F>(value102, value105);
    let (value107) = zkc::algebra::vector_mul::<F>(right_product, value106);
    let (value108) = zkc::algebra::vector_sub::<F>(value101, value107);
    let (value109) = zkc::algebra::vector_add::<F>(value12, value108);
    let (value110) = zkc::algebra::constant::<F>() attributes ("0");
    let (value111) = zkc::algebra::vector_fill::<F>(value110, value0);
    let (value112) = zkc::algebra::vector_fill::<F>(right_terminal, value0);
    let (value113) = zkc::algebra::vector_sub::<F>(value111, value112);
    let (value114) = zkc::algebra::vector_add::<F>(right_product, value113);
    let (value115) = zkc::algebra::constant::<F>() attributes ("0");
    let (value116) = zkc::algebra::vector_fill::<F>(value115, value0);
    let (value117) = zkc::algebra::vector_scale::<F>(value116, alpha);
    let (value118) = zkc::algebra::vector_mul::<F>(value73, value29);
    let (value119) = zkc::algebra::vector_add::<F>(value117, value118);
    let (value120) = zkc::algebra::vector_scale::<F>(value119, alpha);
    let (value121) = zkc::algebra::vector_mul::<F>(value68, value28);
    let (value122) = zkc::algebra::vector_add::<F>(value120, value121);
    let (value123) = zkc::algebra::vector_scale::<F>(value122, alpha);
    let (value124) = zkc::algebra::vector_mul::<F>(value58, value26);
    let (value125) = zkc::algebra::vector_add::<F>(value123, value124);
    let (value126) = zkc::algebra::vector_scale::<F>(value125, alpha);
    let (value127) = zkc::algebra::vector_mul::<F>(value49, value29);
    let (value128) = zkc::algebra::vector_add::<F>(value126, value127);
    let (value129) = zkc::algebra::vector_scale::<F>(value128, alpha);
    let (value130) = zkc::algebra::vector_mul::<F>(value44, value28);
    let (value131) = zkc::algebra::vector_add::<F>(value129, value130);
    let (value132) = zkc::algebra::vector_scale::<F>(value131, alpha);
    let (value133) = zkc::algebra::vector_mul::<F>(value34, value26);
    let (value134) = zkc::algebra::vector_add::<F>(value132, value133);
    let (value135) = zkc::algebra::constant::<F>() attributes ("0");
    let (value136) = zkc::algebra::vector_fill::<F>(value135, value0);
    let (value137) = zkc::algebra::vector_scale::<F>(value136, alpha);
    let (value138) = zkc::algebra::vector_mul::<F>(value114, value29);
    let (value139) = zkc::algebra::vector_add::<F>(value137, value138);
    let (value140) = zkc::algebra::vector_scale::<F>(value139, alpha);
    let (value141) = zkc::algebra::vector_mul::<F>(value109, value28);
    let (value142) = zkc::algebra::vector_add::<F>(value140, value141);
    let (value143) = zkc::algebra::vector_scale::<F>(value142, alpha);
    let (value144) = zkc::algebra::vector_mul::<F>(value99, value26);
    let (value145) = zkc::algebra::vector_add::<F>(value143, value144);
    let (value146) = zkc::algebra::vector_scale::<F>(value145, alpha);
    let (value147) = zkc::algebra::vector_mul::<F>(value90, value29);
    let (value148) = zkc::algebra::vector_add::<F>(value146, value147);
    let (value149) = zkc::algebra::vector_scale::<F>(value148, alpha);
    let (value150) = zkc::algebra::vector_mul::<F>(value85, value28);
    let (value151) = zkc::algebra::vector_add::<F>(value149, value150);
    let (value152) = zkc::algebra::vector_scale::<F>(value151, alpha);
    let (value153) = zkc::algebra::vector_mul::<F>(value77, value26);
    let (value154) = zkc::algebra::vector_add::<F>(value152, value153);
    let (value155) = zkc::poly::coset_interpolate::<F>(value134, value1);
    let (value156) = zkc::poly::coset_interpolate::<F>(value154, value1);
    let (value157) = zkc::poly::degree_check::<F>(value155) attributes ("7");
    zkc::core::require(value157);
    let (value159) = zkc::poly::degree_check::<F>(value156) attributes ("7");
    zkc::core::require(value159);
    let (value161) = zkc::algebra::vector_interleave::<F>(value134, value154);
    return (value155, value156, value134, value154, value161);
  }

  pub fn EqualAlgorithm<F: domain Field>(a: F::Element, b: F::Element) -> (bool) requires (Field(F)) {
    let (value0) = zkc::algebra::equal::<F>(a, b);
    zkc::core::require(value0);
    return (value0);
  }

  pub fn EvaluateAlgorithm<F: domain Field>(p: Polynomial<F>, z: F::Element) -> (F::Element, F::Element) requires (
    TwoAdicField(F)
  ) {
    let (value0) = zkc::algebra::index_constant() attributes ("8");
    let (value1) = zkc::poly::domain_root::<F>(value0);
    let (value2) = zkc::algebra::mul::<F>(z, value1);
    let (value3) = zkc::poly::evaluate::<F>(p, z);
    let (value4) = zkc::poly::evaluate::<F>(p, value2);
    return (value3, value4);
  }

  pub fn CheckOutOfDomainAlgorithm<F: domain Field>(
    at_z_0: F::Element,
    at_z_1: F::Element,
    at_z_2: F::Element,
    at_z_3: F::Element,
    at_z_4: F::Element,
    at_next_0: F::Element,
    at_next_1: F::Element,
    at_next_2: F::Element,
    at_next_3: F::Element,
    at_next_4: F::Element,
    quotient_left: F::Element,
    quotient_right: F::Element,
    beta: F::Element,
    alpha: F::Element,
    left_terminal: F::Element,
    right_terminal: F::Element,
    initial: F::Element,
    final_value: F::Element,
    total: F::Element,
    z: F::Element
  ) -> (bool) requires (TwoAdicField(F)) {
    let (value0) = zkc::algebra::inverse::<F>(z);
    let (value1) = zkc::algebra::mul::<F>(z, z);
    let (value2) = zkc::algebra::mul::<F>(value1, value1);
    let (value3) = zkc::algebra::mul::<F>(value2, value2);
    let (value4) = zkc::algebra::constant::<F>() attributes ("1");
    let (value5) = zkc::algebra::sub::<F>(value3, value4);
    let (value6) = zkc::algebra::inverse::<F>(value5);
    let (value7) = zkc::algebra::mul::<F>(z, z);
    let (value8) = zkc::algebra::mul::<F>(value7, value7);
    let (value9) = zkc::algebra::mul::<F>(value8, value8);
    let (value10) = zkc::algebra::mul::<F>(value9, value9);
    let (value11) = zkc::algebra::mul::<F>(value10, value10);
    let (value12) = zkc::algebra::constant::<F>() attributes ("3");
    let (value13) = zkc::algebra::mul::<F>(value12, value12);
    let (value14) = zkc::algebra::mul::<F>(value13, value13);
    let (value15) = zkc::algebra::mul::<F>(value14, value14);
    let (value16) = zkc::algebra::mul::<F>(value15, value15);
    let (value17) = zkc::algebra::mul::<F>(value16, value16);
    let (value18) = zkc::algebra::sub::<F>(value11, value17);
    let (value19) = zkc::algebra::inverse::<F>(value18);
    let (value20) = zkc::algebra::constant::<F>() attributes ("1");
    let (value21) = zkc::algebra::constant::<F>() attributes ("1");
    let (value22) = zkc::algebra::index_constant() attributes ("8");
    let (value23) = zkc::algebra::index_constant() attributes ("7");
    let (value24) = zkc::poly::domain_point::<F>(value21, value22, value23);
    let (value25) = zkc::algebra::sub::<F>(z, value20);
    let (value26) = zkc::algebra::sub::<F>(z, value24);
    let (value27) = zkc::algebra::mul::<F>(z, z);
    let (value28) = zkc::algebra::mul::<F>(value27, value27);
    let (value29) = zkc::algebra::mul::<F>(value28, value28);
    let (value30) = zkc::algebra::sub::<F>(value29, value20);
    let (value31) = zkc::algebra::inverse::<F>(value25);
    let (value32) = zkc::algebra::inverse::<F>(value30);
    let (value33) = zkc::algebra::mul::<F>(value26, value32);
    let (value34) = zkc::algebra::inverse::<F>(value26);
    let (value35) = zkc::algebra::constant::<F>() attributes ("0");
    let (value36) = zkc::algebra::sub::<F>(value35, initial);
    let (value37) = zkc::algebra::add::<F>(at_z_0, value36);
    let (value38) = zkc::algebra::constant::<F>() attributes ("0");
    let (value39) = zkc::algebra::sub::<F>(value38, at_z_0);
    let (value40) = zkc::algebra::add::<F>(at_next_0, value39);
    let (value41) = zkc::algebra::constant::<F>() attributes ("0");
    let (value42) = zkc::algebra::constant::<F>() attributes ("1");
    let (value43) = zkc::algebra::sub::<F>(value41, value42);
    let (value44) = zkc::algebra::add::<F>(value40, value43);
    let (value45) = zkc::algebra::constant::<F>() attributes ("0");
    let (value46) = zkc::algebra::sub::<F>(value45, final_value);
    let (value47) = zkc::algebra::add::<F>(at_z_0, value46);
    let (value48) = zkc::algebra::constant::<F>() attributes ("0");
    let (value49) = zkc::algebra::constant::<F>() attributes ("0");
    let (value50) = zkc::algebra::sub::<F>(value49, at_z_0);
    let (value51) = zkc::algebra::add::<F>(beta, value50);
    let (value52) = zkc::algebra::sub::<F>(value48, value51);
    let (value53) = zkc::algebra::add::<F>(at_z_3, value52);
    let (value54) = zkc::algebra::constant::<F>() attributes ("0");
    let (value55) = zkc::algebra::constant::<F>() attributes ("0");
    let (value56) = zkc::algebra::sub::<F>(value55, at_next_0);
    let (value57) = zkc::algebra::add::<F>(beta, value56);
    let (value58) = zkc::algebra::mul::<F>(at_z_3, value57);
    let (value59) = zkc::algebra::sub::<F>(value54, value58);
    let (value60) = zkc::algebra::add::<F>(at_next_3, value59);
    let (value61) = zkc::algebra::constant::<F>() attributes ("0");
    let (value62) = zkc::algebra::sub::<F>(value61, left_terminal);
    let (value63) = zkc::algebra::add::<F>(at_z_3, value62);
    let (value64) = zkc::algebra::constant::<F>() attributes ("0");
    let (value65) = zkc::algebra::sub::<F>(value64, at_z_1);
    let (value66) = zkc::algebra::add::<F>(at_z_2, value65);
    let (value67) = zkc::algebra::constant::<F>() attributes ("0");
    let (value68) = zkc::algebra::sub::<F>(value67, at_z_2);
    let (value69) = zkc::algebra::add::<F>(at_next_2, value68);
    let (value70) = zkc::algebra::constant::<F>() attributes ("0");
    let (value71) = zkc::algebra::sub::<F>(value70, at_next_1);
    let (value72) = zkc::algebra::add::<F>(value69, value71);
    let (value73) = zkc::algebra::constant::<F>() attributes ("0");
    let (value74) = zkc::algebra::sub::<F>(value73, total);
    let (value75) = zkc::algebra::add::<F>(at_z_2, value74);
    let (value76) = zkc::algebra::constant::<F>() attributes ("0");
    let (value77) = zkc::algebra::constant::<F>() attributes ("0");
    let (value78) = zkc::algebra::sub::<F>(value77, at_z_1);
    let (value79) = zkc::algebra::add::<F>(beta, value78);
    let (value80) = zkc::algebra::sub::<F>(value76, value79);
    let (value81) = zkc::algebra::add::<F>(at_z_4, value80);
    let (value82) = zkc::algebra::constant::<F>() attributes ("0");
    let (value83) = zkc::algebra::constant::<F>() attributes ("0");
    let (value84) = zkc::algebra::sub::<F>(value83, at_next_1);
    let (value85) = zkc::algebra::add::<F>(beta, value84);
    let (value86) = zkc::algebra::mul::<F>(at_z_4, value85);
    let (value87) = zkc::algebra::sub::<F>(value82, value86);
    let (value88) = zkc::algebra::add::<F>(at_next_4, value87);
    let (value89) = zkc::algebra::constant::<F>() attributes ("0");
    let (value90) = zkc::algebra::sub::<F>(value89, right_terminal);
    let (value91) = zkc::algebra::add::<F>(at_z_4, value90);
    let (value92) = zkc::algebra::constant::<F>() attributes ("0");
    let (value93) = zkc::algebra::mul::<F>(value92, alpha);
    let (value94) = zkc::algebra::mul::<F>(value63, value34);
    let (value95) = zkc::algebra::add::<F>(value93, value94);
    let (value96) = zkc::algebra::mul::<F>(value95, alpha);
    let (value97) = zkc::algebra::mul::<F>(value60, value33);
    let (value98) = zkc::algebra::add::<F>(value96, value97);
    let (value99) = zkc::algebra::mul::<F>(value98, alpha);
    let (value100) = zkc::algebra::mul::<F>(value53, value31);
    let (value101) = zkc::algebra::add::<F>(value99, value100);
    let (value102) = zkc::algebra::mul::<F>(value101, alpha);
    let (value103) = zkc::algebra::mul::<F>(value47, value34);
    let (value104) = zkc::algebra::add::<F>(value102, value103);
    let (value105) = zkc::algebra::mul::<F>(value104, alpha);
    let (value106) = zkc::algebra::mul::<F>(value44, value33);
    let (value107) = zkc::algebra::add::<F>(value105, value106);
    let (value108) = zkc::algebra::mul::<F>(value107, alpha);
    let (value109) = zkc::algebra::mul::<F>(value37, value31);
    let (value110) = zkc::algebra::add::<F>(value108, value109);
    let (value111) = zkc::algebra::constant::<F>() attributes ("0");
    let (value112) = zkc::algebra::mul::<F>(value111, alpha);
    let (value113) = zkc::algebra::mul::<F>(value91, value34);
    let (value114) = zkc::algebra::add::<F>(value112, value113);
    let (value115) = zkc::algebra::mul::<F>(value114, alpha);
    let (value116) = zkc::algebra::mul::<F>(value88, value33);
    let (value117) = zkc::algebra::add::<F>(value115, value116);
    let (value118) = zkc::algebra::mul::<F>(value117, alpha);
    let (value119) = zkc::algebra::mul::<F>(value81, value31);
    let (value120) = zkc::algebra::add::<F>(value118, value119);
    let (value121) = zkc::algebra::mul::<F>(value120, alpha);
    let (value122) = zkc::algebra::mul::<F>(value75, value34);
    let (value123) = zkc::algebra::add::<F>(value121, value122);
    let (value124) = zkc::algebra::mul::<F>(value123, alpha);
    let (value125) = zkc::algebra::mul::<F>(value72, value33);
    let (value126) = zkc::algebra::add::<F>(value124, value125);
    let (value127) = zkc::algebra::mul::<F>(value126, alpha);
    let (value128) = zkc::algebra::mul::<F>(value66, value31);
    let (value129) = zkc::algebra::add::<F>(value127, value128);
    let (value130) = zkc::algebra::equal::<F>(value110, quotient_left);
    zkc::core::require(value130);
    let (value132) = zkc::algebra::equal::<F>(value129, quotient_right);
    zkc::core::require(value132);
    return (value132);
  }

  pub fn DeepAlgorithm<F: domain Field>(
    left: Vector<F::Element>,
    right: Vector<F::Element>,
    sum_values: Vector<F::Element>,
    left_product: Vector<F::Element>,
    right_product: Vector<F::Element>,
    qleft: Vector<F::Element>,
    qright: Vector<F::Element>,
    at_z_0: F::Element,
    at_z_1: F::Element,
    at_z_2: F::Element,
    at_z_3: F::Element,
    at_z_4: F::Element,
    at_next_0: F::Element,
    at_next_1: F::Element,
    at_next_2: F::Element,
    at_next_3: F::Element,
    at_next_4: F::Element,
    quotient_left: F::Element,
    quotient_right: F::Element,
    z: F::Element,
    eta: F::Element,
    degree_mix: F::Element
  ) -> (Vector<F::Element>) requires (TwoAdicField(F)) {
    let (value0) = zkc::algebra::index_constant() attributes ("32");
    let (value1) = zkc::algebra::constant::<F>() attributes ("3");
    let (value2) = zkc::poly::domain_points::<F>(value1, value0);
    let (value3) = zkc::algebra::index_constant() attributes ("8");
    let (value4) = zkc::poly::domain_root::<F>(value3);
    let (value5) = zkc::algebra::mul::<F>(z, value4);
    let (value6) = zkc::algebra::vector_fill::<F>(z, value0);
    let (value7) = zkc::algebra::vector_sub::<F>(value2, value6);
    let (value8) = zkc::algebra::vector_inverse::<F>(value7);
    let (value9) = zkc::algebra::vector_fill::<F>(value5, value0);
    let (value10) = zkc::algebra::vector_sub::<F>(value2, value9);
    let (value11) = zkc::algebra::vector_inverse::<F>(value10);
    let (value12) = zkc::algebra::constant::<F>() attributes ("0");
    let (value13) = zkc::algebra::vector_fill::<F>(value12, value0);
    let (value14) = zkc::algebra::constant::<F>() attributes ("1");
    let (value15) = zkc::algebra::vector_fill::<F>(at_z_0, value0);
    let (value16) = zkc::algebra::vector_sub::<F>(left, value15);
    let (value17) = zkc::algebra::vector_mul::<F>(value16, value8);
    let (value18) = zkc::algebra::vector_scale::<F>(value17, value14);
    let (value19) = zkc::algebra::vector_add::<F>(value13, value18);
    let (value20) = zkc::algebra::mul::<F>(value14, eta);
    let (value21) = zkc::algebra::vector_fill::<F>(at_next_0, value0);
    let (value22) = zkc::algebra::vector_sub::<F>(left, value21);
    let (value23) = zkc::algebra::vector_mul::<F>(value22, value11);
    let (value24) = zkc::algebra::vector_scale::<F>(value23, value20);
    let (value25) = zkc::algebra::vector_add::<F>(value19, value24);
    let (value26) = zkc::algebra::mul::<F>(value20, eta);
    let (value27) = zkc::algebra::vector_fill::<F>(at_z_1, value0);
    let (value28) = zkc::algebra::vector_sub::<F>(right, value27);
    let (value29) = zkc::algebra::vector_mul::<F>(value28, value8);
    let (value30) = zkc::algebra::vector_scale::<F>(value29, value26);
    let (value31) = zkc::algebra::vector_add::<F>(value25, value30);
    let (value32) = zkc::algebra::mul::<F>(value26, eta);
    let (value33) = zkc::algebra::vector_fill::<F>(at_next_1, value0);
    let (value34) = zkc::algebra::vector_sub::<F>(right, value33);
    let (value35) = zkc::algebra::vector_mul::<F>(value34, value11);
    let (value36) = zkc::algebra::vector_scale::<F>(value35, value32);
    let (value37) = zkc::algebra::vector_add::<F>(value31, value36);
    let (value38) = zkc::algebra::mul::<F>(value32, eta);
    let (value39) = zkc::algebra::vector_fill::<F>(at_z_2, value0);
    let (value40) = zkc::algebra::vector_sub::<F>(sum_values, value39);
    let (value41) = zkc::algebra::vector_mul::<F>(value40, value8);
    let (value42) = zkc::algebra::vector_scale::<F>(value41, value38);
    let (value43) = zkc::algebra::vector_add::<F>(value37, value42);
    let (value44) = zkc::algebra::mul::<F>(value38, eta);
    let (value45) = zkc::algebra::vector_fill::<F>(at_next_2, value0);
    let (value46) = zkc::algebra::vector_sub::<F>(sum_values, value45);
    let (value47) = zkc::algebra::vector_mul::<F>(value46, value11);
    let (value48) = zkc::algebra::vector_scale::<F>(value47, value44);
    let (value49) = zkc::algebra::vector_add::<F>(value43, value48);
    let (value50) = zkc::algebra::mul::<F>(value44, eta);
    let (value51) = zkc::algebra::vector_fill::<F>(at_z_3, value0);
    let (value52) = zkc::algebra::vector_sub::<F>(left_product, value51);
    let (value53) = zkc::algebra::vector_mul::<F>(value52, value8);
    let (value54) = zkc::algebra::vector_scale::<F>(value53, value50);
    let (value55) = zkc::algebra::vector_add::<F>(value49, value54);
    let (value56) = zkc::algebra::mul::<F>(value50, eta);
    let (value57) = zkc::algebra::vector_fill::<F>(at_next_3, value0);
    let (value58) = zkc::algebra::vector_sub::<F>(left_product, value57);
    let (value59) = zkc::algebra::vector_mul::<F>(value58, value11);
    let (value60) = zkc::algebra::vector_scale::<F>(value59, value56);
    let (value61) = zkc::algebra::vector_add::<F>(value55, value60);
    let (value62) = zkc::algebra::mul::<F>(value56, eta);
    let (value63) = zkc::algebra::vector_fill::<F>(at_z_4, value0);
    let (value64) = zkc::algebra::vector_sub::<F>(right_product, value63);
    let (value65) = zkc::algebra::vector_mul::<F>(value64, value8);
    let (value66) = zkc::algebra::vector_scale::<F>(value65, value62);
    let (value67) = zkc::algebra::vector_add::<F>(value61, value66);
    let (value68) = zkc::algebra::mul::<F>(value62, eta);
    let (value69) = zkc::algebra::vector_fill::<F>(at_next_4, value0);
    let (value70) = zkc::algebra::vector_sub::<F>(right_product, value69);
    let (value71) = zkc::algebra::vector_mul::<F>(value70, value11);
    let (value72) = zkc::algebra::vector_scale::<F>(value71, value68);
    let (value73) = zkc::algebra::vector_add::<F>(value67, value72);
    let (value74) = zkc::algebra::mul::<F>(value68, eta);
    let (value75) = zkc::algebra::vector_fill::<F>(quotient_left, value0);
    let (value76) = zkc::algebra::vector_sub::<F>(qleft, value75);
    let (value77) = zkc::algebra::vector_mul::<F>(value76, value8);
    let (value78) = zkc::algebra::vector_scale::<F>(value77, value74);
    let (value79) = zkc::algebra::vector_add::<F>(value73, value78);
    let (value80) = zkc::algebra::mul::<F>(value74, eta);
    let (value81) = zkc::algebra::vector_fill::<F>(quotient_right, value0);
    let (value82) = zkc::algebra::vector_sub::<F>(qright, value81);
    let (value83) = zkc::algebra::vector_mul::<F>(value82, value8);
    let (value84) = zkc::algebra::vector_scale::<F>(value83, value80);
    let (value85) = zkc::algebra::vector_add::<F>(value79, value84);
    let (value86) = zkc::algebra::mul::<F>(value80, eta);
    let (value87) = zkc::algebra::constant::<F>() attributes ("1");
    let (value88) = zkc::algebra::vector_fill::<F>(value87, value0);
    let (value89) = zkc::algebra::vector_scale::<F>(value2, degree_mix);
    let (value90) = zkc::algebra::vector_add::<F>(value88, value89);
    let (value91) = zkc::algebra::vector_mul::<F>(value90, value85);
    return (value91);
  }

  pub fn DeepRowAlgorithm<F: domain Field>(
    main_left: Vector<F::Element>,
    main_right: Vector<F::Element>,
    aux_left: Vector<F::Element>,
    aux_right: Vector<F::Element>,
    quotient: Vector<F::Element>,
    at_z_0: F::Element,
    at_z_1: F::Element,
    at_z_2: F::Element,
    at_z_3: F::Element,
    at_z_4: F::Element,
    at_next_0: F::Element,
    at_next_1: F::Element,
    at_next_2: F::Element,
    at_next_3: F::Element,
    at_next_4: F::Element,
    quotient_left: F::Element,
    quotient_right: F::Element,
    z: F::Element,
    eta: F::Element,
    degree_mix: F::Element,
    index: index
  ) -> (F::Element) requires (TwoAdicField(F)) {
    let (value0) = zkc::algebra::index_constant() attributes ("0");
    let (value1) = zkc::algebra::vector_get::<F>(main_left, value0);
    let (value2) = zkc::algebra::index_constant() attributes ("0");
    let (value3) = zkc::algebra::vector_get::<F>(main_right, value2);
    let (value4) = zkc::algebra::index_constant() attributes ("1");
    let (value5) = zkc::algebra::vector_get::<F>(main_right, value4);
    let (value6) = zkc::algebra::index_constant() attributes ("0");
    let (value7) = zkc::algebra::vector_get::<F>(aux_left, value6);
    let (value8) = zkc::algebra::index_constant() attributes ("0");
    let (value9) = zkc::algebra::vector_get::<F>(aux_right, value8);
    let (value10) = zkc::algebra::index_constant() attributes ("0");
    let (value11) = zkc::algebra::vector_get::<F>(quotient, value10);
    let (value12) = zkc::algebra::index_constant() attributes ("1");
    let (value13) = zkc::algebra::vector_get::<F>(quotient, value12);
    let (value14) = zkc::algebra::constant::<F>() attributes ("3");
    let (value15) = zkc::algebra::index_constant() attributes ("32");
    let (value16) = zkc::poly::domain_point::<F>(value14, value15, index);
    let (value17) = zkc::algebra::index_constant() attributes ("8");
    let (value18) = zkc::poly::domain_root::<F>(value17);
    let (value19) = zkc::algebra::mul::<F>(z, value18);
    let (value20) = zkc::algebra::sub::<F>(value16, z);
    let (value21) = zkc::algebra::inverse::<F>(value20);
    let (value22) = zkc::algebra::sub::<F>(value16, value19);
    let (value23) = zkc::algebra::inverse::<F>(value22);
    let (value24) = zkc::algebra::constant::<F>() attributes ("0");
    let (value25) = zkc::algebra::constant::<F>() attributes ("1");
    let (value26) = zkc::algebra::sub::<F>(value1, at_z_0);
    let (value27) = zkc::algebra::mul::<F>(value26, value21);
    let (value28) = zkc::algebra::mul::<F>(value27, value25);
    let (value29) = zkc::algebra::add::<F>(value24, value28);
    let (value30) = zkc::algebra::mul::<F>(value25, eta);
    let (value31) = zkc::algebra::sub::<F>(value1, at_next_0);
    let (value32) = zkc::algebra::mul::<F>(value31, value23);
    let (value33) = zkc::algebra::mul::<F>(value32, value30);
    let (value34) = zkc::algebra::add::<F>(value29, value33);
    let (value35) = zkc::algebra::mul::<F>(value30, eta);
    let (value36) = zkc::algebra::sub::<F>(value3, at_z_1);
    let (value37) = zkc::algebra::mul::<F>(value36, value21);
    let (value38) = zkc::algebra::mul::<F>(value37, value35);
    let (value39) = zkc::algebra::add::<F>(value34, value38);
    let (value40) = zkc::algebra::mul::<F>(value35, eta);
    let (value41) = zkc::algebra::sub::<F>(value3, at_next_1);
    let (value42) = zkc::algebra::mul::<F>(value41, value23);
    let (value43) = zkc::algebra::mul::<F>(value42, value40);
    let (value44) = zkc::algebra::add::<F>(value39, value43);
    let (value45) = zkc::algebra::mul::<F>(value40, eta);
    let (value46) = zkc::algebra::sub::<F>(value5, at_z_2);
    let (value47) = zkc::algebra::mul::<F>(value46, value21);
    let (value48) = zkc::algebra::mul::<F>(value47, value45);
    let (value49) = zkc::algebra::add::<F>(value44, value48);
    let (value50) = zkc::algebra::mul::<F>(value45, eta);
    let (value51) = zkc::algebra::sub::<F>(value5, at_next_2);
    let (value52) = zkc::algebra::mul::<F>(value51, value23);
    let (value53) = zkc::algebra::mul::<F>(value52, value50);
    let (value54) = zkc::algebra::add::<F>(value49, value53);
    let (value55) = zkc::algebra::mul::<F>(value50, eta);
    let (value56) = zkc::algebra::sub::<F>(value7, at_z_3);
    let (value57) = zkc::algebra::mul::<F>(value56, value21);
    let (value58) = zkc::algebra::mul::<F>(value57, value55);
    let (value59) = zkc::algebra::add::<F>(value54, value58);
    let (value60) = zkc::algebra::mul::<F>(value55, eta);
    let (value61) = zkc::algebra::sub::<F>(value7, at_next_3);
    let (value62) = zkc::algebra::mul::<F>(value61, value23);
    let (value63) = zkc::algebra::mul::<F>(value62, value60);
    let (value64) = zkc::algebra::add::<F>(value59, value63);
    let (value65) = zkc::algebra::mul::<F>(value60, eta);
    let (value66) = zkc::algebra::sub::<F>(value9, at_z_4);
    let (value67) = zkc::algebra::mul::<F>(value66, value21);
    let (value68) = zkc::algebra::mul::<F>(value67, value65);
    let (value69) = zkc::algebra::add::<F>(value64, value68);
    let (value70) = zkc::algebra::mul::<F>(value65, eta);
    let (value71) = zkc::algebra::sub::<F>(value9, at_next_4);
    let (value72) = zkc::algebra::mul::<F>(value71, value23);
    let (value73) = zkc::algebra::mul::<F>(value72, value70);
    let (value74) = zkc::algebra::add::<F>(value69, value73);
    let (value75) = zkc::algebra::mul::<F>(value70, eta);
    let (value76) = zkc::algebra::sub::<F>(value11, quotient_left);
    let (value77) = zkc::algebra::mul::<F>(value76, value21);
    let (value78) = zkc::algebra::mul::<F>(value77, value75);
    let (value79) = zkc::algebra::add::<F>(value74, value78);
    let (value80) = zkc::algebra::mul::<F>(value75, eta);
    let (value81) = zkc::algebra::sub::<F>(value13, quotient_right);
    let (value82) = zkc::algebra::mul::<F>(value81, value21);
    let (value83) = zkc::algebra::mul::<F>(value82, value80);
    let (value84) = zkc::algebra::add::<F>(value79, value83);
    let (value85) = zkc::algebra::mul::<F>(value80, eta);
    let (value86) = zkc::algebra::constant::<F>() attributes ("1");
    let (value87) = zkc::algebra::mul::<F>(value16, degree_mix);
    let (value88) = zkc::algebra::add::<F>(value86, value87);
    let (value89) = zkc::algebra::mul::<F>(value88, value84);
    return (value89);
  }

  pub fn FoldAlgorithm<F: domain Field>(
    values: Vector<F::Element>,
    shift: F::Element,
    challenge: F::Element
  ) -> (Vector<F::Element>, F::Element) requires (TwoAdicField(F), CharacteristicNotTwo(F)) {
    let (value0) = zkc::poly::even_odd_fold::<F>(values, shift, challenge);
    let (value1) = zkc::algebra::mul::<F>(shift, shift);
    return (value0, value1);
  }

  pub fn TerminalAlgorithm<F: domain Field>(values: Vector<F::Element>) -> (F::Element) requires (
    TwoAdicField(F)
  ) {
    let (value0) = zkc::algebra::index_constant() attributes ("0");
    let (value1) = zkc::algebra::vector_get::<F>(values, value0);
    let (value2) = zkc::algebra::constant::<F>() attributes ("1");
    let (value3) = zkc::poly::coset_interpolate::<F>(values, value2);
    let (value4) = zkc::poly::degree_check::<F>(value3) attributes ("0");
    zkc::core::require(value4);
    return (value1);
  }

  pub fn FoldPairAlgorithm<F: domain Field>(
    a: Vector<F::Element>,
    b: Vector<F::Element>,
    challenge: F::Element,
    shift: F::Element,
    size: index,
    index: index,
    previous: index
  ) -> (F::Element, F::Element, index) requires (TwoAdicField(F)) {
    let (value0) = zkc::algebra::index_constant() attributes ("2");
    let (value1) = zkc::algebra::index_div(size, value0);
    let (value2) = zkc::algebra::index_div(previous, value1);
    let (value3) = zkc::algebra::vector_concat::<F>(a, b);
    let (value4) = zkc::algebra::vector_get::<F>(value3, value2);
    let (value5) = zkc::algebra::index_constant() attributes ("0");
    let (value6) = zkc::algebra::vector_get::<F>(a, value5);
    let (value7) = zkc::algebra::index_constant() attributes ("0");
    let (value8) = zkc::algebra::vector_get::<F>(b, value7);
    let (value9) = zkc::poly::domain_point::<F>(shift, size, index);
    let (value10) = zkc::algebra::constant::<F>() attributes ("2");
    let (value11) = zkc::algebra::inverse::<F>(value10);
    let (value12) = zkc::algebra::add::<F>(value6, value8);
    let (value13) = zkc::algebra::mul::<F>(value12, value11);
    let (value14) = zkc::algebra::sub::<F>(value6, value8);
    let (value15) = zkc::algebra::mul::<F>(value14, value11);
    let (value16) = zkc::algebra::inverse::<F>(value9);
    let (value17) = zkc::algebra::mul::<F>(value15, value16);
    let (value18) = zkc::algebra::mul::<F>(challenge, value17);
    let (value19) = zkc::algebra::add::<F>(value13, value18);
    return (value19, value4, value1);
  }

  pub fn RowValueAlgorithm<F: domain Field>(row: Vector<F::Element>) -> (F::Element) requires (Field(F)) {
    let (value0) = zkc::algebra::index_constant() attributes ("0");
    let (value1) = zkc::algebra::vector_get::<F>(row, value0);
    return (value1);
  }

  pub fn CoordinatesAlgorithm<>(query: index, size: index) -> (index, index) {
    let (value0) = zkc::algebra::index_constant() attributes ("2");
    let (value1) = zkc::algebra::index_div(size, value0);
    let (value2) = zkc::algebra::index_mod(query, value1);
    let (value3) = zkc::algebra::index_add(value2, value1);
    return (value2, value3);
  }

  pub fn CommitBaseAlgorithm<C: domain Commitment>(
    values: Vector<C::ValueField::Element>,
    width: index
  ) -> (Commitment<C>, OpeningState<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = zkc::oracle::commit::<C>(values, width);
    return (value00, value01);
  }

  pub configure CommitBase = CommitBaseAlgorithm(C = "rows.merkle-keccak256.koala-bear/1");
  pub fn CommitExtensionAlgorithm<C: domain Commitment>(
    values: Vector<C::ValueField::Element>,
    width: index
  ) -> (Commitment<C>, OpeningState<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = zkc::oracle::commit::<C>(values, width);
    return (value00, value01);
  }

  pub configure CommitExtension = CommitExtensionAlgorithm(
    C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
  );
  pub fn OpenBaseAlgorithm<C: domain Commitment>(
    state: OpeningState<C>,
    index: index
  ) -> (Vector<C::ValueField::Element>, Proof<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = zkc::oracle::open::<C>(state, index);
    return (value00, value01);
  }

  pub configure OpenBase = OpenBaseAlgorithm(C = "rows.merkle-keccak256.koala-bear/1");
  pub fn OpenExtensionAlgorithm<C: domain Commitment>(
    state: OpeningState<C>,
    index: index
  ) -> (Vector<C::ValueField::Element>, Proof<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = zkc::oracle::open::<C>(state, index);
    return (value00, value01);
  }

  pub configure OpenExtension = OpenExtensionAlgorithm(
    C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
  );
  pub fn CheckBaseAlgorithm<C: domain Commitment>(
    root: Commitment<C>,
    width: index,
    height: index,
    index: index,
    row: Vector<C::ValueField::Element>,
    path: Proof<C>
  ) -> (bool) requires (VectorCommitment(C)) {
    let (value0) = zkc::oracle::check::<C>(root, width, height, index, row, path);
    zkc::core::require(value0);
    return (value0);
  }

  pub configure CheckBase = CheckBaseAlgorithm(C = "rows.merkle-keccak256.koala-bear/1");
  pub fn CheckExtensionAlgorithm<C: domain Commitment>(
    root: Commitment<C>,
    width: index,
    height: index,
    index: index,
    row: Vector<C::ValueField::Element>,
    path: Proof<C>
  ) -> (bool) requires (VectorCommitment(C)) {
    let (value0) = zkc::oracle::check::<C>(root, width, height, index, row, path);
    zkc::core::require(value0);
    return (value0);
  }

  pub configure CheckExtension = CheckExtensionAlgorithm(
    C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
  );
  pub fn DrawAlgorithm<F: domain Field>(coins: Rng<F>) -> (F::Element, Rng<F>) requires (Field(F)) {
    [draw] let (value00, value01) = zkc::random::draw::<F>(coins);
    return (value00, value01);
  }

  pub configure Draw = DrawAlgorithm(F = "koala-bear.ext8-binomial3");
  pub fn QueryAlgorithm<F: domain Field>(coins: Rng<F>, bound: index) -> (index, Rng<F>) requires (
    IndexRandomness(F)
  ) {
    [draw] let (value00, value01) = zkc::random::index::<F>(coins, bound);
    return (value00, value01);
  }

  pub configure Query = QueryAlgorithm(F = "koala-bear.ext8-binomial3");
  pub fn EmptyStatesAlgorithm<C: domain Commitment>() -> (OpeningStates<C>) requires (
    VectorCommitment(C)
  ) {
    let (value0) = zkc::oracle::opening_states_empty::<C>();
    return (value0);
  }

  pub fn EmptyRootsAlgorithm<C: domain Commitment>() -> (Commitments<C>) requires (VectorCommitment(C)) {
    let (value0) = zkc::oracle::commitments_empty::<C>();
    return (value0);
  }

  pub fn SaveStateAlgorithm<C: domain Commitment>(
    values: OpeningStates<C>,
    value: OpeningState<C>
  ) -> (OpeningStates<C>) requires (VectorCommitment(C)) {
    let (value0) = zkc::oracle::opening_states_append::<C>(values, value);
    return (value0);
  }

  pub fn SaveRootAlgorithm<C: domain Commitment>(
    values: Commitments<C>,
    value: Commitment<C>
  ) -> (Commitments<C>) requires (VectorCommitment(C)) {
    let (value0) = zkc::oracle::commitments_append::<C>(values, value);
    return (value0);
  }

  pub fn StateAtAlgorithm<C: domain Commitment>(
    values: OpeningStates<C>,
    index: index
  ) -> (OpeningState<C>) requires (VectorCommitment(C)) {
    let (value0) = zkc::oracle::opening_states_at::<C>(values, index);
    return (value0);
  }

  pub fn RootAtAlgorithm<C: domain Commitment>(values: Commitments<C>, index: index) -> (Commitment<C>) requires (
    VectorCommitment(C)
  ) {
    let (value0) = zkc::oracle::commitments_at::<C>(values, index);
    return (value0);
  }

  pub fn EmptyChallengesAlgorithm<F: domain Field>() -> (Vector<F::Element>) requires (Field(F)) {
    let (value0) = zkc::algebra::vector_empty::<F>();
    return (value0);
  }

  pub fn SaveChallengeAlgorithm<F: domain Field>(
    values: Vector<F::Element>,
    value: F::Element
  ) -> (Vector<F::Element>) requires (Field(F)) {
    let (value0) = zkc::algebra::vector_append::<F>(values, value);
    return (value0);
  }

  pub fn ChallengeAtAlgorithm<F: domain Field>(values: Vector<F::Element>, index: index) -> (F::Element) requires (
    Field(F)
  ) {
    let (value0) = zkc::algebra::vector_get::<F>(values, index);
    return (value0);
  }

  pub fn NextIndexAlgorithm<>(index: index) -> (index) {
    let (value0) = zkc::algebra::index_constant() attributes ("1");
    let (value1) = zkc::algebra::index_add(index, value0);
    return (value1);
  }

  pub fn QueryInitAlgorithm<>() -> (Indices, index) {
    let (value0) = zkc::algebra::indices_empty();
    let (value1) = zkc::algebra::index_constant() attributes ("0");
    return (value0, value1);
  }

  pub fn QueryAppendAlgorithm<>(values: Indices, index: index) -> (Indices) {
    let (value0) = zkc::algebra::indices_append(values, index);
    return (value0);
  }

  pub fn QueryAtAlgorithm<>(values: Indices, position: index) -> (index, index) {
    let (value0) = zkc::algebra::indices_at(values, position);
    let (value1) = zkc::algebra::index_constant() attributes ("1");
    let (value2) = zkc::algebra::index_add(position, value1);
    return (value0, value2);
  }

  pub fn ParametersAlgorithm<F: domain Field>(
  ) -> (index, index, index, index, index, index, F::Element) requires (Field(F)) {
    let (value0) = zkc::algebra::index_constant() attributes ("0");
    let (value1) = zkc::algebra::index_constant() attributes ("1");
    let (value2) = zkc::algebra::index_constant() attributes ("2");
    let (value3) = zkc::algebra::index_constant() attributes ("8");
    let (value4) = zkc::algebra::index_constant() attributes ("16");
    let (value5) = zkc::algebra::index_constant() attributes ("32");
    let (value6) = zkc::algebra::constant::<F>() attributes ("3");
    return (value0, value1, value2, value3, value4, value5, value6);
  }

  pub configure Prepare = PrepareAlgorithm(F = "koala-bear");
  pub configure Interleave = InterleaveAlgorithm(F = "koala-bear");
  pub configure LiftVector = LiftVectorAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure LiftScalar = LiftScalarAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure LiftPolynomial = LiftPolynomialAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure Auxiliary = AuxiliaryAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure Quotients = QuotientsAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure Equal = EqualAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure Evaluate = EvaluateAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure CheckOutOfDomain = CheckOutOfDomainAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure Deep = DeepAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure DeepRow = DeepRowAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure Fold = FoldAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure Terminal = TerminalAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure FoldPair = FoldPairAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure RowValue = RowValueAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure Coordinates = CoordinatesAlgorithm();
  pub configure EmptyStates = EmptyStatesAlgorithm(
    C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
  );
  pub configure EmptyRoots = EmptyRootsAlgorithm(
    C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
  );
  pub configure SaveState = SaveStateAlgorithm(C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1");
  pub configure SaveRoot = SaveRootAlgorithm(C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1");
  pub configure StateAt = StateAtAlgorithm(C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1");
  pub configure RootAt = RootAtAlgorithm(C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1");
  pub configure EmptyChallenges = EmptyChallengesAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure SaveChallenge = SaveChallengeAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure ChallengeAt = ChallengeAtAlgorithm(F = "koala-bear.ext8-binomial3");
  pub configure NextIndex = NextIndexAlgorithm();
  pub configure QueryInit = QueryInitAlgorithm();
  pub configure QueryAppend = QueryAppendAlgorithm();
  pub configure QueryAt = QueryAtAlgorithm();
  pub configure Parameters = ParametersAlgorithm(F = "koala-bear.ext8-binomial3");
  pub fn HalfSizeAlgorithm<>(size: index) -> (index) {
    let (value0) = zkc::algebra::index_constant() attributes ("2");
    let (value1) = zkc::algebra::index_div(size, value0);
    return (value1);
  }

  pub configure HalfSize = HalfSizeAlgorithm();
  pub fn DoubleSizeAlgorithm<>(size: index) -> (index) {
    let (value0) = zkc::algebra::index_constant() attributes ("2");
    let (value1) = zkc::algebra::index_mul(size, value0);
    return (value1);
  }

  pub configure DoubleSize = DoubleSizeAlgorithm();
  pub fn SquareAlgorithm<F: domain Field>(x: F::Element) -> (F::Element) requires (Field(F)) {
    let (value0) = zkc::algebra::mul::<F>(x, x);
    return (value0);
  }

  pub configure Square = SquareAlgorithm(F = "koala-bear.ext8-binomial3");
}
