// Reused arithmetic from examples/protocols/air-oracle/air-permutation.pir.
module {
  library(namespace="zkc.examples", name="air", version="1", resolution="source-v1");

  pub fn PrepareAlgorithm<F: domain Field>(
    values: Vector<F::Element>
  ) -> (Polynomial<F>, Vector<F::Element>) requires (TwoAdicField(F)) {
    let (value0) = vector.length_check::<F>(values) attributes ("8");
    control.require(value0);
    let (value2) = field.constant::<F>() attributes ("1");
    let (value3) = poly.coset_interpolate::<F>(values, value2);
    let (value4) = field.constant::<F>() attributes ("3");
    let (value5) = index.constant() attributes ("32");
    let (value6) = poly.coset_evaluate::<F>(value3, value4, value5);
    return (value3, value6);
  }

  pub fn InterleaveAlgorithm<F: domain Field>(
    a: Vector<F::Element>,
    b: Vector<F::Element>
  ) -> (Vector<F::Element>) requires (Field(F)) {
    let (value0) = vector.interleave::<F>(a, b);
    return (value0);
  }

  pub fn LiftVectorAlgorithm<F: domain Field>(
    value: Vector<F::BaseField::Element>
  ) -> (Vector<F::Element>) requires (ExtensionField(F)) {
    let (value0) = vector.embed::<F>(value);
    return (value0);
  }

  pub fn LiftScalarAlgorithm<F: domain Field>(value: F::BaseField::Element) -> (F::Element) requires (
    ExtensionField(F)
  ) {
    let (value0) = field.embed::<F>(value);
    return (value0);
  }

  pub fn LiftPolynomialAlgorithm<F: domain Field>(value: Polynomial<F::BaseField>) -> (Polynomial<F>) requires (
    ExtensionField(F),
    Field(F::BaseField)
  ) {
    let (value0) = poly.coefficients::<F::BaseField>(value);
    let (value1) = vector.embed::<F>(value0);
    let (value2) = poly.from_coefficients::<F>(value1);
    return (value2);
  }

  pub fn AuxiliaryAlgorithm<F: domain Field>(
    values: Vector<F::BaseField::Element>,
    beta: F::Element
  ) -> (Polynomial<F>, Vector<F::Element>, F::Element) requires (ExtensionField(F), TwoAdicField(F)) {
    let (value0) = vector.embed::<F>(values);
    let (value1) = index.constant() attributes ("8");
    let (value2) = vector.fill::<F>(beta, value1);
    let (value3) = vector.sub::<F>(value2, value0);
    let (value4) = vector.prefix_product::<F>(value3);
    let (value5) = index.constant() attributes ("7");
    let (value6) = vector.get::<F>(value4, value5);
    let (value7) = field.constant::<F>() attributes ("1");
    let (value8) = poly.coset_interpolate::<F>(value4, value7);
    let (value9) = field.constant::<F>() attributes ("3");
    let (value10) = index.constant() attributes ("32");
    let (value11) = poly.coset_evaluate::<F>(value8, value9, value10);
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
    let (value0) = index.constant() attributes ("32");
    let (value1) = field.constant::<F>() attributes ("3");
    let (value2) = poly.domain_points::<F>(value1, value0);
    let (value3) = index.constant() attributes ("4");
    let (value4) = vector.rotate::<F>(left, value3);
    let (value5) = index.constant() attributes ("4");
    let (value6) = vector.rotate::<F>(right, value5);
    let (value7) = index.constant() attributes ("4");
    let (value8) = vector.rotate::<F>(sum_values, value7);
    let (value9) = index.constant() attributes ("4");
    let (value10) = vector.rotate::<F>(left_product, value9);
    let (value11) = index.constant() attributes ("4");
    let (value12) = vector.rotate::<F>(right_product, value11);
    let (value13) = field.constant::<F>() attributes ("1");
    let (value14) = vector.fill::<F>(value13, value0);
    let (value15) = field.constant::<F>() attributes ("1");
    let (value16) = index.constant() attributes ("8");
    let (value17) = index.constant() attributes ("7");
    let (value18) = poly.domain_point::<F>(value15, value16, value17);
    let (value19) = vector.sub::<F>(value2, value14);
    let (value20) = vector.fill::<F>(value18, value0);
    let (value21) = vector.sub::<F>(value2, value20);
    let (value22) = vector.mul::<F>(value2, value2);
    let (value23) = vector.mul::<F>(value22, value22);
    let (value24) = vector.mul::<F>(value23, value23);
    let (value25) = vector.sub::<F>(value24, value14);
    let (value26) = vector.inverse::<F>(value19);
    let (value27) = vector.inverse::<F>(value25);
    let (value28) = vector.mul::<F>(value21, value27);
    let (value29) = vector.inverse::<F>(value21);
    let (value30) = field.constant::<F>() attributes ("0");
    let (value31) = vector.fill::<F>(value30, value0);
    let (value32) = vector.fill::<F>(initial, value0);
    let (value33) = vector.sub::<F>(value31, value32);
    let (value34) = vector.add::<F>(left, value33);
    let (value35) = field.constant::<F>() attributes ("0");
    let (value36) = vector.fill::<F>(value35, value0);
    let (value37) = vector.sub::<F>(value36, left);
    let (value38) = vector.add::<F>(value4, value37);
    let (value39) = field.constant::<F>() attributes ("0");
    let (value40) = vector.fill::<F>(value39, value0);
    let (value41) = field.constant::<F>() attributes ("1");
    let (value42) = vector.fill::<F>(value41, value0);
    let (value43) = vector.sub::<F>(value40, value42);
    let (value44) = vector.add::<F>(value38, value43);
    let (value45) = field.constant::<F>() attributes ("0");
    let (value46) = vector.fill::<F>(value45, value0);
    let (value47) = vector.fill::<F>(final_value, value0);
    let (value48) = vector.sub::<F>(value46, value47);
    let (value49) = vector.add::<F>(left, value48);
    let (value50) = field.constant::<F>() attributes ("0");
    let (value51) = vector.fill::<F>(value50, value0);
    let (value52) = vector.fill::<F>(beta, value0);
    let (value53) = field.constant::<F>() attributes ("0");
    let (value54) = vector.fill::<F>(value53, value0);
    let (value55) = vector.sub::<F>(value54, left);
    let (value56) = vector.add::<F>(value52, value55);
    let (value57) = vector.sub::<F>(value51, value56);
    let (value58) = vector.add::<F>(left_product, value57);
    let (value59) = field.constant::<F>() attributes ("0");
    let (value60) = vector.fill::<F>(value59, value0);
    let (value61) = vector.fill::<F>(beta, value0);
    let (value62) = field.constant::<F>() attributes ("0");
    let (value63) = vector.fill::<F>(value62, value0);
    let (value64) = vector.sub::<F>(value63, value4);
    let (value65) = vector.add::<F>(value61, value64);
    let (value66) = vector.mul::<F>(left_product, value65);
    let (value67) = vector.sub::<F>(value60, value66);
    let (value68) = vector.add::<F>(value10, value67);
    let (value69) = field.constant::<F>() attributes ("0");
    let (value70) = vector.fill::<F>(value69, value0);
    let (value71) = vector.fill::<F>(left_terminal, value0);
    let (value72) = vector.sub::<F>(value70, value71);
    let (value73) = vector.add::<F>(left_product, value72);
    let (value74) = field.constant::<F>() attributes ("0");
    let (value75) = vector.fill::<F>(value74, value0);
    let (value76) = vector.sub::<F>(value75, right);
    let (value77) = vector.add::<F>(sum_values, value76);
    let (value78) = field.constant::<F>() attributes ("0");
    let (value79) = vector.fill::<F>(value78, value0);
    let (value80) = vector.sub::<F>(value79, sum_values);
    let (value81) = vector.add::<F>(value8, value80);
    let (value82) = field.constant::<F>() attributes ("0");
    let (value83) = vector.fill::<F>(value82, value0);
    let (value84) = vector.sub::<F>(value83, value6);
    let (value85) = vector.add::<F>(value81, value84);
    let (value86) = field.constant::<F>() attributes ("0");
    let (value87) = vector.fill::<F>(value86, value0);
    let (value88) = vector.fill::<F>(total, value0);
    let (value89) = vector.sub::<F>(value87, value88);
    let (value90) = vector.add::<F>(sum_values, value89);
    let (value91) = field.constant::<F>() attributes ("0");
    let (value92) = vector.fill::<F>(value91, value0);
    let (value93) = vector.fill::<F>(beta, value0);
    let (value94) = field.constant::<F>() attributes ("0");
    let (value95) = vector.fill::<F>(value94, value0);
    let (value96) = vector.sub::<F>(value95, right);
    let (value97) = vector.add::<F>(value93, value96);
    let (value98) = vector.sub::<F>(value92, value97);
    let (value99) = vector.add::<F>(right_product, value98);
    let (value100) = field.constant::<F>() attributes ("0");
    let (value101) = vector.fill::<F>(value100, value0);
    let (value102) = vector.fill::<F>(beta, value0);
    let (value103) = field.constant::<F>() attributes ("0");
    let (value104) = vector.fill::<F>(value103, value0);
    let (value105) = vector.sub::<F>(value104, value6);
    let (value106) = vector.add::<F>(value102, value105);
    let (value107) = vector.mul::<F>(right_product, value106);
    let (value108) = vector.sub::<F>(value101, value107);
    let (value109) = vector.add::<F>(value12, value108);
    let (value110) = field.constant::<F>() attributes ("0");
    let (value111) = vector.fill::<F>(value110, value0);
    let (value112) = vector.fill::<F>(right_terminal, value0);
    let (value113) = vector.sub::<F>(value111, value112);
    let (value114) = vector.add::<F>(right_product, value113);
    let (value115) = field.constant::<F>() attributes ("0");
    let (value116) = vector.fill::<F>(value115, value0);
    let (value117) = vector.scale::<F>(value116, alpha);
    let (value118) = vector.mul::<F>(value73, value29);
    let (value119) = vector.add::<F>(value117, value118);
    let (value120) = vector.scale::<F>(value119, alpha);
    let (value121) = vector.mul::<F>(value68, value28);
    let (value122) = vector.add::<F>(value120, value121);
    let (value123) = vector.scale::<F>(value122, alpha);
    let (value124) = vector.mul::<F>(value58, value26);
    let (value125) = vector.add::<F>(value123, value124);
    let (value126) = vector.scale::<F>(value125, alpha);
    let (value127) = vector.mul::<F>(value49, value29);
    let (value128) = vector.add::<F>(value126, value127);
    let (value129) = vector.scale::<F>(value128, alpha);
    let (value130) = vector.mul::<F>(value44, value28);
    let (value131) = vector.add::<F>(value129, value130);
    let (value132) = vector.scale::<F>(value131, alpha);
    let (value133) = vector.mul::<F>(value34, value26);
    let (value134) = vector.add::<F>(value132, value133);
    let (value135) = field.constant::<F>() attributes ("0");
    let (value136) = vector.fill::<F>(value135, value0);
    let (value137) = vector.scale::<F>(value136, alpha);
    let (value138) = vector.mul::<F>(value114, value29);
    let (value139) = vector.add::<F>(value137, value138);
    let (value140) = vector.scale::<F>(value139, alpha);
    let (value141) = vector.mul::<F>(value109, value28);
    let (value142) = vector.add::<F>(value140, value141);
    let (value143) = vector.scale::<F>(value142, alpha);
    let (value144) = vector.mul::<F>(value99, value26);
    let (value145) = vector.add::<F>(value143, value144);
    let (value146) = vector.scale::<F>(value145, alpha);
    let (value147) = vector.mul::<F>(value90, value29);
    let (value148) = vector.add::<F>(value146, value147);
    let (value149) = vector.scale::<F>(value148, alpha);
    let (value150) = vector.mul::<F>(value85, value28);
    let (value151) = vector.add::<F>(value149, value150);
    let (value152) = vector.scale::<F>(value151, alpha);
    let (value153) = vector.mul::<F>(value77, value26);
    let (value154) = vector.add::<F>(value152, value153);
    let (value155) = poly.coset_interpolate::<F>(value134, value1);
    let (value156) = poly.coset_interpolate::<F>(value154, value1);
    let (value157) = poly.degree_check::<F>(value155) attributes ("7");
    control.require(value157);
    let (value159) = poly.degree_check::<F>(value156) attributes ("7");
    control.require(value159);
    let (value161) = vector.interleave::<F>(value134, value154);
    return (value155, value156, value134, value154, value161);
  }

  pub fn EqualAlgorithm<F: domain Field>(a: F::Element, b: F::Element) -> (bool) requires (Field(F)) {
    let (value0) = field.equal::<F>(a, b);
    control.require(value0);
    return (value0);
  }

  pub fn EvaluateAlgorithm<F: domain Field>(p: Polynomial<F>, z: F::Element) -> (F::Element, F::Element) requires (
    TwoAdicField(F)
  ) {
    let (value0) = index.constant() attributes ("8");
    let (value1) = poly.domain_root::<F>(value0);
    let (value2) = field.mul::<F>(z, value1);
    let (value3) = poly.univariate_evaluate::<F>(p, z);
    let (value4) = poly.univariate_evaluate::<F>(p, value2);
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
    let (value0) = field.inverse::<F>(z);
    let (value1) = field.mul::<F>(z, z);
    let (value2) = field.mul::<F>(value1, value1);
    let (value3) = field.mul::<F>(value2, value2);
    let (value4) = field.constant::<F>() attributes ("1");
    let (value5) = field.sub::<F>(value3, value4);
    let (value6) = field.inverse::<F>(value5);
    let (value7) = field.mul::<F>(z, z);
    let (value8) = field.mul::<F>(value7, value7);
    let (value9) = field.mul::<F>(value8, value8);
    let (value10) = field.mul::<F>(value9, value9);
    let (value11) = field.mul::<F>(value10, value10);
    let (value12) = field.constant::<F>() attributes ("3");
    let (value13) = field.mul::<F>(value12, value12);
    let (value14) = field.mul::<F>(value13, value13);
    let (value15) = field.mul::<F>(value14, value14);
    let (value16) = field.mul::<F>(value15, value15);
    let (value17) = field.mul::<F>(value16, value16);
    let (value18) = field.sub::<F>(value11, value17);
    let (value19) = field.inverse::<F>(value18);
    let (value20) = field.constant::<F>() attributes ("1");
    let (value21) = field.constant::<F>() attributes ("1");
    let (value22) = index.constant() attributes ("8");
    let (value23) = index.constant() attributes ("7");
    let (value24) = poly.domain_point::<F>(value21, value22, value23);
    let (value25) = field.sub::<F>(z, value20);
    let (value26) = field.sub::<F>(z, value24);
    let (value27) = field.mul::<F>(z, z);
    let (value28) = field.mul::<F>(value27, value27);
    let (value29) = field.mul::<F>(value28, value28);
    let (value30) = field.sub::<F>(value29, value20);
    let (value31) = field.inverse::<F>(value25);
    let (value32) = field.inverse::<F>(value30);
    let (value33) = field.mul::<F>(value26, value32);
    let (value34) = field.inverse::<F>(value26);
    let (value35) = field.constant::<F>() attributes ("0");
    let (value36) = field.sub::<F>(value35, initial);
    let (value37) = field.add::<F>(at_z_0, value36);
    let (value38) = field.constant::<F>() attributes ("0");
    let (value39) = field.sub::<F>(value38, at_z_0);
    let (value40) = field.add::<F>(at_next_0, value39);
    let (value41) = field.constant::<F>() attributes ("0");
    let (value42) = field.constant::<F>() attributes ("1");
    let (value43) = field.sub::<F>(value41, value42);
    let (value44) = field.add::<F>(value40, value43);
    let (value45) = field.constant::<F>() attributes ("0");
    let (value46) = field.sub::<F>(value45, final_value);
    let (value47) = field.add::<F>(at_z_0, value46);
    let (value48) = field.constant::<F>() attributes ("0");
    let (value49) = field.constant::<F>() attributes ("0");
    let (value50) = field.sub::<F>(value49, at_z_0);
    let (value51) = field.add::<F>(beta, value50);
    let (value52) = field.sub::<F>(value48, value51);
    let (value53) = field.add::<F>(at_z_3, value52);
    let (value54) = field.constant::<F>() attributes ("0");
    let (value55) = field.constant::<F>() attributes ("0");
    let (value56) = field.sub::<F>(value55, at_next_0);
    let (value57) = field.add::<F>(beta, value56);
    let (value58) = field.mul::<F>(at_z_3, value57);
    let (value59) = field.sub::<F>(value54, value58);
    let (value60) = field.add::<F>(at_next_3, value59);
    let (value61) = field.constant::<F>() attributes ("0");
    let (value62) = field.sub::<F>(value61, left_terminal);
    let (value63) = field.add::<F>(at_z_3, value62);
    let (value64) = field.constant::<F>() attributes ("0");
    let (value65) = field.sub::<F>(value64, at_z_1);
    let (value66) = field.add::<F>(at_z_2, value65);
    let (value67) = field.constant::<F>() attributes ("0");
    let (value68) = field.sub::<F>(value67, at_z_2);
    let (value69) = field.add::<F>(at_next_2, value68);
    let (value70) = field.constant::<F>() attributes ("0");
    let (value71) = field.sub::<F>(value70, at_next_1);
    let (value72) = field.add::<F>(value69, value71);
    let (value73) = field.constant::<F>() attributes ("0");
    let (value74) = field.sub::<F>(value73, total);
    let (value75) = field.add::<F>(at_z_2, value74);
    let (value76) = field.constant::<F>() attributes ("0");
    let (value77) = field.constant::<F>() attributes ("0");
    let (value78) = field.sub::<F>(value77, at_z_1);
    let (value79) = field.add::<F>(beta, value78);
    let (value80) = field.sub::<F>(value76, value79);
    let (value81) = field.add::<F>(at_z_4, value80);
    let (value82) = field.constant::<F>() attributes ("0");
    let (value83) = field.constant::<F>() attributes ("0");
    let (value84) = field.sub::<F>(value83, at_next_1);
    let (value85) = field.add::<F>(beta, value84);
    let (value86) = field.mul::<F>(at_z_4, value85);
    let (value87) = field.sub::<F>(value82, value86);
    let (value88) = field.add::<F>(at_next_4, value87);
    let (value89) = field.constant::<F>() attributes ("0");
    let (value90) = field.sub::<F>(value89, right_terminal);
    let (value91) = field.add::<F>(at_z_4, value90);
    let (value92) = field.constant::<F>() attributes ("0");
    let (value93) = field.mul::<F>(value92, alpha);
    let (value94) = field.mul::<F>(value63, value34);
    let (value95) = field.add::<F>(value93, value94);
    let (value96) = field.mul::<F>(value95, alpha);
    let (value97) = field.mul::<F>(value60, value33);
    let (value98) = field.add::<F>(value96, value97);
    let (value99) = field.mul::<F>(value98, alpha);
    let (value100) = field.mul::<F>(value53, value31);
    let (value101) = field.add::<F>(value99, value100);
    let (value102) = field.mul::<F>(value101, alpha);
    let (value103) = field.mul::<F>(value47, value34);
    let (value104) = field.add::<F>(value102, value103);
    let (value105) = field.mul::<F>(value104, alpha);
    let (value106) = field.mul::<F>(value44, value33);
    let (value107) = field.add::<F>(value105, value106);
    let (value108) = field.mul::<F>(value107, alpha);
    let (value109) = field.mul::<F>(value37, value31);
    let (value110) = field.add::<F>(value108, value109);
    let (value111) = field.constant::<F>() attributes ("0");
    let (value112) = field.mul::<F>(value111, alpha);
    let (value113) = field.mul::<F>(value91, value34);
    let (value114) = field.add::<F>(value112, value113);
    let (value115) = field.mul::<F>(value114, alpha);
    let (value116) = field.mul::<F>(value88, value33);
    let (value117) = field.add::<F>(value115, value116);
    let (value118) = field.mul::<F>(value117, alpha);
    let (value119) = field.mul::<F>(value81, value31);
    let (value120) = field.add::<F>(value118, value119);
    let (value121) = field.mul::<F>(value120, alpha);
    let (value122) = field.mul::<F>(value75, value34);
    let (value123) = field.add::<F>(value121, value122);
    let (value124) = field.mul::<F>(value123, alpha);
    let (value125) = field.mul::<F>(value72, value33);
    let (value126) = field.add::<F>(value124, value125);
    let (value127) = field.mul::<F>(value126, alpha);
    let (value128) = field.mul::<F>(value66, value31);
    let (value129) = field.add::<F>(value127, value128);
    let (value130) = field.equal::<F>(value110, quotient_left);
    control.require(value130);
    let (value132) = field.equal::<F>(value129, quotient_right);
    control.require(value132);
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
    let (value0) = index.constant() attributes ("32");
    let (value1) = field.constant::<F>() attributes ("3");
    let (value2) = poly.domain_points::<F>(value1, value0);
    let (value3) = index.constant() attributes ("8");
    let (value4) = poly.domain_root::<F>(value3);
    let (value5) = field.mul::<F>(z, value4);
    let (value6) = vector.fill::<F>(z, value0);
    let (value7) = vector.sub::<F>(value2, value6);
    let (value8) = vector.inverse::<F>(value7);
    let (value9) = vector.fill::<F>(value5, value0);
    let (value10) = vector.sub::<F>(value2, value9);
    let (value11) = vector.inverse::<F>(value10);
    let (value12) = field.constant::<F>() attributes ("0");
    let (value13) = vector.fill::<F>(value12, value0);
    let (value14) = field.constant::<F>() attributes ("1");
    let (value15) = vector.fill::<F>(at_z_0, value0);
    let (value16) = vector.sub::<F>(left, value15);
    let (value17) = vector.mul::<F>(value16, value8);
    let (value18) = vector.scale::<F>(value17, value14);
    let (value19) = vector.add::<F>(value13, value18);
    let (value20) = field.mul::<F>(value14, eta);
    let (value21) = vector.fill::<F>(at_next_0, value0);
    let (value22) = vector.sub::<F>(left, value21);
    let (value23) = vector.mul::<F>(value22, value11);
    let (value24) = vector.scale::<F>(value23, value20);
    let (value25) = vector.add::<F>(value19, value24);
    let (value26) = field.mul::<F>(value20, eta);
    let (value27) = vector.fill::<F>(at_z_1, value0);
    let (value28) = vector.sub::<F>(right, value27);
    let (value29) = vector.mul::<F>(value28, value8);
    let (value30) = vector.scale::<F>(value29, value26);
    let (value31) = vector.add::<F>(value25, value30);
    let (value32) = field.mul::<F>(value26, eta);
    let (value33) = vector.fill::<F>(at_next_1, value0);
    let (value34) = vector.sub::<F>(right, value33);
    let (value35) = vector.mul::<F>(value34, value11);
    let (value36) = vector.scale::<F>(value35, value32);
    let (value37) = vector.add::<F>(value31, value36);
    let (value38) = field.mul::<F>(value32, eta);
    let (value39) = vector.fill::<F>(at_z_2, value0);
    let (value40) = vector.sub::<F>(sum_values, value39);
    let (value41) = vector.mul::<F>(value40, value8);
    let (value42) = vector.scale::<F>(value41, value38);
    let (value43) = vector.add::<F>(value37, value42);
    let (value44) = field.mul::<F>(value38, eta);
    let (value45) = vector.fill::<F>(at_next_2, value0);
    let (value46) = vector.sub::<F>(sum_values, value45);
    let (value47) = vector.mul::<F>(value46, value11);
    let (value48) = vector.scale::<F>(value47, value44);
    let (value49) = vector.add::<F>(value43, value48);
    let (value50) = field.mul::<F>(value44, eta);
    let (value51) = vector.fill::<F>(at_z_3, value0);
    let (value52) = vector.sub::<F>(left_product, value51);
    let (value53) = vector.mul::<F>(value52, value8);
    let (value54) = vector.scale::<F>(value53, value50);
    let (value55) = vector.add::<F>(value49, value54);
    let (value56) = field.mul::<F>(value50, eta);
    let (value57) = vector.fill::<F>(at_next_3, value0);
    let (value58) = vector.sub::<F>(left_product, value57);
    let (value59) = vector.mul::<F>(value58, value11);
    let (value60) = vector.scale::<F>(value59, value56);
    let (value61) = vector.add::<F>(value55, value60);
    let (value62) = field.mul::<F>(value56, eta);
    let (value63) = vector.fill::<F>(at_z_4, value0);
    let (value64) = vector.sub::<F>(right_product, value63);
    let (value65) = vector.mul::<F>(value64, value8);
    let (value66) = vector.scale::<F>(value65, value62);
    let (value67) = vector.add::<F>(value61, value66);
    let (value68) = field.mul::<F>(value62, eta);
    let (value69) = vector.fill::<F>(at_next_4, value0);
    let (value70) = vector.sub::<F>(right_product, value69);
    let (value71) = vector.mul::<F>(value70, value11);
    let (value72) = vector.scale::<F>(value71, value68);
    let (value73) = vector.add::<F>(value67, value72);
    let (value74) = field.mul::<F>(value68, eta);
    let (value75) = vector.fill::<F>(quotient_left, value0);
    let (value76) = vector.sub::<F>(qleft, value75);
    let (value77) = vector.mul::<F>(value76, value8);
    let (value78) = vector.scale::<F>(value77, value74);
    let (value79) = vector.add::<F>(value73, value78);
    let (value80) = field.mul::<F>(value74, eta);
    let (value81) = vector.fill::<F>(quotient_right, value0);
    let (value82) = vector.sub::<F>(qright, value81);
    let (value83) = vector.mul::<F>(value82, value8);
    let (value84) = vector.scale::<F>(value83, value80);
    let (value85) = vector.add::<F>(value79, value84);
    let (value86) = field.mul::<F>(value80, eta);
    let (value87) = field.constant::<F>() attributes ("1");
    let (value88) = vector.fill::<F>(value87, value0);
    let (value89) = vector.scale::<F>(value2, degree_mix);
    let (value90) = vector.add::<F>(value88, value89);
    let (value91) = vector.mul::<F>(value90, value85);
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
    let (value0) = index.constant() attributes ("0");
    let (value1) = vector.get::<F>(main_left, value0);
    let (value2) = index.constant() attributes ("0");
    let (value3) = vector.get::<F>(main_right, value2);
    let (value4) = index.constant() attributes ("1");
    let (value5) = vector.get::<F>(main_right, value4);
    let (value6) = index.constant() attributes ("0");
    let (value7) = vector.get::<F>(aux_left, value6);
    let (value8) = index.constant() attributes ("0");
    let (value9) = vector.get::<F>(aux_right, value8);
    let (value10) = index.constant() attributes ("0");
    let (value11) = vector.get::<F>(quotient, value10);
    let (value12) = index.constant() attributes ("1");
    let (value13) = vector.get::<F>(quotient, value12);
    let (value14) = field.constant::<F>() attributes ("3");
    let (value15) = index.constant() attributes ("32");
    let (value16) = poly.domain_point::<F>(value14, value15, index);
    let (value17) = index.constant() attributes ("8");
    let (value18) = poly.domain_root::<F>(value17);
    let (value19) = field.mul::<F>(z, value18);
    let (value20) = field.sub::<F>(value16, z);
    let (value21) = field.inverse::<F>(value20);
    let (value22) = field.sub::<F>(value16, value19);
    let (value23) = field.inverse::<F>(value22);
    let (value24) = field.constant::<F>() attributes ("0");
    let (value25) = field.constant::<F>() attributes ("1");
    let (value26) = field.sub::<F>(value1, at_z_0);
    let (value27) = field.mul::<F>(value26, value21);
    let (value28) = field.mul::<F>(value27, value25);
    let (value29) = field.add::<F>(value24, value28);
    let (value30) = field.mul::<F>(value25, eta);
    let (value31) = field.sub::<F>(value1, at_next_0);
    let (value32) = field.mul::<F>(value31, value23);
    let (value33) = field.mul::<F>(value32, value30);
    let (value34) = field.add::<F>(value29, value33);
    let (value35) = field.mul::<F>(value30, eta);
    let (value36) = field.sub::<F>(value3, at_z_1);
    let (value37) = field.mul::<F>(value36, value21);
    let (value38) = field.mul::<F>(value37, value35);
    let (value39) = field.add::<F>(value34, value38);
    let (value40) = field.mul::<F>(value35, eta);
    let (value41) = field.sub::<F>(value3, at_next_1);
    let (value42) = field.mul::<F>(value41, value23);
    let (value43) = field.mul::<F>(value42, value40);
    let (value44) = field.add::<F>(value39, value43);
    let (value45) = field.mul::<F>(value40, eta);
    let (value46) = field.sub::<F>(value5, at_z_2);
    let (value47) = field.mul::<F>(value46, value21);
    let (value48) = field.mul::<F>(value47, value45);
    let (value49) = field.add::<F>(value44, value48);
    let (value50) = field.mul::<F>(value45, eta);
    let (value51) = field.sub::<F>(value5, at_next_2);
    let (value52) = field.mul::<F>(value51, value23);
    let (value53) = field.mul::<F>(value52, value50);
    let (value54) = field.add::<F>(value49, value53);
    let (value55) = field.mul::<F>(value50, eta);
    let (value56) = field.sub::<F>(value7, at_z_3);
    let (value57) = field.mul::<F>(value56, value21);
    let (value58) = field.mul::<F>(value57, value55);
    let (value59) = field.add::<F>(value54, value58);
    let (value60) = field.mul::<F>(value55, eta);
    let (value61) = field.sub::<F>(value7, at_next_3);
    let (value62) = field.mul::<F>(value61, value23);
    let (value63) = field.mul::<F>(value62, value60);
    let (value64) = field.add::<F>(value59, value63);
    let (value65) = field.mul::<F>(value60, eta);
    let (value66) = field.sub::<F>(value9, at_z_4);
    let (value67) = field.mul::<F>(value66, value21);
    let (value68) = field.mul::<F>(value67, value65);
    let (value69) = field.add::<F>(value64, value68);
    let (value70) = field.mul::<F>(value65, eta);
    let (value71) = field.sub::<F>(value9, at_next_4);
    let (value72) = field.mul::<F>(value71, value23);
    let (value73) = field.mul::<F>(value72, value70);
    let (value74) = field.add::<F>(value69, value73);
    let (value75) = field.mul::<F>(value70, eta);
    let (value76) = field.sub::<F>(value11, quotient_left);
    let (value77) = field.mul::<F>(value76, value21);
    let (value78) = field.mul::<F>(value77, value75);
    let (value79) = field.add::<F>(value74, value78);
    let (value80) = field.mul::<F>(value75, eta);
    let (value81) = field.sub::<F>(value13, quotient_right);
    let (value82) = field.mul::<F>(value81, value21);
    let (value83) = field.mul::<F>(value82, value80);
    let (value84) = field.add::<F>(value79, value83);
    let (value85) = field.mul::<F>(value80, eta);
    let (value86) = field.constant::<F>() attributes ("1");
    let (value87) = field.mul::<F>(value16, degree_mix);
    let (value88) = field.add::<F>(value86, value87);
    let (value89) = field.mul::<F>(value88, value84);
    return (value89);
  }

  pub fn FoldAlgorithm<F: domain Field>(
    values: Vector<F::Element>,
    shift: F::Element,
    challenge: F::Element
  ) -> (Vector<F::Element>, F::Element) requires (TwoAdicField(F), CharacteristicNotTwo(F)) {
    let (value0) = poly.even_odd_fold::<F>(values, shift, challenge);
    let (value1) = field.mul::<F>(shift, shift);
    return (value0, value1);
  }

  pub fn TerminalAlgorithm<F: domain Field>(values: Vector<F::Element>) -> (F::Element) requires (
    TwoAdicField(F)
  ) {
    let (value0) = index.constant() attributes ("0");
    let (value1) = vector.get::<F>(values, value0);
    let (value2) = field.constant::<F>() attributes ("1");
    let (value3) = poly.coset_interpolate::<F>(values, value2);
    let (value4) = poly.degree_check::<F>(value3) attributes ("0");
    control.require(value4);
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
    let (value0) = index.constant() attributes ("2");
    let (value1) = index.div(size, value0);
    let (value2) = index.div(previous, value1);
    let (value3) = vector.concat::<F>(a, b);
    let (value4) = vector.get::<F>(value3, value2);
    let (value5) = index.constant() attributes ("0");
    let (value6) = vector.get::<F>(a, value5);
    let (value7) = index.constant() attributes ("0");
    let (value8) = vector.get::<F>(b, value7);
    let (value9) = poly.domain_point::<F>(shift, size, index);
    let (value10) = field.constant::<F>() attributes ("2");
    let (value11) = field.inverse::<F>(value10);
    let (value12) = field.add::<F>(value6, value8);
    let (value13) = field.mul::<F>(value12, value11);
    let (value14) = field.sub::<F>(value6, value8);
    let (value15) = field.mul::<F>(value14, value11);
    let (value16) = field.inverse::<F>(value9);
    let (value17) = field.mul::<F>(value15, value16);
    let (value18) = field.mul::<F>(challenge, value17);
    let (value19) = field.add::<F>(value13, value18);
    return (value19, value4, value1);
  }

  pub fn RowValueAlgorithm<F: domain Field>(row: Vector<F::Element>) -> (F::Element) requires (Field(F)) {
    let (value0) = index.constant() attributes ("0");
    let (value1) = vector.get::<F>(row, value0);
    return (value1);
  }

  pub fn CoordinatesAlgorithm<>(query: index, size: index) -> (index, index) {
    let (value0) = index.constant() attributes ("2");
    let (value1) = index.div(size, value0);
    let (value2) = index.mod(query, value1);
    let (value3) = index.add(value2, value1);
    return (value2, value3);
  }

  pub fn CommitBaseAlgorithm<C: domain Commitment>(
    values: Vector<C::ValueField::Element>,
    width: index
  ) -> (Commitment<C>, OpeningState<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = oracle.commit::<C>(values, width);
    return (value00, value01);
  }

  pub configure CommitBase = CommitBaseAlgorithm(C = "rows.merkle-keccak256.koala-bear/1");
  pub fn CommitExtensionAlgorithm<C: domain Commitment>(
    values: Vector<C::ValueField::Element>,
    width: index
  ) -> (Commitment<C>, OpeningState<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = oracle.commit::<C>(values, width);
    return (value00, value01);
  }

  pub configure CommitExtension = CommitExtensionAlgorithm(
    C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
  );
  pub fn OpenBaseAlgorithm<C: domain Commitment>(
    state: OpeningState<C>,
    index: index
  ) -> (Vector<C::ValueField::Element>, Proof<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = oracle.open::<C>(state, index);
    return (value00, value01);
  }

  pub configure OpenBase = OpenBaseAlgorithm(C = "rows.merkle-keccak256.koala-bear/1");
  pub fn OpenExtensionAlgorithm<C: domain Commitment>(
    state: OpeningState<C>,
    index: index
  ) -> (Vector<C::ValueField::Element>, Proof<C>) requires (VectorCommitment(C)) {
    let (value00, value01) = oracle.open::<C>(state, index);
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
    let (value0) = oracle.check::<C>(root, width, height, index, row, path);
    control.require(value0);
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
    let (value0) = oracle.check::<C>(root, width, height, index, row, path);
    control.require(value0);
    return (value0);
  }

  pub configure CheckExtension = CheckExtensionAlgorithm(
    C = "rows.merkle-keccak256.koala-bear.ext8-binomial3/1"
  );
  pub fn DrawAlgorithm<F: domain Field>(coins: Rng<F>) -> (F::Element, Rng<F>) requires (Field(F)) {
    [draw] let (value00, value01) = random.draw::<F>(coins);
    return (value00, value01);
  }

  pub configure Draw = DrawAlgorithm(F = "koala-bear.ext8-binomial3");
  pub fn QueryAlgorithm<F: domain Field>(coins: Rng<F>, bound: index) -> (index, Rng<F>) requires (
    IndexRandomness(F)
  ) {
    [draw] let (value00, value01) = random.index::<F>(coins, bound);
    return (value00, value01);
  }

  pub configure Query = QueryAlgorithm(F = "koala-bear.ext8-binomial3");
  pub fn EmptyStatesAlgorithm<C: domain Commitment>() -> (OpeningStates<C>) requires (
    VectorCommitment(C)
  ) {
    let (value0) = opening_states.empty::<C>();
    return (value0);
  }

  pub fn EmptyRootsAlgorithm<C: domain Commitment>() -> (Commitments<C>) requires (VectorCommitment(C)) {
    let (value0) = commitments.empty::<C>();
    return (value0);
  }

  pub fn SaveStateAlgorithm<C: domain Commitment>(
    values: OpeningStates<C>,
    value: OpeningState<C>
  ) -> (OpeningStates<C>) requires (VectorCommitment(C)) {
    let (value0) = opening_states.append::<C>(values, value);
    return (value0);
  }

  pub fn SaveRootAlgorithm<C: domain Commitment>(
    values: Commitments<C>,
    value: Commitment<C>
  ) -> (Commitments<C>) requires (VectorCommitment(C)) {
    let (value0) = commitments.append::<C>(values, value);
    return (value0);
  }

  pub fn StateAtAlgorithm<C: domain Commitment>(
    values: OpeningStates<C>,
    index: index
  ) -> (OpeningState<C>) requires (VectorCommitment(C)) {
    let (value0) = opening_states.at::<C>(values, index);
    return (value0);
  }

  pub fn RootAtAlgorithm<C: domain Commitment>(values: Commitments<C>, index: index) -> (Commitment<C>) requires (
    VectorCommitment(C)
  ) {
    let (value0) = commitments.at::<C>(values, index);
    return (value0);
  }

  pub fn EmptyChallengesAlgorithm<F: domain Field>() -> (Vector<F::Element>) requires (Field(F)) {
    let (value0) = vector.empty::<F>();
    return (value0);
  }

  pub fn SaveChallengeAlgorithm<F: domain Field>(
    values: Vector<F::Element>,
    value: F::Element
  ) -> (Vector<F::Element>) requires (Field(F)) {
    let (value0) = vector.append::<F>(values, value);
    return (value0);
  }

  pub fn ChallengeAtAlgorithm<F: domain Field>(values: Vector<F::Element>, index: index) -> (F::Element) requires (
    Field(F)
  ) {
    let (value0) = vector.get::<F>(values, index);
    return (value0);
  }

  pub fn NextIndexAlgorithm<>(index: index) -> (index) {
    let (value0) = index.constant() attributes ("1");
    let (value1) = index.add(index, value0);
    return (value1);
  }

  pub fn QueryInitAlgorithm<>() -> (Indices, index) {
    let (value0) = indices.empty();
    let (value1) = index.constant() attributes ("0");
    return (value0, value1);
  }

  pub fn QueryAppendAlgorithm<>(values: Indices, index: index) -> (Indices) {
    let (value0) = indices.append(values, index);
    return (value0);
  }

  pub fn QueryAtAlgorithm<>(values: Indices, position: index) -> (index, index) {
    let (value0) = indices.at(values, position);
    let (value1) = index.constant() attributes ("1");
    let (value2) = index.add(position, value1);
    return (value0, value2);
  }

  pub fn ParametersAlgorithm<F: domain Field>(
  ) -> (index, index, index, index, index, index, F::Element) requires (Field(F)) {
    let (value0) = index.constant() attributes ("0");
    let (value1) = index.constant() attributes ("1");
    let (value2) = index.constant() attributes ("2");
    let (value3) = index.constant() attributes ("8");
    let (value4) = index.constant() attributes ("16");
    let (value5) = index.constant() attributes ("32");
    let (value6) = field.constant::<F>() attributes ("3");
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
    let (value0) = index.constant() attributes ("2");
    let (value1) = index.div(size, value0);
    return (value1);
  }

  pub configure HalfSize = HalfSizeAlgorithm();
  pub fn DoubleSizeAlgorithm<>(size: index) -> (index) {
    let (value0) = index.constant() attributes ("2");
    let (value1) = index.mul(size, value0);
    return (value1);
  }

  pub configure DoubleSize = DoubleSizeAlgorithm();
  pub fn SquareAlgorithm<F: domain Field>(x: F::Element) -> (F::Element) requires (Field(F)) {
    let (value0) = field.mul::<F>(x, x);
    return (value0);
  }

  pub configure Square = SquareAlgorithm(F = "koala-bear.ext8-binomial3");
}
