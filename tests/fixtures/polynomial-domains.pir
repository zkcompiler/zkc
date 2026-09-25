module {
  fn Work<F: domain Field>(p:Polynomial<F>,s:F::Element,t:F::Element,beta:F::Element,n:index)
    -> () requires (TwoAdicField(F),CharacteristicNotTwo(F)) {
    let v = poly::coset_evaluate::<F>(p,s,n);
    let back = poly::coset_interpolate::<F>(v,s);
    let points = poly::domain_points::<F>(s,n);
    let two = index::constant() attributes ("2");
    let zero = index::constant() attributes ("0");
    let point = poly::domain_point::<F>(s,n,zero);
    let length = vector::length::<F>(v);
    let length_points = poly::domain_points::<F>(s,length);
    let folded = poly::even_odd_fold::<F>(v,s,beta);
    let half = index::div(n,two);
    let square = field::mul::<F>(s,s);
    let next = poly::domain_points::<F>(square,half);
    let fold_back = poly::coset_interpolate::<F>(folded,square);
    let other = poly::coset_interpolate::<F>(v,t);
    let coefficients = poly::coefficients::<F>(back);
    let scalar = poly::univariate_evaluate::<F>(back,s);
    return ();
  }
  configure Concrete = Work(F=koala-bear);
  protocol Main {
    roles(P);
    inputs(P p:Polynomial<koala-bear>,P s:koala-bear::Element,
           P t:koala-bear::Element,P beta:koala-bear::Element,P n:index);
    local P: Concrete(p,s,t,beta,n);
    return ();
  }
  instance main_instance:Main {roles(P=P);} entry main=main_instance;
}
