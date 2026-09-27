use zkc::algebra::{TwoAdicField, CharacteristicNotTwo};
use zkc::poly::{Polynomial};
use zkc::algebra;
use zkc::poly;
fn Work<F: domain Field>(p:Polynomial<F>,s:F::Element,t:F::Element,beta:F::Element,n:index)
  -> () requires (TwoAdicField(F),CharacteristicNotTwo(F)) {
  let v = zkc::poly::coset_evaluate::<F>(p,s,n);
  let back = zkc::poly::coset_interpolate::<F>(v,s);
  let points = zkc::poly::domain_points::<F>(s,n);
  let two = zkc::algebra::index_constant() attributes ("2");
  let zero = zkc::algebra::index_constant() attributes ("0");
  let point = zkc::poly::domain_point::<F>(s,n,zero);
  let length = zkc::algebra::vector_length::<F>(v);
  let length_points = zkc::poly::domain_points::<F>(s,length);
  let folded = zkc::poly::even_odd_fold::<F>(v,s,beta);
  let half = zkc::algebra::index_div(n,two);
  let square = zkc::algebra::mul::<F>(s,s);
  let next = zkc::poly::domain_points::<F>(square,half);
  let fold_back = zkc::poly::coset_interpolate::<F>(folded,square);
  let other = zkc::poly::coset_interpolate::<F>(v,t);
  let coefficients = zkc::poly::coefficients::<F>(back);
  let scalar = zkc::poly::evaluate::<F>(back,s);
  return ();
}
configure Concrete = Work(F="koala-bear");
protocol Main {
  roles(P);
  inputs(P p:Polynomial<"koala-bear">,P s:"koala-bear"::Element,
         P t:"koala-bear"::Element,P beta:"koala-bear"::Element,P n:index);
  local P: Concrete(p,s,t,beta,n);
  return ();
}
instance main_instance:Main {roles(P=P);} entry main=main_instance;
