// Bind shapes, generator/key suite and application context in publicRoot.
// Only the verifier's coins become transcript challenges; prover entropy stays private.
construction main {
  producer P;
  validator V;
  public "a" = (P p_a, V a);
  public "b" = (P p_b, V b);
  public "c" = (P p_c, V c);
  public "initial" = (P p_initial, V initial);
  public "final" = (P p_final, V final);
  public "context" = (P p_context, V context);
  public "expected_root" = (V expected_root);
  random coins at (DrawChallenge draw);
  accept 0;
  suite "merlin3.bls12-381.fr64be/1";
}
