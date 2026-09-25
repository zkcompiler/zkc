// Bind shapes, generator/key suite and application context in publicRoot.
// Only the verifier's coins become transcript challenges; prover entropy stays private.
construction main {
  producer P;
  validator V;
  public "g" = (P p_g, V g);
  public "h" = (P p_h, V h);
  public "base" = (P p_base, V base);
  public "blind" = (P p_blind, V blind);
  public "commitments" = (P p_commitments, V commitments);
  public "context" = (P p_context, V context);
  random coins at (DrawChallenge draw);
  accept 0;
  suite "merlin3.ristretto255.scalar64le/1";
}
