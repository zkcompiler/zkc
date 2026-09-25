// The statement, context, and each first message precede its challenge.
construction main {
  producer P;
  validator V;
  public "G" = (P p_bases, V bases);
  public "A" = (P p_matrix, V matrix);
  public "b" = (V b);
  public "C" = (V commitment);
  public "context" = (V context);
  random coins at (LinearChallenge draw);
  accept 0;
  suite "merlin3.bls12-381.fr64be/1";
}
