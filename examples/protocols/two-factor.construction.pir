// The public statement binds only the claimed sum in this earlier example.
construction main {
  producer P;
  validator V;
  public "claim" = (V claim);
  random coins at (CheckRoundAndDraw draw);
  accept 0;
  suite "merlin3.bls12-381.fr64be/1";
}
