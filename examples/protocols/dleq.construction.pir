// Both parties bind the same bases; the validator also binds both images.
// Repeated calls to the allowed draw site retain distinct invocation origins.
construction main {
  producer P;
  validator V;
  public "base_0" = (P p_base_0, V base_0);
  public "base_1" = (P p_base_1, V base_1);
  public "image_0" = (V image_0);
  public "image_1" = (V image_1);
  random coins at (DLEQDraw draw);
  accept 0;
  suite "merlin3.bls12-381.fr64be/1";
}
