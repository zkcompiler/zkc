// Apply the installed public-artifact construction to entry main.
// Public labels and the exact local draw site are part of the descriptor.
construction main {
  producer P;
  validator V;
  public "claim" = (V claim);
  public "expected_f" = (V expected_f);
  public "expected_g" = (V expected_g);
  random coins at (CheckRoundAndDraw draw);
  accept 0;
  suite "merlin3.bls12-381.fr64be/1";
}
