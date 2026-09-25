construction main {
  producer P;
  validator V;
  public "width" = (P width, V expected_width);
  public "height" = (V expected_height);
  random coins at (Draw draw, Select draw);
  accept 0;
  suite "merlin3.koala-bear.ext8-binomial3.rejection31le/1";
}
