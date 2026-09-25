construction main {
  producer P;
  validator V;
  public "width" = (P width, V expected_width);
  public "height" = (V height);
  random coins at (DrawIndex draw);
  accept 0;
  suite "merlin3.koala-bear.ext8-binomial3.rejection31le/1";
}
