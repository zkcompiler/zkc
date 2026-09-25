construction main {
  producer P;
  validator V;
  public "initial" = (P p_initial, V v_initial);
  public "final_value" = (P p_final_value, V v_final_value);
  public "total" = (P p_total, V v_total);
  random coins at (Draw draw, Query draw);
  accept 0;
  suite "merlin3.koala-bear.ext8-binomial3.rejection31le/1";
}
