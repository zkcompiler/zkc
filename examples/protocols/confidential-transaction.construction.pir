construction main {
  producer P;
  validator V;
  public "g" = (P p_g, V g);
  public "h" = (P p_h, V h);
  public "base" = (P p_base, V base);
  public "blind" = (P p_blind, V blind);
  public "commitments" = (P p_commitments, V commitments);
  public "context" = (P p_context, V context);
  public "input_commitments" = (P p_input_commitments, V input_commitments);
  public "owners" = (P p_owners, V owners);
  public "input_ids" = (P p_input_ids, V input_ids);
  public "fee" = (P p_fee, V fee);
  random coins at (DrawChallenge draw);
  accept 0;
  suite "merlin3.ristretto255.scalar64le/1";
}
