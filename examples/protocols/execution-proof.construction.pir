// All matrices and public coordinates are verifier-owned and transcript-bound.
construction main {
  producer P;
  validator V;
  public "cpu_a" = (P p_cpu_a, V cpu_a);
  public "cpu_b" = (P p_cpu_b, V cpu_b);
  public "cpu_c" = (P p_cpu_c, V cpu_c);
  public "memory_a" = (P p_memory_a, V memory_a);
  public "memory_b" = (P p_memory_b, V memory_b);
  public "memory_c" = (P p_memory_c, V memory_c);
  public "link_a" = (P p_link_a, V link_a);
  public "link_b" = (P p_link_b, V link_b);
  public "link_c" = (P p_link_c, V link_c);
  public "statement" = (P p_statement, V statement);
  public "context" = (P p_context, V context);
  random coins at (DrawChallenge draw);
  accept 0;
  suite "merlin3.bls12-381.fr64be/1";
}
