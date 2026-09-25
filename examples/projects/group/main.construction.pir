construction main {
  producer P;
  validator V;
  random coins at (group::BlsGroup.draw call_1);
  accept 0;
  suite "merlin3.bls12-381.fr64be/1";
}
