pragma circom 2.2.2;

include "../vendor/circomlib/circuits/poseidon.circom";

// Path is bottom-up. directions[i] = 0 puts the running node on the left;
// directions[i] = 1 puts it on the right. All hash inputs are Fr elements.
template MerkleMembership(depth) {
    signal input root;
    signal input secret;
    signal input blinding;
    signal input siblings[depth];
    signal input directions[depth];

    component leaf = Poseidon(2);
    leaf.inputs[0] <== secret;
    leaf.inputs[1] <== blinding;

    signal nodes[depth + 1];
    signal left[depth];
    signal right[depth];
    component hashes[depth];
    nodes[0] <== leaf.out;
    for (var i = 0; i < depth; i++) {
        directions[i] * (directions[i] - 1) === 0;
        left[i] <== nodes[i] + directions[i] * (siblings[i] - nodes[i]);
        right[i] <== siblings[i] + directions[i] * (nodes[i] - siblings[i]);
        hashes[i] = Poseidon(2);
        hashes[i].inputs[0] <== left[i];
        hashes[i].inputs[1] <== right[i];
        nodes[i + 1] <== hashes[i].out;
    }
    nodes[depth] === root;
}
