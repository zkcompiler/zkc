pragma circom 2.1.6;
template Mul() {
    signal input a;
    signal input b;
    signal output out;
    out <== a * b;
}
component main {public [a]} = Mul();
