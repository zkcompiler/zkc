pragma circom 2.1.6;
include "circomlib/circuits/bitify.circom";
include "circomlib/circuits/comparators.circom";
// Bounded balance transfer: private balance and transfer amount; public fee.
// This arithmetic/range relation is valid over either selected large prime.
template Transfer() {
    signal input balance;
    signal input amount;
    signal input fee;
    signal output remaining;
    component br = Num2Bits(32);
    component ar = Num2Bits(32);
    component fr = Num2Bits(16);
    component rr = Num2Bits(32);
    component canSpend = LessEqThan(33);
    br.in <== balance;
    ar.in <== amount;
    fr.in <== fee;
    remaining <== balance - amount - fee;
    rr.in <== remaining;
    canSpend.in[0] <== amount + fee;
    canSpend.in[1] <== balance;
    canSpend.out === 1;
}
component main {public [fee]} = Transfer();
