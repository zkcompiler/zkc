pragma circom 2.2.2;
include "./merkle.circom";
component main {public [root]} = MerkleMembership(2);
