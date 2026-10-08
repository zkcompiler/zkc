# Protocol libraries

[Schnorr](schnorr/lib.zkc) and [Sumcheck](sumcheck/lib.zkc) define generic
protocols in `.zkc`. Libraries own the mathematical algorithm and exchange;
[client projects](../projects/README.md) choose concrete domains and Entries.
Explicit module maps resolve imports. Both libraries execute through the same
compiler and Host.
