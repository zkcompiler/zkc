# Binary FRI

`LowDegree<Rows, LogSize, TerminalLog, Rounds, Queries>` authenticates antipodal
pairs on a two-adic coset, folds them with verifier challenges and checks the
terminal polynomial's degree and queried evaluations. It returns the verifier's
acceptance together with residual data for composition. The commitment scheme
and field capabilities remain explicit static parameters.

The prover commits each round before its challenge. Both siblings must be
authenticated at the same root and position; the next round is checked against
the fold equation. Query positions, natural order, coset shifts and the terminal
degree bound are part of that schedule. STARK's split commit/open schedule stays
owned by the STARK argument rather than being hidden behind a generic callback.

The [example](../../../../examples/projects/fri/README.md) generates a deterministic
32-point, degree-seven word and runs both interactive and proof Entries. Its
small parameters demonstrate the implementation. Tests independently evaluate
polynomials and reject changed commitments, openings, folds and terminal data;
they do not prove a proximity bound or Fiat–Shamir security theorem.
