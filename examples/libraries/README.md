# Reusable implementation libraries

The matching clients live in [`../projects`](../projects/README.md). Each root
has an exact source identity; aliases change lookup spelling, not declaration
identity. `views/layouts.pir` illustrates a conventional child module with a
public facade. Relation assets belong to their declaring source file.

`groth16/lib.pir` and `air/lib.pir` preserve the existing protocol arithmetic from
`examples/protocols/groth16.pir` and `examples/protocols/air-oracle/air-permutation.pir`.
Only the public implementation API is imported by the separately authored schedules.
`pcs` exposes ordinary KZG verification; its native preparation evidence remains
at the host seam documented by the integration tests.
