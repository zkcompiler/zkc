# Entry functions and proofs

A `protocol` describes participant computation and interaction. A `proof`
declaration chooses a closed proof construction. An `entry fn` is an application
entry point: it prepares data, calls protocols or proofs, and returns a value.
The [declaration contract](../spec/language/entries.md) defines the exact checks.

## Application control

Entry functions use ordinary typed arguments and Local expressions. They may
call numerical helpers and other Entry functions. A result annotation is optional
when the compiler can infer it from the body.

```zkc
fn increment(value: index) -> index { return value + 1; }

entry fn Next(value: index) {
  return increment(value);
}

entry fn Twice(value: index) {
  let next = Next(value);
  return Next(next);
}
```

`zkc run Twice` executes this function. Its argument file contains
`{"value":"7"}`; its source result is `"9"`. An Entry function needs no protocol
wrapper for an ordinary calculation. Its numerical work uses the same Kernel
lowering and VM as participant computation.

A protocol specialization exposes generated `Inputs`, `RunResult` and `run`:

```zkc
entry fn Interactive(inputs: Schnorr<G>::Inputs) {
  return Schnorr<G>::run(inputs);
}
```

`Inputs` is a record keyed by participant, with ordinary data ports in each
participant's record. A shared port has a separate supplied value for each role;
this does not assert that independently supplied copies agree. Services, setup
keys and limits are supplied by the Host context, separately from ordinary data.
A completed run can return a verifier Boolean of `false` as ordinary data.

## Proof operations

The declarative proof configuration remains separate:

```zkc
proof Core = Schnorr<G> {
  prover P;
  verifier V;
  public { base, point };
  accept accepted;
  construction fiat_shamir("merlin3.bls12-381.fr64be/0", challenges);
}

entry fn Produce(public: Core::Public, witness: Core::Witness) {
  let result = Core::prove(public = public, witness = witness);
  return result.proof;
}

entry fn Validate(public: Core::Public, candidate: Core::Proof) {
  return Core::verify(public = public, proof = candidate);
}
```

`Core::Public` and `Core::Witness` name generated records for public and
producer-private data. `Core::Proof` contains exact candidate bytes; its type
does not establish validity. `prove` returns a `ProveResult` containing the
candidate and producer outputs. `verify` returns `VerifyResult::Accepted` with
verifier outputs, or `VerifyResult::Rejected` without outputs. Framing, runtime,
resource and cleanup failures remain execution failures.

A trace- or witness-generating Entry calls an ordinary helper or another Entry,
then calls `Core::prove` with the generated witness. This does not change `Core`:
independent applications may still call `zkc prove Core` and `zkc verify Core`
with explicit inputs. Only values explicitly returned by a successful Entry are
published. A failure after a proof call does not publish that intermediate proof.

## External calls

`zkc inspect` shows checked signatures and generated API types; `zkc prepare`
creates named argument templates. The compiler publishes source correspondence,
interface, compilation choices and the executable artifact in an
[Entry package](../spec/formats/entry.md). Applications authenticate the package
before executing its common Host.

See [running Entries](../runtime/entries.md) for CLI use, Rust bindings and the
Python adapter. Entry execution does not establish a protocol security theorem.
