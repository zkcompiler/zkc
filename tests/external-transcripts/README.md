# External transcript fixtures

The scripts that rebuild two frozen inputs from the transcript corpus in
`tests/fixtures/external-transcript/` and the native primitives. Nothing runs them as
a test; each takes where it writes as an argument.

`make_replays.py` converts every archived transcript into an explicit
`external_replay` event schedule. BP+ schedules decode the bounded saved proof
containers and take the separately supplied V; OpenVM schedules replay the
recorded observe and sample log.

```sh
python3 tests/external-transcripts/make_replays.py build/reports/external-replays
```

`make_external_constructions.py` replays each schedule with the pinned native
`external_replay` example and records the exact hash and permutation
input/output pairs the Lean reference takes as trusted primitive replies. It
does not establish that the primitives are correct.

```sh
cargo build --release --locked -p zkc-backends --example external_replay
python3 tests/external-transcripts/make_external_constructions.py \
  --replay target/release/examples/external_replay \
  --output tests/fixtures/external-constructions.json
```
