# Monero Bulletproofs+ reference

This optional executable uses Monero v0.18.5.1 at
`4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5`: its prover, verifier, binary
serializer, point map and Keccak implementation. The source algorithm is
unchanged. A linker wrapper supplies the prover's private scalars `1,2,...`;
verification uses upstream randomness. This is a test facility only.

Build with CMake, a C/C++17 compiler, Boost headers, RapidJSON and libsodium.
Use one consistent toolchain for these dependencies. On Linux:

```sh
git clone https://github.com/monero-project/monero build/experiments/monero
git -C build/experiments/monero checkout 4f92268d7c16741cfb41e5bbe2aa46cc260a9ea5
cmake -S common/tests/reference/monero -B build/experiments/monero-reference \
  -DCMAKE_BUILD_TYPE=Release -DMONERO_SOURCE="$PWD/build/experiments/monero"
cmake --build build/experiments/monero-reference --parallel
python3 common/tests/reference/monero/reproduce.py \
  --source build/experiments/monero \
  --reference build/experiments/monero-reference/monero-reference \
  --output build/experiments/monero-fixtures
cmp build/experiments/monero-fixtures/corpus.json common/tests/fixtures/bulletproofs-plus/corpus.json
cmp build/experiments/monero-fixtures/edwards-map.json crates/zkc-backends/tests/fixtures/edwards-map.json
```

Set `CMAKE_PREFIX_PATH` and `PKG_CONFIG_PATH` when the dependencies are outside
standard paths. The wrapper relies on the Linux C++ symbol for `rct::skGen`;
do not enable interprocedural optimization. No build downloads dependencies. The same build also provides `monero-benchmark`,
which uses ordinary upstream randomness and the [benchmark worker](../../../benchmarks/README.md)
contract. Only `monero-reference` links the replay wrapper.
The reproduction script rejects modified or differently pinned upstream sources.

`monero-reference prove COUNT PREFIX PATTERN` produces the proof, original `V`
bytes and amounts. Counts are 1..16; patterns are `zero`, `max`, `mixed`, `random`
and `sequence`. Masks are `17,18,...`; random amounts use `mt19937_64(12345+COUNT)`.
`monero-reference verify PROOF COMMITMENTS` checks the complete serialized
object. It supplies the upstream amount-count guard before the verifier, and
requires EOF. `map` reads 32-byte hex inputs and emits the upstream legacy map
followed by multiplication by eight.

The [native source test](../../protocol/test_bulletproofs_plus.py) compiles the
`.zkc` project, replays the retained coins through a test-only service, compares
all 64 proof bytestrings, and verifies them with the ordinary Host. Existing
independent random-coin and consistently torsion-bearing upstream fixtures are
also verified. Mutation controls cover raw-byte binding, canonical scalars,
points, counts, framing, truncation and trailing bytes. These are finite
compatibility checks; they do not establish a security theorem.
