// The duplex framing rule held to vectors, C++ leg. The corpus
// (Inputs/duplex-framing-kat.json) was minted by the reference twin and
// covers the four framing sub-rules the paragraph in
// docs/spec/vocabularies.md §7 states: rate zeroing on a partial block,
// the length binding into the first capacity element, LIFO output
// order, and the IV's big-endian four-byte chunking with a short final
// chunk. The Rust leg confirms the same corpus in zkc-rt's tests; the
// twin re-derives it in oracle.parity's duplex-kat mode.
// RUN: zkc-test-opt -test-duplex-framing='kat=%S/Inputs/duplex-framing-kat.json' %s | FileCheck %s
// CHECK: duplex framing corpus: 6 cases agree, 1 distinct pair(s) separate

// The twin's own run, where uv exists: the corpus was minted on that
// leg, so this is its freshness guard rather than a second reading.
// RUN: %if uv %{ %uv python -m oracle.parity duplex-kat %S/Inputs/duplex-framing-kat.json | FileCheck %s --check-prefix=TWIN %}
// TWIN: duplex framing corpus: 6 cases agree, 1 distinct pair(s) separate

module {}
