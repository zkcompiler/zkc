// Archived typed-metadata adapter schema: tests/support/shape_data.py.
// VK/config is caller-selected trusted metadata, separate from received proof.
// Selected slots = batch sumcheck rounds + GKR layers; this body is a schedule
// skeleton, not SWIRL arithmetic/verification. See tests/fixtures/archived-shapes/README.md.
module {
  use zkc::algebra::{Indices};
  use zkc::algebra;
  use zkc::core;
  fn Eq(a: index, b: index) -> index {
    zkc::core::require(zkc::algebra::index_equal(a, b));
    return a;
  }
  fn AtMost(a: index, b: index) -> index {
    zkc::core::require(zkc::algebra::index_less(a, b + 1));
    return a;
  }
  fn Power(exponent: index) -> index {
    let checked = AtMost(exponent, 20);
    let mut result = 1;
    for i in 0..checked { result = result * 2; }
    return result;
  }
  fn Select(key: Indices, proof: Indices) -> index {
    zkc::core::require(zkc::algebra::index_less(3, key.len()));
    zkc::core::require(zkc::algebra::index_less(8, proof.len()));
    let skip = AtMost(key[0], 16);
    let stack = AtMost(key[1], 20);
    let maxHeight = AtMost(skip + stack, 20);
    let degree = AtMost(key[2], 16);
    let airs = AtMost(key[3], 32);
    zkc::core::require(zkc::algebra::index_less(0, airs));
    let keyBase = 4 + airs * 10;
    zkc::core::require(zkc::algebra::index_less(keyBase, key.len() + 1));
    let traceCount = Eq(proof[0], airs);
    let pvCount = Eq(proof[1], airs);
    let proofBase = 9 + airs * 4;
    zkc::core::require(zkc::algebra::index_less(proofBase, proof.len() + 1));
    let mut keyEnd = keyBase;
    let mut present = 0;
    let mut highest = 0;
    let mut interactions = 0;
    for air in 0..airs {
      let k = 4 + air * 10;
      let p = 9 + air * 4;
      let required = AtMost(key[k], 1);
      let expectedPV = AtMost(key[k + 1], 4096);
      let rotated = AtMost(key[k + 2], 1);
      let multiplicity = AtMost(key[k + 3], 1024);
      let prepared = AtMost(key[k + 4], 1);
      let preparedHeight = AtMost(key[k + 5], maxHeight);
      let commonWidth = AtMost(key[k + 6], 4096);
      let preparedWidth = AtMost(key[k + 7], 4096);
      let cached = AtMost(key[k + 8], 16);
      let widthOffset = Eq(key[k + 9], keyEnd);
      keyEnd = keyEnd + cached;
      zkc::core::require(zkc::algebra::index_less(keyEnd, key.len() + 1));
      for c in 0..cached { let width = AtMost(key[widthOffset + c], 4096); }
      if zkc::algebra::index_equal(prepared, 0) {
        let emptyHeight = Eq(preparedHeight, 0);
        let emptyWidth = Eq(preparedWidth, 0);
      }
      let exists = AtMost(proof[p], 1);
      let height = AtMost(proof[p + 1], maxHeight);
      if zkc::algebra::index_equal(exists, 0) {
        let optional = Eq(required, 0);
        let noHeight = Eq(height, 0);
        let noCached = Eq(proof[p + 2], 0);
        let noPV = Eq(proof[p + 3], 0);
      } else {
        let cachedOK = Eq(proof[p + 2], cached);
        let pvOK = Eq(proof[p + 3], expectedPV);
        if zkc::algebra::index_equal(prepared, 1) { let prepOK = Eq(height, preparedHeight); }
        present = present + 1;
        if zkc::algebra::index_less(highest, height) { highest = height; }
        let mut paddedHeight = height;
        if zkc::algebra::index_less(height, skip) { paddedHeight = skip; }
        interactions = interactions + multiplicity * Power(paddedHeight);
      }
    }
    let keyExact = Eq(keyEnd, key.len());
    zkc::core::require(zkc::algebra::index_less(0, present));
    let numeratorOK = Eq(proof[2], present);
    let denominatorOK = Eq(proof[3], present);
    let univariateOK = Eq(proof[4], (degree + 1) * (Power(skip) - 1) + 1);
    let openingCount = Eq(proof[5], present);
    let mut batchRounds = 0;
    if zkc::algebra::index_less(skip, highest) { batchRounds = highest - skip; }
    let batchOK = Eq(proof[6], batchRounds);
    // bit_length(total), including the extra layer for a power of two.
    let mut remaining = interactions;
    let mut gkrLayers = 0;
    for bit in 0..40 {
      if zkc::algebra::index_less(0, remaining) {
        gkrLayers = gkrLayers + 1;
        remaining = zkc::algebra::index_div(remaining, 2);
      }
    }
    let exhausted = Eq(remaining, 0);
    let gkrOK = Eq(proof[7], gkrLayers);
    let mut gkrOuter = 0;
    if zkc::algebra::index_less(0, gkrLayers) { gkrOuter = gkrLayers - 1; }
    let gkrOuterOK = Eq(proof[8], gkrOuter);
    let mut cursor = proofBase;
    let mut previousHeight = maxHeight;
    let mut previousAir = 0;
    for slot in 0..openingCount {
      zkc::core::require(zkc::algebra::index_less(cursor + 1, proof.len()));
      let air = proof[cursor];
      zkc::core::require(zkc::algebra::index_less(air, airs));
      let k = 4 + air * 10;
      let p = 9 + air * 4;
      let active = Eq(proof[p], 1);
      let height = proof[p + 1];
      let descending = AtMost(height, previousHeight);
      if zkc::algebra::index_less(0, slot) {
        if zkc::algebra::index_equal(height, previousHeight) {
          zkc::core::require(zkc::algebra::index_less(previousAir, air));
        }
      }
      previousHeight = height;
      previousAir = air;
      let prepared = key[k + 4];
      let cached = key[k + 8];
      let parts = Eq(proof[cursor + 1], 1 + prepared + cached);
      let widths = cursor + 2;
      cursor = widths + parts;
      zkc::core::require(zkc::algebra::index_less(cursor, proof.len() + 1));
      let rotation = 1 + key[k + 2];
      let mainOK = Eq(proof[widths], key[k + 6] * rotation);
      if zkc::algebra::index_equal(prepared, 1) {
        let preparedOK = Eq(proof[widths + 1], key[k + 7] * rotation);
      }
      for c in 0..cached {
        let cacheOK = Eq(proof[widths + 1 + prepared + c], key[key[k + 9] + c] * rotation);
      }
    }
    let end = Eq(cursor + batchRounds + gkrOuter, proof.len());
    for r in 0..batchRounds { let widthOK = Eq(proof[cursor + r], degree + 1); }
    for r in 0..gkrOuter { let widthOK = Eq(proof[cursor + batchRounds + r], r + 1); }
    return batchRounds + gkrLayers;
  }
  fn Zero() -> index { return 0; }
  fn Step(value: index) -> index { return value + 1; }
  protocol Family {
    roles (P, V);
    parameters (rounds);
    inputs (P key: Indices, P proof: Indices, V receivedKey: Indices, V receivedProof: Indices);
    outputs (P index, V index);
    local [startP] P: let p = Zero();
    local [startV] V: let v = Zero();
    loop [round] rounds carry (a = p, b = v) -> (x, y) {
      local [step] P: let next = Step(a);
      message [roundMessage] index: P(next) -> V(got);
      yield (next, got);
    }
    return (x, y);
  }
  instance Main: Family {
    parameters (rounds = ingress(64, P = Select(key, proof), V = Select(receivedKey, receivedProof)));
    roles (P = P, V = V);
  }
  entry main = Main;
}
