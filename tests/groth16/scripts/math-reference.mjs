// Independent canonical-BigInt QAP/FFT and binary reader. Group primitives and
// beacon decoding use ffjavascript/snarkjs; no Groth16 prover is called here.
import Blake2b from 'blake2b-wasm';
import {buildBn128} from 'ffjavascript';
import assert from 'node:assert/strict';
import crypto from 'node:crypto';
import fs from 'node:fs';

import {rngFromBeaconParams} from '../node_modules/snarkjs/src/misc.js';
import {calculateFirstChallengeHash, keyFromBeacon} from '../node_modules/snarkjs/src/powersoftau_utils.js';

import {mod, P} from './poseidon.mjs';

const directory = process.argv[2];
const start = performance.now();
const curve = await buildBn128();
const {Fr, G1, G2} = curve;
const Q = BigInt(curve.q);
function pow(base, exponent, modulus = P) {
  let result = 1n;
  base = ((base % modulus) + modulus) % modulus;
  while (exponent > 0n) {
    if (exponent & 1n) {
      result = result * base % modulus;
    }
    base = base * base % modulus;
    exponent >>= 1n;
  }
  return result;
}
const inv = (x, p = P) => {
  assert.notEqual(x % p, 0n);
  return pow(x, p - 2n, p);
};
const readLE = bytes => {
  let value = 0n;
  for (let i = bytes.length - 1; i >= 0; i--) {
    value = (value << 8n) + BigInt(bytes[i]);
  }
  return value;
};
function scalarBytes(values) {
  const bytes = Buffer.alloc(values.length * 32);
  values.forEach((value, index) => {
    assert(value >= 0n && value < P);
    for (let limb = 0; limb < 32; limb++) {
      bytes[index * 32 + limb] = Number(value & 255n);
      value >>= 8n;
    }
  });
  return bytes;
}
const json = x => JSON.stringify(x, (_, v) => typeof v === 'bigint' ? v.toString() : v, 2) + '\n';
const object = (G, p) => G.toObject(G.toAffine(p));
function sections(path, magic) {
  const b = fs.readFileSync(path);
  assert.equal(b.subarray(0, 4).toString(), magic);
  let pos = 12;
  const result = {}, layout = [];
  for (let i = 0; i < b.readUInt32LE(8); i++) {
    const id = b.readUInt32LE(pos), size = Number(b.readBigUInt64LE(pos + 4));
    pos += 12;
    assert(!result[id]);
    result[id] = b.subarray(pos, pos + size);
    layout.push({id, offset: pos, size});
    pos += size;
  }
  assert.equal(pos, b.length);
  return {result, layout, version: b.readUInt32LE(4)};
}
const zfile = sections(`${directory}/final.zkey`, 'zkey'), z = zfile.result;
let offset = 0;
const u32 = () => {
  const x = z[2].readUInt32LE(offset);
  offset += 4;
  return x;
};
const field = () => {
  const n = u32(), x = readLE(z[2].subarray(offset, offset + n));
  offset += n;
  assert.equal(n, 32);
  return x;
};
assert.equal(field(), Q);
assert.equal(field(), P);
const nVars = u32(), nPublic = u32(), N = u32();
assert.equal(nPublic, 1);
const R = pow(2n, 256n), R2 = R * R % P, R2inv = inv(R2), Rq = pow(2n, 256n, Q), RqInv = inv(Rq, Q);
function point(b, group) {
  const limbs = Array.from(
      {length: group === 'G1' ? 2 : 4},
      (_, i) => readLE(b.subarray(i * 32, (i + 1) * 32)) * RqInv % Q);
  if (limbs.every(x => x === 0n))
    return group === 'G1' ? [0n, 1n, 0n] : [[0n, 0n], [1n, 0n], [0n, 0n]];
  return group === 'G1' ? [...limbs, 1n] : [[limbs[0], limbs[1]], [limbs[2], limbs[3]], [1n, 0n]];
}
const header = {};
for (const [name, group] of [
         ['alpha1', 'G1'], ['beta1', 'G1'], ['beta2', 'G2'], ['gamma2', 'G2'], ['delta1', 'G1'],
         ['delta2', 'G2']]) {
  const bytes = group === 'G1' ? 64 : 128;
  header[name] = point(z[2].subarray(offset, offset + bytes), group);
  offset += bytes;
}
assert.equal(offset, z[2].length);
const wf = sections(`${directory}/witness.wtns`, 'wtns');
assert.equal(readLE(wf.result[1].subarray(4, 36)), P);
const w =
    Array.from({length: nVars}, (_, i) => readLE(wf.result[2].subarray(i * 32, (i + 1) * 32)));
assert.equal(wf.result[1].readUInt32LE(36), nVars);
assert.equal(w[0], 1n);
w.forEach(x => assert(x < P));
const r1cs = JSON.parse(fs.readFileSync(`${directory}/r1cs.json`));
const rows = r1cs.nConstraints;
assert.equal(r1cs.nVars, nVars);
assert.equal(N, 2 ** Math.ceil(Math.log2(rows + nPublic + 1)));
const A = Array(N).fill(0n), B = Array(N).fill(0n),
      privateRows = [0, 1, 2].map(() => Array(N).fill(0n));
const recordCount = z[4].readUInt32LE(0), records = [];
assert.equal(z[4].length, 4 + 44 * recordCount);
for (let i = 0; i < recordCount; i++) {
  const p = 4 + 44 * i, m = z[4].readUInt32LE(p), row = z[4].readUInt32LE(p + 4),
        wire = z[4].readUInt32LE(p + 8);
  const raw = readLE(z[4].subarray(p + 12, p + 44)), coef = raw * R2inv % P;
  assert(m === 0 || m === 1);
  assert(row < N && wire < nVars);
  assert(raw < P);
  const out = m === 0 ? A : B;
  out[row] = mod(out[row] + coef * w[wire]);
  if (i < 8 || row >= rows)
    records.push({index: i, matrix: m, row, wire, rawR2: raw, coefficient: coef});
}
for (let row = 0; row < rows; row++) {
  const actual = r1cs.constraints[row].map((terms, m) => {
    let total = 0n;
    for (const [wireText, coefText] of Object.entries(terms)) {
      const wire = Number(wireText), v = BigInt(coefText) * w[wire];
      total = mod(total + v);
      if (wire > nPublic)
        privateRows[m][row] = mod(privateRows[m][row] + v);
    }
    return total;
  });
  assert.equal(actual[0], A[row]);
  assert.equal(actual[1], B[row]);
  assert.equal(A[row] * B[row] % P, actual[2]);
}
for (let i = 0; i <= nPublic; i++) {
  assert.equal(A[rows + i], w[i]);
  assert.equal(B[rows + i], 0n);
}
for (let row = rows + nPublic + 1; row < N; row++) {
  assert.equal(A[row], 0n);
  assert.equal(B[row], 0n);
}
const C = A.map((a, i) => a * B[i] % P);
let nqr = 2n;
while (pow(nqr, (P - 1n) / 2n) !== P - 1n)
  nqr++;
const omega = pow(nqr, (P - 1n) / BigInt(N)), inc = pow(nqr, (P - 1n) / BigInt(2 * N));
assert.equal(Fr.toObject(Fr.w[Math.log2(N)]), omega);
assert.equal(Fr.toObject(Fr.w[Math.log2(N) + 1]), inc);
assert.equal(inc * inc % P, omega);
assert.equal(pow(inc, BigInt(N)), P - 1n);
function fft(input, inverse = false) {
  const a = input.slice(), n = a.length;
  assert.equal(n, N);
  for (let i = 1, j = 0; i < n; i++) {
    let bit = n >> 1;
    for (; j & bit; bit >>= 1)
      j ^= bit;
    j ^= bit;
    if (i < j)
      [a[i], a[j]] = [a[j], a[i]];
  }
  const root = inverse ? inv(omega) : omega;
  for (let len = 2; len <= n; len *= 2) {
    const step = pow(root, BigInt(n / len));
    for (let i = 0; i < n; i += len) {
      let z = 1n;
      for (let j = 0; j < len / 2; j++) {
        const u = a[i + j], v = a[i + j + len / 2] * z % P;
        a[i + j] = mod(u + v);
        a[i + j + len / 2] = mod(u - v);
        z = z * step % P;
      }
    }
  }
  const normalization = inverse ? inv(BigInt(n)) : 1n;
  return inverse ? a.map(x => x * normalization % P) : a;
}
function shift(a, factor) {
  let z = 1n;
  return a.map(x => {
    const out = x * z % P;
    z = z * factor % P;
    return out;
  });
}
const [a, b, c] = [A, B, C].map(x => fft(x, true));
const [ao, bo, co] = [a, b, c].map(x => fft(shift(x, inc)));
const numerator = ao.map((x, i) => mod(x * bo[i] - co[i]));
const cosetDenominatorInv = inv(P - 2n);
const hCoset = numerator.map(x => x * cosetDenominatorInv % P);
const h = shift(fft(hCoset, true), inv(inc));
assert.equal(h[N - 1], 0n);
// Exhaustive independent BigInt-versus-WASM FFT comparisons for A, B and C.
for (const [input, coeff, odd] of [[A, a, ao], [B, b, bo], [C, c, co]]) {
  const im = await Fr.batchToMontgomery(scalarBytes(input));
  const coeffWasm = await Fr.ifft(im);
  assert.deepEqual(Buffer.from(await Fr.batchFromMontgomery(coeffWasm)), scalarBytes(coeff));
  const oddWasm = await Fr.fft(await Fr.batchApplyKey(coeffWasm, Fr.e(1), Fr.e(inc)));
  assert.deepEqual(Buffer.from(await Fr.batchFromMontgomery(oddWasm)), scalarBytes(odd));
}
const msm = {};
for (const [name, section, group, scalars] of [
         ['A', 5, G1, w], ['B1', 6, G1, w], ['B2', 7, G2, w], ['L', 8, G1, w.slice(nPublic + 1)],
         ['H', 9, G1, numerator]]) {
  assert.equal(z[section].length, scalars.length * group.F.n8 * 2);
  msm[name] = await group.multiExpAffine(z[section], scalarBytes(scalars));
}

// Reconstruct PUBLIC TEST setup scalars to check each MSM independently by
// evaluating the canonical polynomials at tau and multiplying the generators.
await Blake2b.ready();
const beacon =
    Buffer.from('7e571e577e571e577e571e577e571e577e571e577e571e577e571e577e571e57', 'hex');
const key = await keyFromBeacon(curve, calculateFirstChallengeHash(curve, 13), beacon, 10);
const tau = Fr.toObject(key.tau.prvKey), alpha = Fr.toObject(key.alpha.prvKey),
      beta = Fr.toObject(key.beta.prvKey);
const zkeyBeacon =
    Buffer.from('814748cce1c82c2a499397fc30c8578e495edc6b6dc906bd64e3d077fd24352e', 'hex');
const delta = Fr.toObject(Fr.fromRng(await rngFromBeaconParams(zkeyBeacon, 10)));
assert.notEqual(delta, tau);
const evaluate = (poly, x) => poly.reduceRight((out, y) => mod(out * x + y), 0n);
const at = evaluate(a, tau), bt = evaluate(b, tau), ct = evaluate(c, tau),
      zt = mod(pow(tau, BigInt(N)) - 1n);
const privateAtTau = privateRows.map(x => evaluate(fft(x, true), tau));
const lScalar =
    mod((beta * privateAtTau[0] + alpha * privateAtTau[1] + privateAtTau[2]) * inv(delta));
const hScalar = mod((at * bt - ct) * inv(delta));
assert.equal(evaluate(h, tau) * zt % P, mod(at * bt - ct));
for (const [name, group, scalar] of [
         ['A', G1, at], ['B1', G1, bt], ['B2', G2, bt], ['L', G1, lScalar], ['H', G1, hScalar]])
  assert(
      group.eq(msm[name], group.timesScalar(group.g, scalar)),
      `independent MSM scalar check ${name}`);
for (const [name, group, scalar] of [
         ['alpha1', G1, alpha], ['beta1', G1, beta], ['beta2', G2, beta], ['gamma2', G2, 1n],
         ['delta1', G1, delta], ['delta2', G2, delta]])
  assert.deepEqual(object(group, group.timesScalar(group.g, scalar)), header[name]);

const hSamples = [];
for (const j of [0, 1, 2, N - 1]) {
  const x = pow(inc, BigInt(2 * j + 1)), ratio = tau * inv(x) % P;
  let value = mod((pow(ratio, BigInt(2 * N)) - 1n) * inv(mod(ratio - 1n)));
  // Phase-1 highest degree is 2**14-2. At its maximal circuit domain,
  // preparePhase2 inserts the identity in place of tau**(2*N-1).
  if (N === 8192)
    value = mod(value - pow(ratio, BigInt(2 * N - 1)));
  value = mod(value * inv(BigInt(2 * N)) * inv(delta));
  const actual = point(z[9].subarray(j * 64, (j + 1) * 64), 'G1');
  assert.deepEqual(object(G1, G1.timesScalar(G1.g, value)), actual);
  hSamples.push({
    index: j,
    cosetPoint: x,
    basisScalar: value,
    point: actual,
    highestTauPowerPadded: N === 8192
  });
}
const proofScalars = {};
for (const [r, s] of [[1n, 2n], [0n, 0n]]) {
  const ap = mod(alpha + at + r * delta), bp = mod(beta + bt + s * delta);
  const cp = mod(lScalar + hScalar + s * ap + r * bp - r * s * delta);
  const expected = {
    pi_a: object(G1, G1.timesScalar(G1.g, ap)),
    pi_b: object(G2, G2.timesScalar(G2.g, bp)),
    pi_c: object(G1, G1.timesScalar(G1.g, cp)),
    protocol: 'groth16',
    curve: 'bn128'
  };
  const actual = JSON.parse(fs.readFileSync(`${directory}/proof-r${r}-s${s}.json`));
  assert.deepEqual(JSON.parse(json(expected)), actual, `exact canonical proof r=${r} s=${s}`);
  fs.writeFileSync(`${directory}/math-proof-r${r}-s${s}.json`, json(expected));
  proofScalars[`r${r}-s${s}`] = {r, s, A: ap, B: bp, C: cp};
}
fs.mkdirSync(`${directory}/vectors`, {recursive: true});
const vectorSummary = {};
for (const [name, values] of Object.entries({
       witness: w,
       A_evaluations: A,
       B_evaluations: B,
       C_evaluations: C,
       A_coefficients: a,
       B_coefficients: b,
       C_coefficients: c,
       A_coset: ao,
       B_coset: bo,
       C_coset: co,
       P_coset: numerator,
       H_coset: hCoset,
       H_coefficients: h
     })) {
  const bytes = scalarBytes(values), path = `vectors/${name}.frle`;
  fs.writeFileSync(`${directory}/${path}`, bytes);
  vectorSummary[name] = {
    path,
    length: values.length,
    encoding: 'canonical Fr, 32-byte little-endian, no header',
    sha256: crypto.createHash('sha256').update(bytes).digest('hex'),
    first8: values.slice(0, 8),
    last2: values.slice(-2)
  };
}
const summary = {
  nVars,
  nPublic,
  nConstraints: rows,
  domainSize: N,
  zkeyVersion: zfile.version,
  zkeySections: zfile.layout,
  scalarField: P,
  baseField: Q,
  R_scalar: R,
  R2_scalar: R2,
  R_base: Rq,
  nqr,
  omega,
  inc,
  cosetVanishing: P - 2n,
  publicRows: [0, 1].map(i => ({row: rows + i, A: A[rows + i], B: B[rows + i], C: C[rows + i]})),
  coefficients: records,
  header,
  msm: Object.fromEntries(
      Object.entries(msm).map(([name, p]) => [name, object(name === 'B2' ? G2 : G1, p)])),
  hSamples,
  publicTestTrapdoors: {
    warning: 'PUBLIC DETERMINISTIC TEST SETUP ONLY; no secrecy or security',
    tau,
    alpha,
    beta,
    gamma: 1n,
    delta
  },
  polynomialValues: {
    A_tau: at,
    B_tau: bt,
    C_tau: ct,
    Z_tau: zt,
    H_tau: evaluate(h, tau),
    privateAtTau,
    L_scalar: lScalar,
    H_MSM_scalar: hScalar
  },
  proofScalars,
  vectors: vectorSummary,
  checks: {
    allR1CSRows: true,
    allQAPRows: true,
    allFFTValues: true,
    allMSMResults: true,
    sampledHQueries: true,
    exactProofs: 2
  },
  elapsedMs: performance.now() - start
};
fs.writeFileSync(`${directory}/intermediates.json`, json(summary));
console.log(json({directory, domainSize: N, checks: summary.checks, elapsedMs: summary.elapsedMs}));
await curve.terminate();
