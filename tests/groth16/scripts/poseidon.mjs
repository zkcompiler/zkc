// Independent, unoptimized BigInt Poseidon permutation using pinned circomlib's
// original t=3 constants. The compiled circuit uses its optimized permutation.
import assert from 'node:assert/strict';
import fs from 'node:fs';

export const P = 21888242871839275222246405745257275088548364400416034343698204186575808495617n;
export const mod = x => ((x % P) + P) % P;
const source = fs.readFileSync(
    new URL('../vendor/circomlib/circuits/poseidon_constants_old.circom', import.meta.url), 'utf8');
function constants(name, count) {
  const body = source.split(`function ${name}(t)`)[1].split('function ')[0];
  const values = body.match(/if\s*\(t == 3\)\s*\{\s*return\s*(\[[\s\S]*?\]);/)[1]
                     .match(/0x[0-9a-fA-F]+|\d+/g)
                     .map(BigInt);
  assert.equal(values.length, count);
  return values;
}
export const C = constants('POSEIDON_C', 195);
export const M = constants('POSEIDON_M', 9);
export function poseidon(a, b) {
  let state = [0n, mod(BigInt(a)), mod(BigInt(b))];
  for (let round = 0; round < 65; round++) {
    state = state.map((x, i) => mod(x + C[round * 3 + i]));
    state = state.map((x, i) => (round < 4 || round >= 61 || i === 0) ? mod(x ** 5n) : x);
    state = [0, 1, 2].map(i => mod(state.reduce((sum, x, j) => sum + M[3 * i + j] * x, 0n)));
  }
  return state[0];
}
export function fold(input) {
  let node = poseidon(input.secret, input.blinding);
  const nodes = [node];
  for (let i = 0; i < input.siblings.length; i++) {
    const d = BigInt(input.directions[i]), s = BigInt(input.siblings[i]);
    // This algebraic form also permits a targeted non-boolean control.
    node = poseidon(mod(node + d * (s - node)), mod(s + d * (node - s)));
    nodes.push(node);
  }
  return nodes;
}
