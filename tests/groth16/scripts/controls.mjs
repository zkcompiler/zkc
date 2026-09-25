import assert from 'node:assert/strict';
import crypto from 'node:crypto';
import fs from 'node:fs';
import {createRequire} from 'node:module';

import {getCurveFromName} from '../node_modules/snarkjs/src/curves.js';
import prove from '../node_modules/snarkjs/src/groth16_prove.js';
import verify from '../node_modules/snarkjs/src/groth16_verify.js';
import check from '../node_modules/snarkjs/src/wtns_check.js';
import deterministicProve from '../reference/snarkjs-controlled/src/groth16_prove.js';

import {fold, mod, P} from './poseidon.mjs';

const directory = process.argv[2], depth = Number(directory.match(/depth(\d+)$/)[1]);
const require = createRequire(import.meta.url);
const buildCalculator = require(`../${directory}/depth${depth}_js/witness_calculator.js`);
const wc =
    await buildCalculator(fs.readFileSync(`${directory}/depth${depth}_js/depth${depth}.wasm`));
const curve = await getCurveFromName('bn128');
const source = JSON.parse(fs.readFileSync(`${directory}/input.json`));
const vk = JSON.parse(fs.readFileSync(`${directory}/vk.json`));
const pub = JSON.parse(fs.readFileSync(`${directory}/public.json`));
const proof = JSON.parse(fs.readFileSync(`${directory}/proof-r1-s2.json`));
const json = x => JSON.stringify(x, (_, v) => typeof v === 'bigint' ? v.toString() : v, 2) + '\n';
const results = [];
// snarkjs 0.7.5's failing-row branch dereferences logger.warn unconditionally.
const checkerLog = {
  info: () => {},
  debug: () => {},
  warn: message => console.log(message),
  error: message => console.log(message)
};
fs.mkdirSync(`${directory}/controls`, {recursive: true});
async function invalid(name, mutate) {
  const input = structuredClone(source);
  mutate(input);
  fs.writeFileSync(`${directory}/controls/input-${name}.json`, json(input));
  let error;
  try {
    await wc.calculateWTNSBin(input, true);
  } catch (e) {
    error = e.message;
  }
  assert(error, `Invalid ${name} unexpectedly generated a witness`);
  results.push({name, result: 'witness rejected', error});
}
for (const name of ['root', 'secret', 'blinding'])
  await invalid(name, input => input[name] = mod(BigInt(input[name]) + 1n).toString());
for (let i = 0; i < depth; i++) {
  await invalid(
      `sibling-${i}`, input => input.siblings[i] = mod(BigInt(input.siblings[i]) + 1n).toString());
  await invalid(
      `direction-flip-${i}`,
      input => input.directions[i] = (1n - BigInt(input.directions[i])).toString());
  await invalid(`nonboolean-${i}`, input => {
    input.directions[i] = '2';
    // Keep the entire algebraic hash path consistent, so rejection isolates
    // the boolean direction constraint rather than a stale root mismatch.
    input.root = fold(input).at(-1).toString();
  });
}
for (const [name, secret, blinding, direction] of [
         ['zero-inputs-left', 0n, 0n, '0'], ['boundary-inputs-right', P - 1n, P - 1n, '1']]) {
  const input = structuredClone(source);
  input.secret = secret.toString();
  input.blinding = blinding.toString();
  input.directions.fill(direction);
  input.root = fold(input).at(-1).toString();
  const path = `${directory}/controls/${name}.wtns`;
  fs.writeFileSync(`${directory}/controls/input-${name}.json`, json(input));
  fs.writeFileSync(path, Buffer.from(await wc.calculateWTNSBin(input, true)));
  assert.equal(await check(`${directory}/depth${depth}.r1cs`, path, checkerLog), true);
  results.push({name, result: 'valid witness checked'});
}
// Mutate a genuine witness on disk, bypassing the witness generator.
const tampered = fs.readFileSync(`${directory}/witness.wtns`);
let pos = 12, witnessOffset;
for (let i = 0; i < tampered.readUInt32LE(8); i++) {
  const id = tampered.readUInt32LE(pos), size = Number(tampered.readBigUInt64LE(pos + 4));
  pos += 12;
  if (id === 2)
    witnessOffset = pos;
  pos += size;
}
assert(witnessOffset);
let root = mod(BigInt(pub[0]) + 1n);
for (let i = 0; i < 32; i++, root >>= 8n)
  tampered[witnessOffset + 32 + i] = Number(root & 255n);
const badPath = `${directory}/controls/tampered-root.wtns`;
fs.writeFileSync(badPath, tampered);
assert.equal(await check(`${directory}/depth${depth}.r1cs`, badPath, checkerLog), false);
results.push({name: 'tampered-wtns-root', result: 'unmodified wtns checker rejected'});
const bad = await prove(`${directory}/final.zkey`, badPath);
fs.writeFileSync(`${directory}/controls/tampered-proof.json`, json(bad.proof));
fs.writeFileSync(`${directory}/controls/tampered-public.json`, json(bad.publicSignals));
assert.equal(await verify(vk, bad.publicSignals, bad.proof), false);
results.push(
    {name: 'tampered-wtns-proof', result: 'prover emitted proof; unmodified verifier rejected'});
for (const [name, inputs] of [
         ['changed-public-root', [mod(BigInt(pub[0]) + 1n).toString()]],
         ['noncanonical-public-root', [(BigInt(pub[0]) + P).toString()]]]) {
  assert.equal(await verify(vk, inputs, proof), false);
  results.push({name, result: 'unmodified verifier rejected'});
}
const negated = structuredClone(proof);
negated.pi_a[1] = (BigInt(curve.q) - BigInt(proof.pi_a[1])).toString();
assert.equal(await verify(vk, pub, negated), false);
results.push({name: 'negated-A-valid-curve-point', result: 'unmodified verifier rejected'});
const swapped = structuredClone(proof);
swapped.pi_b[0].reverse();
swapped.pi_b[1].reverse();
assert.equal(await verify(vk, pub, swapped), false);
results.push({name: 'G2-coefficients-swapped', result: 'unmodified verifier rejected'});
for (const [r, s] of [['1', '2'], ['0', '0']]) {
  const repeat = await deterministicProve(
      `${directory}/final.zkey`, `${directory}/witness.wtns`, undefined,
      {fixtureR: r, fixtureS: s});
  const saved = JSON.parse(fs.readFileSync(`${directory}/proof-r${r}-s${s}.json`));
  assert.deepEqual(repeat.proof, saved);
  assert.deepEqual(repeat.publicSignals, pub);
  results.push({name: `repeat-r${r}-s${s}`, result: 'exact canonical proof equality'});
}
const verifier = fs.readFileSync('node_modules/snarkjs/src/groth16_verify.js');
const integrity = JSON.parse(fs.readFileSync('reference/source-integrity.json'));
assert.equal(
    crypto.createHash('sha256').update(verifier).digest('hex'), integrity.unmodifiedVerifierSha256);
fs.writeFileSync(
    `${directory}/controls/results.json`,
    json({depth, passed: results.length, results, unmodifiedVerifier: true}));
console.log(json({depth, passed: results.length, unmodifiedVerifier: true}));
await curve.terminate();
