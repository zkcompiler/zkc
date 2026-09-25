import assert from 'node:assert/strict';
import fs from 'node:fs';

import {getCurveFromName} from '../node_modules/snarkjs/src/curves.js';
import exportCalldata from '../node_modules/snarkjs/src/groth16_exportsoliditycalldata.js';
import groth16Verify from '../node_modules/snarkjs/src/groth16_verify.js';
import groth16Prove from '../reference/snarkjs-controlled/src/groth16_prove.js';

const [directory, rText, sText] = process.argv.slice(2);
const curve = await getCurveFromName('bn128');
for (const value of [rText, sText]) {
  assert.match(value || '', /^(0|[1-9][0-9]*)$/);
  assert(BigInt(value) < curve.r);
}
const t = performance.now();
const result = await groth16Prove(
    `${directory}/final.zkey`, `${directory}/witness.wtns`, undefined,
    {fixtureR: rText, fixtureS: sText});
const proveMs = performance.now() - t;
const vk = JSON.parse(fs.readFileSync(`${directory}/vk.json`));
assert.equal(await groth16Verify(vk, result.publicSignals, result.proof), true);
assert.deepEqual(result.publicSignals, JSON.parse(fs.readFileSync(`${directory}/public.json`)));
const tag = `r${rText}-s${sText}`;
fs.writeFileSync(`${directory}/proof-${tag}.json`, JSON.stringify(result.proof, null, 2) + '\n');
fs.writeFileSync(
    `${directory}/calldata-${tag}.txt`,
    await exportCalldata(result.proof, result.publicSignals) + '\n');
fs.writeFileSync(
    `${directory}/timing-${tag}.json`,
    JSON.stringify({r: rText, s: sText, proveMs, verified: true}, null, 2) + '\n');
console.log(JSON.stringify({directory, r: rText, s: sText, proveMs, verified: true}));
await curve.terminate();
