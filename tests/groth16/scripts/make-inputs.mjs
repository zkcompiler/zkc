import fs from 'node:fs';

import {C, fold, M, P, poseidon} from './poseidon.mjs';

const json = x => JSON.stringify(x, (_, v) => typeof v === 'bigint' ? v.toString() : v, 2) + '\n';
fs.writeFileSync('reference/poseidon-t3.json', json({
                   prime: P,
                   width: 3,
                   fullRounds: 8,
                   partialRounds: 57,
                   exponent: 5,
                   C,
                   M,
                   matrixOrder: 'row-major',
                   initialState: 0
                 }));
for (const depth of [2, 16]) {
  let empty = poseidon(0n, 0n);
  const siblings = [], directions = [];
  const index = depth === 2 ? 1 : 0xa53d;
  for (let i = 0; i < depth; i++) {
    siblings.push(empty);
    directions.push(BigInt((index >> i) & 1));
    empty = poseidon(empty, empty);
  }
  const input = {secret: 123456789n, blinding: 987654321n, siblings, directions};
  const nodes = fold(input);
  input.root = nodes.at(-1);
  const out = `artifacts/depth${depth}`;
  fs.writeFileSync(`${out}/input.json`, json(input));
  fs.writeFileSync(`${out}/hash-vectors.json`, json({
                     depth,
                     index,
                     description: 'One populated leaf; all other leaves are Poseidon(0,0)',
                     emptyLeaf: poseidon(0n, 0n),
                     emptyTreeRoot: empty,
                     nodes,
                     poseidon12: poseidon(1n, 2n)
                   }));
  console.log(`depth=${depth} index=${index} root=${input.root}`);
}
