// Exercise the shipped Worker boundary with an injected SDK binding. Actual
// Wasm and browser agreement are covered separately by roundtrip.mjs.
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import test from 'node:test';
import vm from 'node:vm';

const binding = "import init, { ProofSession } from './pkg/zkc_web.js';";
const source = readFileSync(new URL('../../../crates/zkc-web/web/worker.js', import.meta.url), 'utf8');
assert.ok(source.includes(binding));

async function worker({ trap = false, failReply = false } = {}) {
  const state = { replies: [], closed: false, calls: 0 };
  class ProofSession {
    describe() { return '{}'; }
    prove() {
      state.calls++;
      if (trap) throw new WebAssembly.RuntimeError('injected trap');
      assert.fail('unexpected execution');
    }
  }
  const self = {
    postMessage(reply) {
      if (failReply && reply.error) throw new DOMException('injected reply failure', 'DataCloneError');
      state.replies.push(structuredClone(reply));
    },
    close() { state.closed = true; },
  };
  vm.runInNewContext(source.replace(binding, ''), {
    self, init: async () => {}, ProofSession, Uint8Array, WebAssembly, performance,
  });
  await self.onmessage({ data: { id: 1, operation: 'admit', package: new Uint8Array(), pin: new Uint8Array() } });
  return { state, send: data => self.onmessage({ data }) };
}

test('invalid envelopes and correlation IDs are refused before execution', async () => {
  const { state, send } = await worker();
  for (const data of [null, 12, 'message', []]) {
    await send(data);
    assert.equal(state.replies.at(-1).error, 'Error: web-message');
  }
  for (const id of [undefined, {}, [], Number.MAX_SAFE_INTEGER + 1]) {
    await send({ id, operation: 'prove', public: new Uint8Array(), witness: new Uint8Array() });
    const reply = state.replies.at(-1);
    assert.equal(reply.error, 'Error: web-message-id');
    assert.equal(reply.id, undefined);
    assert.equal(reply.fatal, false);
  }
  assert.equal(state.calls, 0);
  assert.equal(state.closed, false);
});

test('a trapped Worker closes even if reporting its failure throws', async () => {
  const { state, send } = await worker({ trap: true, failReply: true });
  await assert.rejects(send({ id: 'request', operation: 'prove', public: new Uint8Array(), witness: new Uint8Array() }), { name: 'DataCloneError' });
  assert.equal(state.calls, 1);
  assert.equal(state.closed, true);
});

test('queued continuations cannot reenter a trapped session', async () => {
  const { state, send } = await worker({ trap: true });
  const request = { id: 2, operation: 'prove', public: new Uint8Array(), witness: new Uint8Array() };
  await Promise.all([send(request), send({ ...request, id: 3 })]);
  assert.equal(state.calls, 1);
  assert.equal(state.closed, true);
  assert.equal(state.replies.at(-1).fatal, true);
});
