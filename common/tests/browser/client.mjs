import assert from 'node:assert/strict';
import test from 'node:test';
import { ProofClient, ProofClientError } from '../../../crates/zkc-web/web/client.mjs';
import { FakeWorker, admission, proving, turn, admissionTimings, reportTimings } from './fake-worker.mjs';

async function client(config = {}, options = {}) {
  const workers = [];
  const api = new ProofClient({ timeoutMs: 1000, ...options, workerFactory: () => {
    const fake = new FakeWorker(config);
    workers.push(fake);
    return fake;
  } });
  await api.ready;
  await api.admit(admission());
  return { api, fake: workers[0], workers };
}
const outcome = promise => promise.then(value => ({ value }), error => ({ error }));

test('public API serializes admission, setup, named input, proof and verification', async () => {
  const fake = new FakeWorker();
  const api = new ProofClient({ workerFactory: () => fake });
  const admitted = api.admit(admission());
  const setup = api.setSetup('key', new Uint8Array([1]));
  const input = api.setInput('pk', new Uint8Array([9, 8]));
  const proof = api.prove(proving());
  assert.deepEqual((await admitted).timings, admissionTimings);
  await setup;
  await input;
  const result = await proof;
  assert.equal(result.report.success, true);
  assert.deepEqual(result.report.timings, reportTimings);
  assert.deepEqual(JSON.parse(result.reportText).timings, reportTimings);
  const verified = await api.verify({ public: new Uint8Array(), proof: result.proof });
  assert.equal(verified.report.accepted, true);
  assert.deepEqual(fake.messages.map(m => m.operation), ['initialize', 'admit', 'setup', 'input', 'prove', 'verify']);
  assert.deepEqual(fake.input, ['pk', new Uint8Array([9, 8])]);
  api.dispose();
});

test('named input snapshots queued bytes and consuming transfers detach all aliases', async () => {
  const { api, fake } = await client({ hold: new Set(['setup', 'input']) });
  const setup = api.setSetup('vk', new Uint8Array([1]));
  const material = new Uint8Array([2, 3, 4]);
  const borrowed = api.setInput('pk', material.subarray(1));
  material.fill(99);
  await fake.release();
  await setup;
  await turn();
  await fake.release();
  await borrowed;
  assert.deepEqual(fake.input, ['pk', new Uint8Array([3, 4])]);
  assert.equal(material.byteLength, 3);
  const disposable = new Uint8Array([5, 6, 7, 8]);
  const alias = disposable.subarray(1, 3);
  const consumed = api.setInput('pk', alias, { consume: true });
  assert.equal(disposable.byteLength, 0);
  assert.equal(alias.byteLength, 0);
  await fake.release();
  await consumed;
  assert.deepEqual(fake.input, ['pk', new Uint8Array([6, 7])]);
  api.dispose();
});

test('named input bounds and argument refusals precede consumption', async () => {
  const { api, fake } = await client({ hold: new Set(['input']) }, { maxQueue: 1, maxPendingBytes: 40 });
  const material = new Uint8Array([1]);
  await assert.rejects(api.setInput(1, material, { consume: true }), /web-message-string: name/);
  await assert.rejects(api.setInput('pk', 'bad', { consume: true }), /web-message-bytes: material/);
  const backing = new Uint8Array(41);
  await assert.rejects(api.setInput('pk', backing.subarray(0, 1), { consume: true }), /web-client-bytes-full/);
  assert.equal(backing.byteLength, 41);
  assert.equal(material.byteLength, 1);
  const active = outcome(api.setInput('pk', material));
  const queued = outcome(api.setInput('aux', material));
  await assert.rejects(api.setInput('overflow', material, { consume: true }), /web-client-queue-full/);
  assert.equal(material.byteLength, 1);
  assert.equal(fake.messages.filter(m => m.operation === 'input').length, 1);
  api.terminate();
  assert.equal((await active).error.completion, 'unknown');
  assert.equal((await queued).error.completion, 'not-started');
});

test('named input cancellation removes queued work and SDK refusals never replay or fall back', async () => {
  const config = { hold: new Set(['setup']), inputError: true };
  const { api, fake } = await client(config);
  const setup = api.setSetup('vk', new Uint8Array([1]));
  const controller = new AbortController();
  const cancelled = outcome(api.setInput('cancelled', new Uint8Array([1]), { signal: controller.signal }));
  controller.abort();
  assert.equal((await cancelled).error.completion, 'not-started');
  await fake.release();
  await setup;
  await assert.rejects(api.setInput('pk', new Uint8Array([2])), error =>
    error.code === 'web-setup-limit' && error.completion === 'known' && !error.fatal);
  assert.equal(fake.messages.filter(m => m.operation === 'input').length, 1);
  assert.equal(fake.terminated, false);
  config.inputError = false;
  await api.setInput('pk', new Uint8Array([3]));
  await api.prove({ ...proving(), budget: '18446744073709551615' });
  assert.equal(fake.callArguments[3], 0xffffffffffffffffn);
  assert.equal(fake.messages.filter(m => m.operation === 'input').length, 2);
  api.dispose();
});

test('invalid admission timings reject admission and queued input before any binding', async () => {
  const fake = new FakeWorker({ timings: undefined });
  const api = new ProofClient({ workerFactory: () => fake });
  const admitted = outcome(api.admit(admission()));
  const input = outcome(api.setInput('pk', new Uint8Array([1])));
  assert.match((await admitted).error.code, /web-session-timings/);
  assert.equal((await input).error.completion, 'not-started');
  assert.equal(fake.input, undefined);
  assert.equal(fake.terminated, true);
});

test('typed-array storage overrides cannot reenter queue, abort or disposal', async () => {
  for (const action of ['queue', 'abort', 'dispose']) {
    const { api, fake } = await client();
    const controller = new AbortController();
    const material = new Uint8Array([9]);
    const backing = material.buffer;
    let entered = false;
    Object.defineProperty(material, 'buffer', { get() {
      entered = true;
      if (action === 'queue') api.prove(proving());
      if (action === 'abort') controller.abort();
      if (action === 'dispose') api.dispose();
      return backing;
    } });
    for (const key of ['byteOffset', 'byteLength']) Object.defineProperty(material, key, {
      get() { throw new Error('caller storage getter must not run'); },
    });
    await api.setInput('pk', material, { consume: true, signal: controller.signal });
    assert.equal(entered, false);
    assert.equal(backing.byteLength, 0);
    assert.deepEqual(fake.input, ['pk', new Uint8Array([9])]);
    assert.equal(fake.calls, 0);
    assert.equal(fake.terminated, false);
    api.dispose();
  }
});

test('reentrant nested option normalization rechecks queue, abort and disposal before consumption', async () => {
  for (const action of ['queue', 'abort', 'dispose']) {
    const { api, fake } = await client({ hold: new Set(['prove']) }, { maxQueue: 1 });
    const pending = [outcome(api.prove(proving()))];
    const controller = new AbortController();
    let entered = false;
    const providers = new Proxy(['plonky3'], { getOwnPropertyDescriptor(target, key) {
      if (key === '0' && !entered) {
        entered = true;
        if (action === 'queue') pending.push(outcome(api.prove(proving())));
        if (action === 'abort') controller.abort();
        if (action === 'dispose') api.dispose();
      }
      return Reflect.getOwnPropertyDescriptor(target, key);
    } });
    const args = { ...admission(), options: { providers } };
    const expected = { queue: 'web-client-queue-full', abort: 'web-client-cancelled', dispose: 'web-client-disposed' }[action];
    await assert.rejects(api.admit(args, { consume: true, signal: controller.signal }), error =>
      error.code === expected && error.completion === 'not-started');
    assert.equal(entered, true);
    assert.equal(args.package.byteLength, 2);
    assert.equal(args.pin.byteLength, 32);
    assert.equal(fake.messages.filter(m => m.operation === 'admit').length, 1);
    if (action !== 'dispose') {
      await fake.release();
      await turn();
      await fake.release();
      assert.equal(fake.calls, action === 'queue' ? 2 : 1);
    }
    api.dispose();
    await Promise.all(pending);
  }
});

test('synchronous Worker startup failure has stable lifecycle metadata and cause', async () => {
  const cause = new DOMException('injected startup policy', 'SecurityError');
  const api = new ProofClient({ workerFactory: () => { throw cause; } });
  await assert.rejects(api.ready, error => error instanceof ProofClientError &&
    error.code === 'web-worker-start' && error.fatal && error.completion === 'not-started' && error.cause === cause);
  await assert.rejects(api.setInput('pk', new Uint8Array([1])), /web-client-closed/);
  api.dispose();
  await assert.rejects(api.recycle(), /web-client-disposed/);
});

test('synchronous recycle startup failure closes the new generation with stable metadata', async () => {
  const fake = new FakeWorker();
  const cause = new DOMException('injected recycle policy', 'SecurityError');
  let starts = 0;
  const api = new ProofClient({ workerFactory: () => {
    if (++starts > 1) throw cause;
    return fake;
  } });
  await api.ready;
  await api.admit(admission());
  await assert.rejects(api.recycle(), error => error instanceof ProofClientError &&
    error.code === 'web-worker-start' && error.fatal && error.completion === 'not-started' && error.cause === cause);
  assert.equal(fake.terminated, true);
  assert.equal(fake.calls, 0);
  assert.equal(api.generation, 2);
  await assert.rejects(api.prove(proving()), /web-client-closed/);
  api.dispose();
});

test('queue and retained byte bounds refuse before detaching user input', async () => {
  const { api, fake } = await client({ hold: new Set(['prove']) }, { maxQueue: 1, maxPendingBytes: 40 });
  const first = outcome(api.prove(proving()));
  const second = outcome(api.prove(proving()));
  const overflow = proving();
  await assert.rejects(api.prove(overflow, { consume: true }), /web-client-queue-full/);
  assert.equal(overflow.witness.byteLength, 1);
  assert.equal(fake.messages.filter(m => m.operation === 'prove').length, 1);
  api.terminate();
  assert.equal((await first).error.completion, 'unknown');
  assert.equal((await second).error.completion, 'not-started');
  const bounded = await client({}, { maxPendingBytes: 40 });
  const large = { public: new Uint8Array(41), witness: new Uint8Array() };
  await assert.rejects(bounded.api.prove(large, { consume: true }), /web-client-bytes-full/);
  assert.equal(large.public.byteLength, 41);
  bounded.api.dispose();
});

test('borrowed calls snapshot at enqueue while consuming calls detach whole aliasing buffers', async () => {
  const { api, fake } = await client({ hold: new Set(['prove']) });
  const borrowed = proving();
  const first = api.prove(borrowed);
  borrowed.public[0] = 99;
  assert.equal(borrowed.public.byteLength, 1);
  assert.equal(fake.messages.at(-1).public[0], 3);
  const backing = new Uint8Array([1, 2, 3, 4]);
  const alias = backing.subarray(1, 3);
  const consumed = api.prove({ public: alias, witness: alias }, { consume: true });
  assert.equal(backing.byteLength, 0);
  assert.equal(alias.byteLength, 0);
  await fake.release();
  await first;
  await turn();
  await fake.release();
  await consumed;
  assert.deepEqual([...fake.callArguments[0]], [2, 3]);
  api.dispose();
});

test('ordinary SDK refusal rejects one promise and leaves the queue usable', async () => {
  const { api, fake } = await client({ sdkError: true });
  await assert.rejects(api.prove(proving()), /entry-request-format: public/);
  await api.setSetup('key', new Uint8Array([1]));
  assert.equal(fake.terminated, false);
  api.dispose();
});

for (const type of ['error', 'messageerror']) {
  test(`${type} settles active and queued requests with distinct completion states`, async () => {
    const { api, fake } = await client({ hold: new Set(['prove']) });
    const first = outcome(api.prove(proving()));
    const second = outcome(api.prove(proving()));
    fake.emit(type);
    assert.equal((await first).error.completion, 'unknown');
    assert.equal((await second).error.completion, 'not-started');
    assert.equal(fake.terminated, true);
    await assert.rejects(api.prove(proving()), /web-client-closed/);
  });
}

test('fatal Wasm result settles every request without replay', async () => {
  const { api, fake } = await client({ trap: true });
  const results = await Promise.all([outcome(api.prove(proving())), outcome(api.prove(proving()))]);
  assert.equal(results[0].error.fatal, true);
  assert.equal(results[0].error.completion, 'known');
  assert.equal(results[1].error.completion, 'not-started');
  assert.equal(fake.calls, 1);
  assert.equal(fake.terminated, true);
});

test('lost result delivery times out completion-unknown and discards all queued calls', async () => {
  const { api, fake } = await client({ dropReplies: new Set(['prove']) });
  const first = outcome(api.prove(proving(), { timeoutMs: 20 }));
  const second = outcome(api.prove(proving()));
  assert.equal((await first).error.completion, 'unknown');
  assert.equal((await second).error.completion, 'not-started');
  assert.equal(fake.calls, 1);
  assert.equal(fake.free, 1);
  assert.equal(fake.terminated, true);
});

test('queued timeout settles just that request without killing an active invocation', async () => {
  const { api, fake } = await client({ hold: new Set(['prove']) });
  const first = api.prove(proving());
  await assert.rejects(api.prove(proving(), { timeoutMs: 10 }), error => error.completion === 'not-started');
  assert.equal(fake.terminated, false);
  await fake.release();
  await first;
  assert.equal(fake.calls, 1);
  api.dispose();
});

test('cooperative cancellation removes queued calls and waits for active completion', async () => {
  const { api, fake } = await client({ hold: new Set(['prove']) });
  const activeSignal = new AbortController();
  let settled = false;
  const first = outcome(api.prove(proving(), { signal: activeSignal.signal })).then(value => { settled = true; return value; });
  const queuedSignal = new AbortController();
  const second = outcome(api.prove(proving(), { signal: queuedSignal.signal }));
  queuedSignal.abort();
  activeSignal.abort();
  await turn();
  assert.equal(settled, false);
  assert.equal((await second).error.completion, 'not-started');
  await fake.release();
  assert.equal((await first).error.completion, 'known');
  assert.equal(fake.calls, 1);
  assert.equal(fake.terminated, false);
  api.dispose();
});

test('dispose and hard termination settle every promise and permanently dispose rejects reuse', async () => {
  const { api, fake } = await client({ hold: new Set(['prove']) });
  const calls = [outcome(api.prove(proving())), outcome(api.prove(proving()))];
  api.dispose();
  assert.equal((await calls[0]).error.completion, 'unknown');
  assert.equal((await calls[1]).error.completion, 'not-started');
  assert.equal(fake.terminated, true);
  api.dispose();
  await assert.rejects(api.recycle(), /web-client-disposed/);
});

test('current-generation correlation errors fail pending calls; stale-generation replies are ignored', async () => {
  const { api, fake } = await client({ hold: new Set(['prove']) });
  const pending = outcome(api.prove(proving()));
  fake.emit('message', { data: { generation: 9, id: 3, fatal: true, error: 'stale' } });
  assert.equal(fake.terminated, false);
  fake.emit('message', { data: { generation: api.generation, id: 999 } });
  assert.match((await pending).error.code, /web-client-correlation/);
  assert.equal(fake.terminated, true);
});

test('idle recycling preserves code but creates a new Worker and requires fresh admission', async () => {
  const { api, fake, workers } = await client();
  const module = api.compiledModule;
  const generation = api.generation;
  await api.recycle();
  assert.equal(fake.terminated, true);
  assert.equal(api.generation, generation + 1);
  assert.notEqual(workers[1], fake);
  assert.ok(workers[1].loaded.module instanceof WebAssembly.Module);
  assert.equal(module instanceof WebAssembly.Module, true);
  await assert.rejects(api.prove(proving()), /web-session-missing/);
  await api.admit(admission());
  await api.prove(proving());
  api.dispose();
});

test('busy recycling is refused and a failed send closes all pending work', async () => {
  const { api } = await client({ hold: new Set(['prove']) });
  const pending = outcome(api.prove(proving()));
  await assert.rejects(api.recycle(), /web-client-busy/);
  api.terminate();
  await pending;
  const failed = await client({ failSend: true });
  await assert.rejects(failed.api.prove(proving()), /web-client-send/);
  assert.equal(failed.fake.terminated, true);
});

test('initialization loss, invalid controls and invalid late bytes cannot strand promises', async () => {
  const fake = new FakeWorker({ dropReplies: new Set(['initialize']) });
  const api = new ProofClient({ timeoutMs: 10, workerFactory: () => fake });
  const admitted = outcome(api.admit(admission()));
  await assert.rejects(api.ready, /web-client-timeout/);
  assert.equal((await admitted).error.completion, 'not-started');
  const live = await client();
  for (const controls of [{ timeoutMs: 0 }, { timeoutMs: 0x80000000 }, { consume: 'yes' }, { signal: {} }, { extra: true }]) {
    await assert.rejects(live.api.prove(proving(), controls), /web-client-/);
  }
  const input = proving();
  await assert.rejects(live.api.prove({ ...input, context: 'bad' }, { consume: true }), /web-message-bytes/);
  assert.equal(input.public.byteLength, 1);
  assert.equal(live.fake.calls, 0);
  live.api.dispose();
});

test('repeated small calls and a large result preserve transfer ownership', async () => {
  const { api, fake } = await client({ resultBytes: 1024 * 1024 }, { maxPendingBytes: 40 });
  for (let i = 0; i < 30; i++) {
    const result = await api.prove(proving());
    assert.equal(result.proof.byteLength, 1024 * 1024);
  }
  assert.equal(fake.free, 30);
  api.dispose();
});

test('a failure after publication closes the session before queued Wasm entry', async () => {
  const { api, fake } = await client({ freeTrap: true });
  const first = outcome(api.prove(proving()));
  const second = outcome(api.prove(proving()));
  assert.equal((await first).value.report.success, true);
  assert.equal((await second).error.completion, 'unknown');
  assert.equal(fake.calls, 1);
  assert.equal(fake.terminated, true);
});

test('failure publishing both a result and its error settles through Worker loss', async () => {
  const { api, fake } = await client({ failResult: true, failReply: true });
  const first = outcome(api.prove(proving()));
  const second = outcome(api.prove(proving()));
  assert.equal((await first).error.completion, 'unknown');
  assert.equal((await second).error.completion, 'not-started');
  assert.equal(fake.free, 1);
  assert.equal(fake.terminated, true);
});

test('recycling after a trap never replays work or accepts callbacks from the old Worker', async () => {
  const config = { trap: true };
  const { api, fake, workers } = await client(config);
  const oldReceive = [...fake.listeners.get('message')][0];
  await assert.rejects(api.prove(proving()), /injected trap/);
  config.trap = false;
  await api.recycle();
  assert.equal(workers[1].calls, 0);
  await api.admit(admission());
  const pending = api.prove(proving());
  oldReceive({ data: { generation: api.generation, id: workers[1].messages.at(-1).id, fatal: true, error: 'old Worker callback' } });
  assert.equal((await pending).report.success, true);
  assert.equal(fake.calls, 1);
  assert.equal(workers[1].calls, 1);
  api.dispose();
});

test('queued admission freezes provider options independently of caller mutation', async () => {
  const fake = new FakeWorker({ hold: new Set(['initialize']) });
  const api = new ProofClient({ workerFactory: () => fake });
  const options = { providers: ['plonky3'], external_work: 0xffffffffffffffffn };
  const pending = api.admit({ ...admission(), options });
  options.providers.push('blst');
  options.external_work = 0n;
  await fake.release();
  await pending;
  assert.equal(fake.arguments[2], '{"providers":["plonky3"],"external_work":18446744073709551615}');
  api.dispose();
});


test('successful replies require operation payloads before the queue continues', async () => {
  for (const patch of [{ proof: undefined }, { milliseconds: Infinity }, { report: {} }]) {
    const { api, fake } = await client({ hold: new Set(['prove']) });
    const active = outcome(api.prove(proving()));
    const queued = outcome(api.verify({ public: new Uint8Array(), proof: new Uint8Array() }));
    const call = fake.messages.at(-1);
    fake.emit('message', { data: { id: call.id, generation: call.generation,
      proof: new Uint8Array(), milliseconds: 1, reportText: '{}',
      report: { success: true, accepted: null }, ...patch } });
    assert.equal((await active).error.code, 'web-client-protocol');
    assert.equal((await active).error.completion, 'unknown');
    assert.equal((await queued).error.completion, 'not-started');
    assert.equal(fake.terminated, true);
    api.dispose();
  }
});

test('control names are bounded before consuming payloads', async () => {
  const { api } = await client();
  const bytes = new Uint8Array([1]);
  await assert.rejects(api.setSetup('s'.repeat(4097), bytes, { consume: true }), /web-message-string: slot/);
  await assert.rejects(api.setInput('i'.repeat(4097), bytes, { consume: true }), /web-message-string: name/);
  assert.equal(bytes.byteLength, 1);
  api.dispose();
});


test('SDK refusal preserves phase and Unicode path without discarding the session', async () => {
  const config = { structuredError: { code: 'entry-input-unfilled', phase: 'request', path: 'public.公開.値' } };
  const { api, fake } = await client(config);
  await assert.rejects(api.prove(proving()), error => error instanceof ProofClientError &&
    error.code === 'entry-input-unfilled' && error.phase === 'request' && error.path === 'public.公開.値' &&
    error.refusal.code === 'entry-input-unfilled' && error.refusal.path === error.path &&
    error.completion === 'known' && !error.fatal);
  config.structuredError = undefined;
  assert.equal((await api.prove(proving())).report.success, true);
  assert.equal(fake.terminated, false);
  api.dispose();
});

test('consuming transfer charges intrinsic backing size before detachment', async () => {
  const { api } = await client({}, { maxPendingBytes: 64 });
  for (const descriptor of [{ value: 0 }, { get() { throw new Error('shadowed byteLength'); } }]) {
    const backing = new ArrayBuffer(4096);
    Object.defineProperty(backing, 'byteLength', descriptor);
    const publicBytes = new Uint8Array(backing, 0, 1);
    await assert.rejects(api.prove({ public: publicBytes, witness: new Uint8Array(1) },
      { consume: true }), /web-client-bytes-full/);
    assert.equal(new Uint8Array(backing).length, 4096);
  }
  assert.equal((await api.prove(proving())).report.success, true);
  api.dispose();
});
