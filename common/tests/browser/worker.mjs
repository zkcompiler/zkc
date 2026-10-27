import assert from 'node:assert/strict';
import test from 'node:test';
import { FakeWorker, admission, proving, turn, admissionTimings, reportTimings } from './fake-worker.mjs';
import { optionsJSON, request, supportsSimd } from '../../../crates/zkc-web/web/protocol.mjs';

async function worker(config = {}) {
  const fake = new FakeWorker(config);
  let id = 0;
  const send = data => fake.scope.onmessage({ data });
  const call = (operation, args = {}) => send({ id: ++id, generation: 1, operation, ...args });
  await call('initialize');
  await call('admit', admission());
  return { fake, send, call };
}

test('admission validates and publishes the timing getter before exposing a session', async () => {
  const { fake } = await worker();
  const reply = fake.replies.at(-1);
  assert.deepEqual(reply.description, { fixture: true });
  assert.deepEqual(reply.timings, admissionTimings);
  assert.ok(fake.events.indexOf('timings') < fake.events.lastIndexOf('reply'));
  assert.equal(fake.closed, false);
});

test('missing, malformed and invalid admission timings are fatal before publication', async () => {
  for (const timings of [undefined, {}, '{', 'null', '[]', '{}',
    '{"package_capture_ms":1,"package_admit_ms":"2"}',
    '{"package_capture_ms":-1,"package_admit_ms":2}',
    '{"package_capture_ms":1,"package_admit_ms":1e999}',
    '{"package_capture_ms":1,"package_admit_ms":2,"unexpected":3}']) {
    const { fake } = await worker({ timings });
    assert.match(fake.replies.at(-1).error, /web-session-timings/);
    assert.equal(fake.replies.at(-1).fatal, true);
    assert.equal(fake.replies.some(reply => Object.hasOwn(reply, 'description')), false);
    assert.equal(fake.closed, true);
  }
  const { fake } = await worker({ timingsError: true });
  assert.match(fake.replies.at(-1).error, /injected timings getter failure/);
  assert.equal(fake.replies.at(-1).fatal, true);
  assert.equal(fake.closed, true);
});

test('named opaque inputs use only setInput and validate every argument before glue', async () => {
  const { fake, call, send } = await worker();
  for (const args of [{ name: 1, material: new Uint8Array([1]) },
    { name: 'pk', material: 'bad' }, { name: 'pk', material: new Uint8Array(), extra: true }]) {
    await call('input', args);
    assert.match(fake.replies.at(-1).error, /web-message/);
    assert.equal(fake.replies.at(-1).fatal, false);
    assert.equal(fake.input, undefined);
  }
  const detached = new Uint8Array([1]);
  structuredClone(detached, { transfer: [detached.buffer] });
  assert.throws(() => request('input', { name: 'pk', material: detached }), /web-message-bytes/);
  if (typeof SharedArrayBuffer !== 'undefined') {
    assert.throws(() => request('input', { name: 'pk', material: new Uint8Array(new SharedArrayBuffer(1)) }), /web-message-bytes/);
  }
  await send({ id: 6, generation: 2, operation: 'input', name: 'pk', material: new Uint8Array([1]) });
  assert.match(fake.replies.at(-1).error, /web-session-generation/);
  assert.equal(fake.input, undefined);
  // Deliberately invalid key bytes remain opaque to this JS layer.
  await call('input', { name: 'pk', material: new Uint8Array([255, 0, 7]) });
  assert.deepEqual(fake.input, ['pk', new Uint8Array([255, 0, 7])]);
  assert.equal(fake.setup, undefined);
  assert.equal(fake.calls, 0);
  assert.equal(fake.closed, false);
});

test('invalid envelopes and correlation IDs are refused before execution', async () => {
  const { fake, send } = await worker();
  for (const data of [null, 12, 'message', []]) {
    await send(data);
    assert.equal(fake.replies.at(-1).error, 'Error: web-message');
  }
  for (const id of [undefined, {}, [], Number.MAX_SAFE_INTEGER + 1, 'request', 0]) {
    await send({ id, generation: 1, operation: 'prove', ...proving() });
    assert.equal(fake.replies.at(-1).error, 'Error: web-message-id');
    assert.equal(fake.replies.at(-1).id, undefined);
    assert.equal(fake.replies.at(-1).fatal, false);
  }
  assert.equal(fake.calls, 0);
  assert.equal(fake.closed, false);
});

test('a trapped Worker closes even if reporting its failure throws', async () => {
  const { fake, call } = await worker({ trap: true, failReply: true });
  await assert.rejects(call('prove', proving()), { name: 'DataCloneError' });
  assert.equal(fake.calls, 1);
  assert.equal(fake.closed, true);
});

test('queued continuations cannot reenter a trapped session', async () => {
  const { fake, call } = await worker({ trap: true });
  await Promise.all([call('prove', proving()), call('prove', proving())]);
  assert.equal(fake.calls, 1);
  assert.equal(fake.closed, true);
  assert.equal(fake.replies.at(-1).fatal, true);
});

test('stale generations, duplicate IDs and reselection never enter Wasm', async () => {
  const { fake, call, send } = await worker();
  await send({ id: 3, generation: 2, operation: 'prove', ...proving() });
  assert.match(fake.replies.at(-1).error, /web-session-generation/);
  await send({ id: 2, generation: 1, operation: 'prove', ...proving() });
  assert.match(fake.replies.at(-1).error, /web-message-id-order/);
  await call('initialize', { variant: 'simd' });
  assert.match(fake.replies.at(-1).error, /web-worker-initialized/);
  await call('admit', { ...admission(), options: { providers: ['plonky3'] } });
  assert.match(fake.replies.at(-1).error, /web-session-active/);
  assert.equal(fake.calls, 0);
  await call('prove', proving());
  assert.equal(fake.calls, 1);
});

test('initialization has no unbounded Worker-side queue or parallel continuation', async () => {
  let release;
  const fake = new FakeWorker({ loadGate: new Promise(resolve => { release = resolve; }) });
  const initialization = fake.scope.onmessage({ data: { id: 1, generation: 1, operation: 'initialize' } });
  await fake.scope.onmessage({ data: { id: 2, generation: 1, operation: 'admit', ...admission() } });
  assert.match(fake.replies.at(-1).error, /web-worker-busy/);
  release();
  await initialization;
  assert.equal(fake.arguments, undefined);
});

test('invalid late arguments, unknown options and wasm32 sizes are refused before glue', async () => {
  const { fake, call } = await worker();
  for (const args of [{ ...proving(), context: 'bad' }, { ...proving(), budget: Number.MAX_SAFE_INTEGER + 1 },
    { ...proving(), budget: '-1' }, { ...proving(), budget: '18446744073709551616' },
    { ...proving(), extra: true }, { ...proving(), witness: undefined }, { ...proving(), context: null }]) {
    await call('prove', args);
    assert.equal(fake.replies.at(-1).fatal, false);
  }
  assert.equal(fake.calls, 0);
  for (const options of [{ providers: ['Plonky3'] }, { providers: ['unknown'] }, { operation: 'run' },
    { allow_authored: 1 }, { unknown: true }, { package_bytes: 0x100000000 },
    { external_work: Number.MAX_SAFE_INTEGER + 1 },
    { capacity: ['zkc.native-capacity/0', '1', '1', '1', '1', ['1', '1', '1'], ['1', '4294967296']] }]) {
    assert.throws(() => request('admit', { ...admission(), options }), /web-/);
  }
  const detached = new Uint8Array();
  structuredClone(detached, { transfer: [detached.buffer] });
  assert.throws(() => request('prove', { ...proving(), witness: detached }), /web-message-bytes/);
  if (typeof SharedArrayBuffer !== 'undefined') {
    assert.throws(() => request('prove', { ...proving(), context: new Uint8Array(new SharedArrayBuffer(1)) }), /web-message-bytes/);
  }
});

test('u64 values preserve exact decimal bytes and providers are frozen before admission', async () => {
  const fake = new FakeWorker();
  await fake.scope.onmessage({ data: { id: 1, generation: 1, operation: 'initialize' } });
  await fake.scope.onmessage({ data: { id: 2, generation: 1, operation: 'admit', ...admission(),
    options: { providers: ['plonky3', 'arkworks', 'plonky3'], external_work: '18446744073709551615' } } });
  assert.equal(fake.arguments[2], '{"providers":["arkworks","plonky3"],"external_work":18446744073709551615}');
  await fake.scope.onmessage({ data: { id: 3, generation: 1, operation: 'prove', ...proving(), budget: '18446744073709551615' } });
  assert.equal(fake.callArguments[3], 0xffffffffffffffffn);
  assert.equal(optionsJSON({ external_work: 0xffffffffffffffffn }), '{"external_work":18446744073709551615}');
});

test('successful transferable publication precedes result.free and preserves raw report', async () => {
  const { fake, call } = await worker();
  await call('prove', proving());
  assert.deepEqual([...fake.replies.at(-1).proof], [5, 6]);
  assert.match(fake.replies.at(-1).reportText, /18446744073709551615/);
  assert.deepEqual(fake.replies.at(-1).report.timings, reportTimings);
  assert.deepEqual(JSON.parse(fake.replies.at(-1).reportText).timings, reportTimings);
  assert.ok(fake.events.indexOf('publish') < fake.events.indexOf('result.free'));
  assert.equal(fake.free, 1);
  assert.equal(fake.closed, false);
});

for (const config of [{ getterError: true }, { badReport: true }, { failResult: true }]) {
  test(`result failure frees custody and kills the session: ${JSON.stringify(config)}`, async () => {
    const { fake, call } = await worker(config);
    await call('prove', proving());
    assert.equal(fake.free, 1);
    assert.equal(fake.closed, true);
    assert.equal(fake.replies.at(-1).fatal, true);
  });
}

test('direct disposal frees the session and closes its Worker', async () => {
  const { fake, call } = await worker();
  await call('dispose');
  assert.ok(fake.events.indexOf('dispose') < fake.events.indexOf('session.free'));
  assert.equal(fake.closed, true);
  assert.equal(fake.replies.at(-1).id, 3);
  assert.equal(fake.events.filter(event => event === 'dispose').length, 1);
  assert.equal(fake.events.filter(event => event === 'session.free').length, 1);
});

test('direct disposal closes an initialized Worker before admission or after a refused admission', async () => {
  for (const admissionError of [false, true]) {
    const fake = new FakeWorker({ admissionError });
    const send = (id, operation, args = {}) => fake.scope.onmessage({ data: { id, generation: 1, operation, ...args } });
    await send(1, 'initialize');
    if (admissionError) {
      await send(2, 'admit', admission());
      assert.equal(fake.replies.at(-1).error, 'package-refused');
      assert.equal(fake.replies.at(-1).fatal, false);
      assert.equal(fake.closed, false);
    }
    await send(3, 'dispose');
    assert.deepEqual(fake.replies.at(-1), { id: 3, generation: 1 });
    assert.equal(fake.closed, true);
    assert.equal(fake.events.includes('dispose'), false);
    assert.equal(fake.events.includes('session.free'), false);
  }
});

test('nested option arrays normalize data without invoking custom methods or accessors', () => {
  const providers = ['plonky3'];
  providers.some = providers[Symbol.iterator] = () => { throw new Error('custom array method'); };
  assert.equal(optionsJSON({ providers }), '{"providers":["plonky3"]}');
  Object.defineProperty(providers, '0', { get() { throw new Error('custom array accessor'); } });
  assert.throws(() => optionsJSON({ providers }), /web-options-providers/);
  const capacity = ['zkc.native-capacity/0', '1', '1', '1', '1', ['1', '1', '1'], ['1', '1']];
  capacity.slice = capacity[5].map = () => { throw new Error('custom capacity method'); };
  assert.deepEqual(JSON.parse(optionsJSON({ capacity })).capacity,
    ['zkc.native-capacity/0', '1', '1', '1', '1', ['1', '1', '1'], ['1', '1']]);
});

test('feature selection precedes loading with no failed-module fallback', async () => {
  assert.equal(typeof supportsSimd(), 'boolean');
  for (const [variant, supported, expected] of [['portable', false, 'portable'], ['auto', false, 'portable'],
    ['auto', true, 'simd'], ['simd', true, 'simd']]) {
    const fake = new FakeWorker({ simd: supported });
    await fake.scope.onmessage({ data: { id: 1, generation: 1, operation: 'initialize', variant } });
    assert.equal(fake.loaded.variant, expected);
  }
  const fake = new FakeWorker({ simd: false });
  await fake.scope.onmessage({ data: { id: 1, generation: 1, operation: 'initialize', variant: 'simd' } });
  assert.equal(fake.loaded, undefined);
  assert.equal(fake.closed, true);
  assert.match(fake.replies.at(-1).error, /web-simd-unavailable/);
  const broken = new FakeWorker({ loadError: true });
  await broken.scope.onmessage({ data: { id: 1, generation: 1, operation: 'initialize', variant: 'auto' } });
  assert.equal(broken.loaded.variant, 'simd');
  assert.equal(broken.closed, true);
});

test('Worker-side messageerror is fatal even without a request ID', async () => {
  const { fake } = await worker();
  fake.scope.onmessageerror();
  await turn();
  assert.equal(fake.closed, true);
  assert.equal(fake.replies.at(-1).generation, 1);
  assert.equal(fake.replies.at(-1).fatal, true);
});

test('an Error escaping a glue import aborts the session', async () => {
  const { fake, call } = await worker({ abortError: true });
  await call('prove', proving());
  assert.equal(fake.closed, true);
  assert.equal(fake.replies.at(-1).fatal, true);
});
