import { bytes, envelope, fail, optionsJSON, record, sdkRefusal, supportsSimd } from './protocol.mjs';

function admissionTimings(value) {
  if (typeof value !== 'string') fail('web-session-timings');
  let timings;
  try { timings = JSON.parse(value); }
  catch { fail('web-session-timings'); }
  const names = ['package_capture_ms', 'package_admit_ms'];
  record(timings, names, 'web-session-timings');
  if (names.some(name => typeof timings[name] !== 'number' ||
      !Number.isFinite(timings[name]) || timings[name] < 0)) fail('web-session-timings');
  return timings;
}

async function loadBinding(variant, compiledModule) {
  const directory = variant === 'simd' ? './pkg-simd/' : './pkg/';
  const binding = await import(new URL(directory + 'zkc_web.js', import.meta.url));
  if (!compiledModule) {
    const response = await fetch(new URL(directory + 'zkc_web_bg.wasm', import.meta.url));
    if (!response.ok) fail(`web-module-http: ${response.status}`);
    compiledModule = response.headers.get('Content-Type')?.split(';')[0] === 'application/wasm'
      ? await WebAssembly.compileStreaming(response)
      : await WebAssembly.compile(await response.arrayBuffer());
  }
  // wasm-bindgen 0.2.129 accepts this object; a Module supplies code only.
  // Each dedicated Worker gets fresh glue globals, instance and memory.
  await binding.default({ module_or_path: compiledModule });
  return { ProofSession: binding.ProofSession, module: compiledModule };
}

export function installWorker(scope, { load = loadBinding, simd = supportsSimd, now = () => performance.now() } = {}) {
  let generation;
  let lastId = 0;
  let busy = false;
  let closed = false;
  let binding;
  let session;

  function close() {
    closed = true;
    session = undefined;
    binding = undefined;
    scope.close();
  }

  scope.onmessageerror = () => {
    if (closed) return;
    try { scope.postMessage({ generation, error: 'web-worker-messageerror', fatal: true }); }
    finally { close(); }
  };

  scope.onmessage = async ({ data }) => {
    if (closed) return;
    let id;
    let replyGeneration;
    let fatal = false;
    let ownsBusy = false;
    try {
      if (Number.isSafeInteger(data?.id) && data.id > 0) id = data.id;
      if (Number.isSafeInteger(data?.generation) && data.generation > 0) replyGeneration = data.generation;
      const call = envelope(data);
      if (generation !== undefined && call.generation !== generation) fail('web-session-generation');
      if (busy) fail('web-worker-busy');
      if (call.id <= lastId) fail('web-message-id-order');
      lastId = call.id;
      busy = ownsBusy = true;
      const reply = value => {
        try { scope.postMessage({ id, generation: replyGeneration, ...value }); }
        catch (error) { fatal = true; throw error; }
      };
      const invoke = action => {
        try { return action(); }
        catch (error) {
          // Generated Result<_, String> errors are ordinary SDK refusals.
          // Other exceptions escaping glue/imports give no cleanup guarantee.
          if (typeof error !== 'string') fatal = true;
          throw error;
        }
      };

      if (call.operation === 'initialize') {
        if (generation !== undefined) fail('web-worker-initialized');
        generation = call.generation;
        fatal = true;
        const supported = simd();
        const variant = call.variant === 'auto' ? (supported ? 'simd' : 'portable') : call.variant;
        if (variant === 'simd' && !supported) fail('web-simd-unavailable');
        binding = await load(variant, call.module);
        if (closed) return;
        reply({ variant, module: binding.module });
        return;
      }
      if (!binding) fail('web-worker-uninitialized');
      if (call.operation === 'dispose') {
        fatal = true;
        if (session) {
          try { session.dispose(); } finally { session.free(); }
          session = undefined;
        }
        try { reply({}); } finally { close(); }
        return;
      }
      if (call.operation === 'admit') {
        if (session) fail('web-session-active');
        const json = optionsJSON(call.options);
        session = invoke(() => new binding.ProofSession(call.package, call.pin, json, call.authority));
        fatal = true;
        const description = JSON.parse(session.describe());
        const timings = admissionTimings(session.timings);
        reply({ description, timings });
        return;
      }
      if (!session) fail('web-session-missing');
      if (call.operation === 'setup') {
        invoke(() => session.setSetup(call.slot, call.material));
        reply({});
        return;
      }
      if (call.operation === 'input') {
        invoke(() => session.setInput(call.name, call.material));
        reply({});
        return;
      }
      const started = now();
      const result = invoke(() => call.operation === 'prove'
        ? session.prove(call.public, call.witness, call.context, call.budget)
        : session.verify(call.public, call.proof, call.context, call.budget));
      fatal = true;
      try {
        const milliseconds = now() - started;
        const proof = bytes(result.proof, 'result.proof');
        const output = result.outputs;
        const outputs = output === undefined ? undefined : bytes(output, 'result.outputs');
        const reportText = result.report;
        if (typeof reportText !== 'string') fail('web-result-report');
        const report = JSON.parse(reportText);
        const transfer = [...new Set([proof.buffer, ...(outputs ? [outputs.buffer] : [])])];
        // Retain the Rust result/guards through getter copies and successful
        // transferable publication. postMessage does not guarantee receipt.
        scope.postMessage({ id, generation, milliseconds, proof, outputs, reportText, report }, transfer);
      } finally {
        result.free();
      }
    } catch (error) {
      fatal ||= error instanceof WebAssembly.RuntimeError || error instanceof TypeError || error instanceof RangeError;
      const refusal = sdkRefusal(error);
      try { scope.postMessage({ id, generation: replyGeneration, error: refusal?.code ?? String(error),
        ...(refusal ? { refusal } : {}), fatal }); }
      catch (publicationError) { fatal = true; throw publicationError; }
      finally { if (fatal) close(); }
    } finally {
      if (ownsBusy) busy = false;
    }
  };
}
