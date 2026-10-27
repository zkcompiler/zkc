// One ordinary module per Worker. No shared memory or browser thread pool.
import init, { ProofSession } from './pkg/zkc_web.js';
const ready = init();
let session;
let terminated = false;
// Validate every argument before entering glue: a late JS conversion exception
// can strand earlier Wasm argument allocations before Rust takes ownership.
function bytes(value, name) {
  if (!(value instanceof Uint8Array) ||
      (typeof SharedArrayBuffer !== 'undefined' && value.buffer instanceof SharedArrayBuffer)) {
    throw new Error(`web-message-bytes: ${name}`);
  }
  return value;
}
self.onmessage = async ({ data }) => {
  let id;
  try {
    if (!data || typeof data !== 'object' || Array.isArray(data)) throw new Error('web-message');
    // Echo only primitive correlation IDs; transferred objects may not be
    // cloneable in replies, including the reply reporting a Wasm trap.
    if (typeof data.id !== 'string' && !Number.isSafeInteger(data.id)) throw new Error('web-message-id');
    id = data.id;
    const { operation } = data;
    await ready;
    // Other messages may already be awaiting module initialization when a
    // fatal call closes the Worker. Their continuations must not enter Rust.
    if (terminated) return;
    if (operation === 'admit') {
      if (session) throw new Error('web-session-active');
      // pin and authority are application configuration, independent of package.
      const packageBytes = bytes(data.package, 'package');
      const pin = bytes(data.pin, 'pin');
      const authority = bytes(data.authority ?? new Uint8Array(), 'authority');
      const options = JSON.stringify(data.options ?? {});
      session = new ProofSession(packageBytes, pin, options, authority);
      self.postMessage({ id, description: JSON.parse(session.describe()) });
      return;
    }
    if (!session) throw new Error('web-session-missing');
    if (operation === 'setup') {
      if (typeof data.slot !== 'string') throw new Error('web-message-slot');
      session.setSetup(data.slot, bytes(data.material, 'material'));
      self.postMessage({ id });
      return;
    }
    if (operation === 'dispose') {
      session.dispose();
      session.free();
      session = undefined;
      self.postMessage({ id });
      return;
    }
    let budget;
    if (data.budget != null) {
      if (!['number', 'bigint', 'string'].includes(typeof data.budget)) throw new Error('web-budget');
      if (typeof data.budget === 'number' && !Number.isSafeInteger(data.budget)) {
        throw new Error('web-budget');
      }
      budget = BigInt(data.budget);
      if (budget < 0n || budget > 0xffffffffffffffffn) throw new Error('web-budget');
    }
    const context = bytes(data.context ?? new Uint8Array(), 'context');
    const publicBytes = bytes(data.public, 'public');
    const operand = operation === 'prove' ? bytes(data.witness, 'witness') :
      operation === 'verify' ? bytes(data.proof, 'proof') : undefined;
    const start = performance.now();
    let result;
    if (operation === 'prove') {
      result = session.prove(publicBytes, operand, context, budget);
    } else if (operation === 'verify') {
      result = session.verify(publicBytes, operand, context, budget);
    } else {
      throw new Error('web-operation');
    }
    try {
      const milliseconds = performance.now() - start;
      const proof = result.proof;
      const outputs = result.outputs;
      const reportText = result.report;
      self.postMessage({ id, milliseconds, proof, outputs, reportText,
        report: JSON.parse(reportText) }, [proof.buffer, ...(outputs ? [outputs.buffer] : [])]);
    } finally {
      result.free();
    }
  } catch (error) {
    const fatal = error instanceof WebAssembly.RuntimeError || error instanceof TypeError || error instanceof RangeError;
    if (fatal) terminated = true;
    try {
      self.postMessage({ id, error: String(error), fatal });
    } finally {
      // An abort/trap gives no Rust rollback guarantee. Discard this Worker
      // even when reporting the failure itself throws.
      if (fatal) self.close();
    }
  }
};
