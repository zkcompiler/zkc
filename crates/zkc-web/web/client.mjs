import { buffers, checkReply, record, request } from './protocol.mjs';

const signalAborted = Object.getOwnPropertyDescriptor(AbortSignal.prototype, 'aborted').get;
const addListener = EventTarget.prototype.addEventListener;
const removeListener = EventTarget.prototype.removeEventListener;
const bufferLength = Object.getOwnPropertyDescriptor(ArrayBuffer.prototype, 'byteLength').get;

export class ProofClientError extends Error {
  constructor(code, { fatal = false, completion = 'not-started', refusal } = {}) {
    super(code);
    this.name = 'ProofClientError';
    this.code = code;
    this.fatal = fatal;
    this.completion = completion;
    if (refusal) { this.refusal = refusal; this.phase = refusal.phase; this.path = refusal.path; }
  }
}

function positive(value, name, zero = false) {
  if (!Number.isSafeInteger(value) || value < (zero ? 0 : 1)) throw new ProofClientError(name);
  return value;
}

// Queue ownership, request deadlines and session lifetime belong to this client.
// No protocol call is retried, including after a lost delivery or recycling.
export class ProofClient {
  #factory;
  #url;
  #variant;
  #module;
  #worker;
  #listeners;
  #generation = 0;
  #nextId = 0;
  #queue = [];
  #active;
  #retainedBytes = 0;
  #maxQueue;
  #maxPendingBytes;
  #timeoutMs;
  #closed = true;
  #disposed = false;
  #ready;

  constructor({ workerURL = new URL('./worker.js', import.meta.url), variant = 'portable',
    compiledModule, maxQueue = 8, maxPendingBytes = 64 * 1024 * 1024,
    timeoutMs = 120000, workerFactory = url => new Worker(url, { type: 'module' }) } = {}) {
    request('initialize', { variant, module: compiledModule });
    this.#maxQueue = positive(maxQueue, 'web-client-queue-limit', true);
    this.#maxPendingBytes = positive(maxPendingBytes, 'web-client-byte-limit');
    this.#timeoutMs = positive(timeoutMs, 'web-client-timeout-limit');
    if (timeoutMs > 0x7fffffff) throw new ProofClientError('web-client-timeout-limit');
    if (typeof workerFactory !== 'function') throw new ProofClientError('web-client-worker-factory');
    this.#url = workerURL;
    this.#variant = variant;
    this.#module = compiledModule;
    this.#factory = workerFactory;
    this.#start();
  }

  get ready() { return this.#ready; }
  get generation() { return this.#generation; }
  get compiledModule() { return this.#module; }
  get variant() { return this.#variant; }

  admit(args, controls) { return this.#submit('admit', args, controls); }
  prove(args, controls) { return this.#submit('prove', args, controls); }
  verify(args, controls) { return this.#submit('verify', args, controls); }
  setSetup(slot, material, controls) { return this.#submit('setup', { slot, material }, controls); }
  setInput(name, material, controls) { return this.#submit('input', { name, material }, controls); }

  // Cooperative AbortSignal cancellation removes queued calls. An active call
  // finishes synchronously; its result is discarded and cancellation settles
  // only when its reply arrives. terminate() is the hard cancellation boundary.
  terminate() { this.#stop('web-client-terminated'); }

  dispose() {
    this.#disposed = true;
    this.#stop('web-client-disposed');
  }

  recycle() {
    if (this.#disposed) return Promise.reject(new ProofClientError('web-client-disposed'));
    if (this.#active || this.#queue.length) return Promise.reject(new ProofClientError('web-client-busy'));
    this.#stop('web-client-recycled');
    this.#start();
    return this.#ready;
  }

  #start() {
    this.#generation++;
    this.#closed = false;
    try {
      const worker = this.#factory(this.#url);
      this.#worker = worker;
      const receive = event => {
        if (worker === this.#worker) this.#receive(event.data);
      };
      const error = () => { if (worker === this.#worker) this.#stop('web-worker-error'); };
      const messageerror = () => { if (worker === this.#worker) this.#stop('web-worker-messageerror'); };
      this.#listeners = { message: receive, error, messageerror };
      for (const [type, listener] of Object.entries(this.#listeners)) worker.addEventListener(type, listener);
      this.#ready = this.#submit('initialize', { variant: this.#variant, module: this.#module });
    } catch (error) {
      this.#stop('web-worker-start');
      const failure = new ProofClientError('web-worker-start', { fatal: true });
      failure.cause = error;
      this.#ready = Promise.reject(failure);
    }
    // Construction starts initialization. Callers can await ready or immediately
    // queue admission; an unused ready promise must not leak an unhandled error.
    this.#ready.catch(() => {});
  }

  #submit(operation, args, controls = {}) {
    let call;
    let consume;
    let timeoutMs;
    let signal;
    let retained;
    try {
      if (this.#closed) throw new ProofClientError(this.#disposed ? 'web-client-disposed' : 'web-client-closed');
      record(controls, ['consume', 'timeoutMs', 'signal'], 'web-client-controls');
      consume = controls.consume === undefined ? false : controls.consume;
      if (typeof consume !== 'boolean') throw new ProofClientError('web-client-consume');
      timeoutMs = positive(controls.timeoutMs === undefined ? this.#timeoutMs : controls.timeoutMs, 'web-client-timeout-limit');
      if (timeoutMs > 0x7fffffff) throw new ProofClientError('web-client-timeout-limit');
      signal = controls.signal;
      if (signal !== undefined && !(signal instanceof AbortSignal)) throw new ProofClientError('web-client-signal');
      call = request(operation, args);
      retained = consume ? buffers(call).reduce((n, b) => n + bufferLength.call(b), 0)
        : Object.values(call).reduce((n, v) => n + (v instanceof Uint8Array ? v.byteLength : 0), 0);
      // Caller-associated normalization may reenter the client. Only inert
      // normalized values remain from here through ownership and acceptance.
      if (this.#closed) throw new ProofClientError(this.#disposed ? 'web-client-disposed' : 'web-client-closed');
      if (signal !== undefined && signalAborted.call(signal)) throw new ProofClientError('web-client-cancelled');
      if (this.#active && this.#queue.length >= this.#maxQueue) throw new ProofClientError('web-client-queue-full');
      if (this.#retainedBytes + retained > this.#maxPendingBytes) throw new ProofClientError('web-client-bytes-full');
      if (this.#nextId === Number.MAX_SAFE_INTEGER) throw new ProofClientError('web-client-id-exhausted');
      // Borrowed inputs are snapshots at enqueue, never detached. Consuming calls
      // transfer all backing buffers immediately, including subview aliases.
      if (!consume) {
        for (const [key, value] of Object.entries(call)) if (value instanceof Uint8Array) {
          const copy = new Uint8Array(value.byteLength);
          copy.set(value);
          call[key] = copy;
        }
      } else {
        call = structuredClone(call, { transfer: buffers(call) });
      }
    } catch (error) { return Promise.reject(error); }

    return new Promise((resolve, reject) => {
      const entry = { call: { ...call, id: ++this.#nextId, generation: this.#generation },
        resolve, reject, retained, signal, cancelled: false };
      entry.timer = setTimeout(() => {
        if (entry === this.#active) this.#stop('web-client-timeout');
        else {
          this.#queue.splice(this.#queue.indexOf(entry), 1);
          this.#settle(entry, new ProofClientError('web-client-timeout'));
        }
      }, timeoutMs);
      entry.abort = () => {
        if (entry === this.#active) entry.cancelled = true;
        else {
          this.#queue.splice(this.#queue.indexOf(entry), 1);
          this.#settle(entry, new ProofClientError('web-client-cancelled'));
        }
      };
      if (signal !== undefined) addListener.call(signal, 'abort', entry.abort, { once: true });
      this.#retainedBytes += retained;
      this.#queue.push(entry);
      this.#pump();
    });
  }

  #pump() {
    if (this.#closed || this.#active || !this.#queue.length) return;
    const entry = this.#active = this.#queue.shift();
    try {
      this.#worker.postMessage(entry.call, buffers(entry.call));
      // The Worker now owns input transport buffers. Keep the byte charge until
      // settlement, but drop JS references and bulk metadata from the client.
      entry.call = { id: entry.call.id, generation: entry.call.generation, operation: entry.call.operation };
    } catch { this.#stop('web-client-send'); }
  }

  #receive(data) {
    if (this.#closed) return;
    if (!data || typeof data !== 'object' || Array.isArray(data) ||
        !Number.isSafeInteger(data.generation)) return this.#stop('web-client-protocol');
    if (data.generation !== this.#generation) return;
    const active = this.#active;
    if (data.fatal === true) return this.#stop(typeof data.error === 'string' ? data.error : 'web-worker-fatal', data.id);
    if (!active || data.id !== active.call.id) return this.#stop('web-client-correlation');
    if (Object.hasOwn(data, 'error') && (typeof data.error !== 'string' || data.fatal !== false)) {
      return this.#stop('web-client-protocol');
    }
    if (!Object.hasOwn(data, 'error')) {
      try { checkReply(data, active.call.operation); }
      catch { return this.#stop('web-client-protocol'); }
    }
    if (!Object.hasOwn(data, 'error') && active.call.operation === 'initialize') {
      if (!(data.module instanceof WebAssembly.Module) || !['portable', 'simd'].includes(data.variant) ||
          (this.#variant !== 'auto' && this.#variant !== data.variant)) return this.#stop('web-client-protocol');
      this.#module = data.module;
      this.#variant = data.variant;
    }
    this.#active = undefined;
    const error = Object.hasOwn(data, 'error') ? new ProofClientError(data.error, { completion: 'known', refusal: data.refusal })
      : active.cancelled ? new ProofClientError('web-client-cancelled', { completion: 'known' }) : undefined;
    this.#settle(active, error, data);
    this.#pump();
  }

  #settle(entry, error, data) {
    clearTimeout(entry.timer);
    if (entry.signal !== undefined) removeListener.call(entry.signal, 'abort', entry.abort);
    this.#retainedBytes -= entry.retained;
    if (error) entry.reject(error); else entry.resolve(data);
  }

  #stop(code, knownId) {
    this.#closed = true;
    const worker = this.#worker;
    this.#worker = undefined;
    if (worker) {
      for (const [type, listener] of Object.entries(this.#listeners ?? {})) worker.removeEventListener(type, listener);
      try { worker.terminate(); } catch { /* Pending settlement still takes priority. */ }
    }
    const active = this.#active;
    this.#active = undefined;
    const queued = this.#queue.splice(0);
    if (active) this.#settle(active, new ProofClientError(code, {
      fatal: true, completion: active.call.id === knownId ? 'known' : 'unknown',
    }));
    for (const entry of queued) this.#settle(entry, new ProofClientError(code, { fatal: true }));
  }
}
