import { installWorker } from '../../../crates/zkc-web/web/worker-runtime.mjs';

export const compiledModule = new WebAssembly.Module(new Uint8Array([0, 97, 115, 109, 1, 0, 0, 0]));
export const admission = () => ({ package: new Uint8Array([1, 2]), pin: new Uint8Array(32) });
export const proving = () => ({ public: new Uint8Array([3]), witness: new Uint8Array([4]) });
export const admissionTimings = { package_capture_ms: 1.25, package_admit_ms: 2.5 };
export const reportTimings = { memory_preflight_ms: 3, execute_cleanup_ms: 4.5,
  output_encode_ms: 0.5, diagnostics_ms: 0.25 };
export const turn = () => new Promise(resolve => setImmediate(resolve));

// A real structured clone/transfer boundary with the shipped Worker state
// machine and an injected synchronous Wasm adapter, without a browser or glue.
export class FakeWorker {
  constructor(config = {}) {
    this.config = config;
    this.listeners = new Map();
    this.messages = [];
    this.held = [];
    this.replies = [];
    this.events = [];
    this.calls = 0;
    this.free = 0;
    this.terminated = false;
    this.closed = false;
    const owner = this;
    class ProofSession {
      constructor(...args) {
        owner.arguments = args;
        owner.events.push('admit');
        if (config.admissionError) throw 'package-refused';
      }
      describe() { return '{"fixture":true}'; }
      get timings() {
        owner.events.push('timings');
        if (config.timingsError) throw new Error('injected timings getter failure');
        return Object.hasOwn(config, 'timings') ? config.timings : JSON.stringify(admissionTimings);
      }
      setSetup(slot, material) { owner.setup = [slot, material.slice()]; }
      setInput(name, material) {
        owner.input = [name, material.slice()];
        if (config.inputError) throw 'web-setup-limit';
      }
      dispose() { owner.events.push('dispose'); }
      free() { owner.events.push('session.free'); }
      prove(...args) {
        owner.calls++;
        owner.callArguments = args;
        owner.events.push('call');
        if (config.trap) throw new WebAssembly.RuntimeError('injected trap');
        if (config.abortError) throw new Error('injected import abort');
        if (config.sdkError) throw 'entry-request-format: public';
        if (config.structuredError) throw JSON.stringify({ sdk_refusal: config.structuredError });
        return {
          get proof() {
            owner.events.push('proof');
            if (config.getterError) throw new Error('injected getter failure');
            return new Uint8Array(config.resultBytes ?? [5, 6]);
          },
          get outputs() { owner.events.push('outputs'); return new Uint8Array([7]); },
          get report() {
            owner.events.push('report');
            return config.badReport ? '{' : '{"success":true,"accepted":true,"count":18446744073709551615,"timings":' + JSON.stringify(reportTimings) + '}';
          },
          free() {
            owner.free++;
            owner.events.push('result.free');
            if (config.freeTrap) throw new WebAssembly.RuntimeError('injected free trap');
          },
        };
      }
      verify(...args) { return this.prove(...args); }
    }
    this.scope = {
      postMessage(data, transfer = []) {
        if ((config.failReply && data.error) || (config.failResult && data.proof)) {
          throw new DOMException('injected reply failure', 'DataCloneError');
        }
        owner.events.push(data.proof ? 'publish' : 'reply');
        const clone = structuredClone(data, { transfer });
        owner.replies.push(clone);
        const operation = owner.messages.find(m => m.id === data.id)?.operation;
        if (config.dropReplies?.has(operation)) return;
        queueMicrotask(() => { if (!owner.terminated) owner.emit('message', { data: clone }); });
      },
      close() { owner.closed = true; owner.events.push('close'); },
    };
    installWorker(this.scope, {
      simd: () => config.simd ?? true,
      load: async (variant, module) => {
        this.loaded = { variant, module };
        if (config.loadError) throw new Error('injected module load failure');
        if (config.loadGate) await config.loadGate;
        return { ProofSession, module: module ?? compiledModule };
      },
      now: () => 1,
    });
  }
  addEventListener(type, listener) {
    if (!this.listeners.has(type)) this.listeners.set(type, new Set());
    this.listeners.get(type).add(listener);
  }
  removeEventListener(type, listener) { this.listeners.get(type)?.delete(listener); }
  emit(type, event = {}) { for (const listener of [...(this.listeners.get(type) ?? [])]) listener(event); }
  postMessage(data, transfer = []) {
    if (this.config.failSend && data.operation === 'prove') throw new DOMException('send failure', 'DataCloneError');
    const clone = structuredClone(data, { transfer });
    this.messages.push(clone);
    if (this.config.hold?.has(clone.operation)) this.held.push(clone);
    else queueMicrotask(() => this.dispatch(clone));
  }
  async dispatch(data) {
    if (this.closed || this.terminated) return;
    try { await this.scope.onmessage({ data }); }
    catch (error) { if (!this.terminated) this.emit('error', { message: String(error) }); }
  }
  async release() { const held = this.held.splice(0); for (const data of held) await this.dispatch(data); }
  terminate() { this.terminated = true; this.events.push('terminate'); }
}
