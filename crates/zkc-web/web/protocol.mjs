// Transport checks precede every wasm-bindgen call. Semantic input, authority,
// capacity and provider support checks remain in the shared SDK.
export const WASM32_MAX = 0xffffffff;
const U64_MAX = 0xffffffffffffffffn;
const providers = new Set(['arkworks', 'blst', 'dalek', 'halo2curves', 'plonky3']);
const typedArrayPrototype = Object.getPrototypeOf(Uint8Array.prototype);
const typedArrayBuffer = Object.getOwnPropertyDescriptor(typedArrayPrototype, 'buffer').get;
const typedArrayOffset = Object.getOwnPropertyDescriptor(typedArrayPrototype, 'byteOffset').get;
const typedArrayLength = Object.getOwnPropertyDescriptor(typedArrayPrototype, 'byteLength').get;

export function fail(code) { throw new Error(code); }

export function record(value, allowed, code = 'web-message') {
  if (!value || typeof value !== 'object' || Array.isArray(value) ||
      ![Object.prototype, null].includes(Object.getPrototypeOf(value))) fail(code);
  for (const key of Reflect.ownKeys(value)) {
    if (typeof key !== 'string' || !allowed.includes(key) ||
        !Object.hasOwn(Object.getOwnPropertyDescriptor(value, key), 'value')) fail(code);
  }
  return value;
}

export function u64(value, code = 'web-budget') {
  if (!(typeof value === 'bigint' ||
        (typeof value === 'number' && Number.isSafeInteger(value)) ||
        (typeof value === 'string' && /^(0|[1-9][0-9]*)$/.test(value) && value.length <= 20))) fail(code);
  const result = BigInt(value);
  if (result < 0n || result > U64_MAX) fail(code);
  return result;
}

function size(value, code) {
  const result = u64(value, code);
  if (result > BigInt(WASM32_MAX)) fail(code);
  return Number(result);
}

function text(value, name) {
  // Bound control metadata independently of pending binary payloads.
  if (typeof value !== 'string' || value.length > 4096) fail(`web-message-string: ${name}`);
  return value;
}

export function bytes(value, name) {
  if (!(value instanceof Uint8Array)) fail(`web-message-bytes: ${name}`);
  try {
    // Reject detached buffers, including detached empty views. A plain view
    // and intrinsic getters keep caller overrides out of normalization/glue.
    const buffer = typedArrayBuffer.call(value);
    if (!(buffer instanceof ArrayBuffer)) fail(`web-message-bytes: ${name}`);
    const view = new Uint8Array(buffer, typedArrayOffset.call(value), typedArrayLength.call(value));
    if (view.byteLength > WASM32_MAX) fail(`web-wasm32-size: ${name}`);
    return view;
  } catch { fail(`web-message-bytes: ${name}`); }
}

function dataArray(value, code, expectedLength) {
  if (!Array.isArray(value)) fail(code);
  const length = Object.getOwnPropertyDescriptor(value, 'length').value;
  if (expectedLength !== undefined && length !== expectedLength) fail(code);
  const out = [];
  for (let i = 0; i < length; i++) {
    const item = Object.getOwnPropertyDescriptor(value, String(i));
    if (!item || !Object.hasOwn(item, 'value')) fail(code);
    out.push(item.value);
  }
  return out;
}

function capacity(value) {
  value = dataArray(value, 'web-options-capacity', 7);
  if (value[0] !== 'zkc.native-capacity/0') fail('web-options-capacity');
  const work = dataArray(value[5], 'web-options-capacity', 3);
  const sizes = dataArray(value[6], 'web-options-capacity', 2);
  const natural = (v, wasm32) => {
    if (typeof v !== 'string') fail('web-options-capacity');
    return (wasm32 ? BigInt(size(v, 'web-wasm32-capacity')) : u64(v, 'web-options-capacity')).toString();
  };
  return [value[0], ...value.slice(1, 5).map(v => natural(v, true)),
    work.map(v => natural(v, false)), sizes.map(v => natural(v, true))];
}

export function options(value = {}) {
  record(value, ['capacity', 'package_bytes', 'allow_authored', 'operation', 'external_work', 'providers'], 'web-options');
  const out = {};
  for (const [key, v] of Object.entries(value)) {
    if (key === 'capacity') out[key] = capacity(v);
    if (key === 'package_bytes') out[key] = size(v, 'web-wasm32-package-bytes');
    if (key === 'external_work') out[key] = u64(v, 'web-options-external-work');
    if (key === 'allow_authored') {
      if (typeof v !== 'boolean') fail('web-options');
      out[key] = v;
    }
    if (key === 'operation') {
      if (!['both', 'prove', 'verify'].includes(v)) fail('web-options');
      out[key] = v;
    }
    if (key === 'providers') {
      const names = dataArray(v, 'web-options-providers');
      if (names.some(p => !providers.has(p))) fail('web-options-providers');
      out[key] = [...new Set(names)].sort();
    }
  }
  return out;
}

export function optionsJSON(value) {
  const normalized = options(value);
  // external_work is a JSON u64 number for serde, never a rounded JS number.
  const json = '{' + Object.entries(normalized).map(([k, v]) =>
    JSON.stringify(k) + ':' + (typeof v === 'bigint' ? v.toString() : JSON.stringify(v))).join(',') + '}';
  if (new TextEncoder().encode(json).length > 65536) fail('web-options-limit');
  return json;
}

const fields = {
  initialize: ['variant', 'module'],
  admit: ['package', 'pin', 'authority', 'options'],
  setup: ['slot', 'material'],
  input: ['name', 'material'],
  prove: ['public', 'witness', 'context', 'budget'],
  verify: ['public', 'proof', 'context', 'budget'],
  dispose: [],
};

export function request(operation, value = {}) {
  if (!Object.hasOwn(fields, operation)) fail('web-operation');
  record(value, fields[operation]);
  const out = { operation };
  if (operation === 'initialize') {
    out.variant = value.variant === undefined ? 'portable' : value.variant;
    if (!['portable', 'simd', 'auto'].includes(out.variant)) fail('web-variant');
    if (value.module !== undefined) {
      if (!(value.module instanceof WebAssembly.Module) || out.variant === 'auto') fail('web-module');
      out.module = value.module;
    }
  } else if (operation === 'admit') {
    out.package = bytes(value.package, 'package');
    out.pin = bytes(value.pin, 'pin');
    out.authority = bytes(value.authority === undefined ? new Uint8Array() : value.authority, 'authority');
    out.options = options(value.options);
    optionsJSON(out.options);
  } else if (operation === 'setup' || operation === 'input') {
    const key = operation === 'setup' ? 'slot' : 'name';
    out[key] = text(value[key], key);
    out.material = bytes(value.material, 'material');
  } else if (operation === 'prove' || operation === 'verify') {
    out.public = bytes(value.public, 'public');
    const operand = operation === 'prove' ? 'witness' : 'proof';
    out[operand] = bytes(value[operand], operand);
    out.context = bytes(value.context === undefined ? new Uint8Array() : value.context, 'context');
    if (value.budget !== undefined) out.budget = u64(value.budget);
  }
  let total = 0;
  for (const v of Object.values(out)) if (v instanceof Uint8Array) total += v.byteLength;
  if (out.slot !== undefined) total += new TextEncoder().encode(out.slot).length;
  if (out.name !== undefined) total += new TextEncoder().encode(out.name).length;
  if (out.options) total += new TextEncoder().encode(optionsJSON(out.options)).length;
  if (total > WASM32_MAX) fail('web-wasm32-arguments');
  return out;
}

export function envelope(value) {
  if (!value || typeof value !== 'object' || Array.isArray(value)) fail('web-message');
  if (!Number.isSafeInteger(value.id) || value.id < 1) fail('web-message-id');
  if (!Number.isSafeInteger(value.generation) || value.generation < 1) fail('web-message-generation');
  const { id, generation, operation, ...args } = value;
  return { id, generation, ...request(operation, args) };
}

export function buffers(value) {
  return [...new Set(Object.values(value).filter(v => v instanceof Uint8Array).map(v => v.buffer))];
}

export function supportsSimd() {
  // A complete module containing v128.const followed by drop.
  return WebAssembly.validate(new Uint8Array([
    0, 97, 115, 109, 1, 0, 0, 0, 1, 4, 1, 96, 0, 0,
    3, 2, 1, 0, 10, 23, 1, 21, 0, 253, 12, ...Array(16).fill(0), 26, 11,
  ]));
}

// Correlation alone cannot turn a malformed successful reply into completion.
// These are transport checks, not a replacement for report.success/accepted.
export function checkReply(value, operation) {
  if (operation === 'admit') {
    if (!value.description || typeof value.description !== 'object') fail('web-client-protocol');
    const times = value.timings;
    if (!times || ['package_capture_ms', 'package_admit_ms'].some(key =>
      typeof times[key] !== 'number' || !Number.isFinite(times[key]) || times[key] < 0)) fail('web-client-protocol');
  }
  if (operation === 'prove' || operation === 'verify') {
    bytes(value.proof, 'result.proof');
    if (value.outputs !== undefined) bytes(value.outputs, 'result.outputs');
    if (typeof value.milliseconds !== 'number' || !Number.isFinite(value.milliseconds) || value.milliseconds < 0 ||
        typeof value.reportText !== 'string' || !value.report || typeof value.report.success !== 'boolean' ||
        ![null, true, false].includes(value.report.accepted)) fail('web-client-protocol');
  }
}


// Rust's stable string-error ABI carries the SDK's structured boundary details.
// Other strings remain ordinary refusals; a JS exception is still a fatal trap.
export function sdkRefusal(error) {
  if (typeof error !== 'string' || !error.startsWith('{')) return undefined;
  try {
    const envelope = JSON.parse(error);
    record(envelope, ['sdk_refusal']);
    const refusal = record(envelope.sdk_refusal, ['code', 'phase', 'path']);
    if (typeof refusal.code !== 'string' || !['package', 'interface', 'authority', 'admission',
      'binding', 'assets', 'request', 'preparation'].includes(refusal.phase) ||
      !(refusal.path === null || typeof refusal.path === 'string')) return undefined;
    return refusal;
  } catch { return undefined; }
}
