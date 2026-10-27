// Browser adapter for the common benchmark harness. Mirrors the pinned tool and
// local HTTP conventions of common/tests/browser/roundtrip.mjs; no downloads.
import assert from 'node:assert/strict';
import { readFile, writeFile, mkdir, copyFile } from 'node:fs/promises';
import { createServer } from 'node:http';
import { dirname, extname, resolve, sep } from 'node:path';
import { pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';

const [requestPath, repetitionText] = process.argv.slice(2);
const request = JSON.parse(await readFile(requestPath, 'utf8'));
const repetition = Number(repetitionText);
const playwrightVersion = JSON.parse(await readFile(resolve(dirname(request.playwright), 'package.json'), 'utf8')).version;
assert.equal(playwrightVersion, '1.64.1', 'use the documented browser driver pin');
const { chromium } = await import(pathToFileURL(request.playwright));
const files = new Map();
const cases = [];
for (const [i, candidate] of request.cases.entries()) {
  const input = { ...candidate };
  const url = (file, key) => {
    if (!file) return null;
    const path = `/fixture/${i}/${key}`;
    files.set(path, file);
    return path;
  };
  input.package = url(candidate.package, 'package');
  input.authority = url(candidate.authority, 'authority');
  input.expected_outputs = candidate.expected_outputs ? JSON.parse(await readFile(candidate.expected_outputs, 'utf8')) : null;
  input.inputs = candidate.inputs.map((s, j) => ({ public: url(s.public, `public-${j}`), witness: url(s.witness, `witness-${j}`) }));
  input.setups = candidate.setups.map((s, j) => ({ slot: s.slot, path: url(s.path, `setup-${j}`) }));
  input.bindings = candidate.bindings.map((s, j) => ({ name: s.name, path: url(s.path, `binding-${j}`) }));
  cases.push(input);
}
const root = resolve(request.web);
const server = createServer(async (req, res) => {
  try {
    const pathname = new URL(req.url, 'http://localhost').pathname;
    if (pathname === '/') {
      res.setHeader('Content-Type', 'text/html'); res.end('<!doctype html><title>zkc benchmark</title>'); return;
    }
    const file = files.get(pathname) ?? resolve(root, '.' + pathname);
    if (!files.has(pathname) && !file.startsWith(root + sep)) throw new Error('path');
    const bytes = await readFile(file);
    res.setHeader('Content-Type', { '.js': 'text/javascript', '.mjs': 'text/javascript', '.wasm': 'application/wasm' }[extname(file)] ?? 'application/octet-stream');
    res.setHeader('Cache-Control', 'no-store'); res.end(bytes);
  } catch { res.writeHead(404); res.end(); }
});
await new Promise(r => server.listen(0, '127.0.0.1', r));
let browser;
try {
  browser = await chromium.launch({ headless: true });
  const page = await browser.newPage();
  page.setDefaultTimeout(request.timeout_ms);
  await page.goto(`http://127.0.0.1:${server.address().port}/`);
  const timerFloor = await page.evaluate(() => {
    let previous = performance.now();
    let floor = Infinity;
    for (let i = 0; i < 10000; i++) {
      const current = performance.now();
      if (current > previous) floor = Math.min(floor, current - previous);
      previous = current;
    }
    return Number.isFinite(floor) ? floor : null;
  });
  const report = { format: 'zkc.browser-worker/0', status: 'passed', browser: browser.version(),
    playwright: playwrightVersion, observed_page_timer_increment_ms: timerFloor, transport: request.transport, variants: request.variants, modules: [], cases: [], native: [] };
  // A separate page per glue module keeps wasm-bindgen's initialization cache
  // from making a second variant's startup measurement a no-op.
  for (const variant of request.variants) {
    const modulePage = await browser.newPage();
    await modulePage.goto(`http://127.0.0.1:${server.address().port}/`);
    report.modules.push(await modulePage.evaluate(async variant => {
      const { supportsSimd } = await import('/protocol.mjs');
      if (variant === 'simd' && !supportsSimd()) throw new Error('web-simd-unavailable');
      const path = variant === 'simd' ? '/pkg-simd/' : '/pkg/';
      const startFetch = performance.now();
      const response = await fetch(path + 'zkc_web_bg.wasm');
      if (!response.ok) throw new Error('module fetch');
      const bytes = await response.arrayBuffer();
      const fetch_ms = performance.now() - startFetch;
      const startCompile = performance.now();
      const module = await WebAssembly.compile(bytes);
      const compile_ms = performance.now() - startCompile;
      const binding = await import(path + 'zkc_web.js');
      const instantiate = WebAssembly.instantiate;
      let instantiate_api_ms = null;
      WebAssembly.instantiate = async (...args) => {
        const start = performance.now();
        const result = await instantiate(...args);
        instantiate_api_ms = performance.now() - start;
        return result;
      };
      const startInitialize = performance.now();
      try { await binding.default({ module_or_path: module }); }
      finally { WebAssembly.instantiate = instantiate; }
      const glue_initialize_ms = performance.now() - startInitialize;
      return { variant, bytes: bytes.byteLength, fetch_ms, compile_ms, glue_initialize_ms, instantiate_api_ms,
        cross_origin_isolated: crossOriginIsolated };
    }, variant));
    await modulePage.close();
  }
  const payloads = await page.evaluate(async ({ cases, variants, plan, timeout, transport }) => {
    const { ProofClient } = await import('/client.mjs');
    const get = async url => {
      if (!url) return new Uint8Array();
      const response = await fetch(url);
      if (!response.ok) throw new Error('fixture fetch');
      return new Uint8Array(await response.arrayBuffer());
    };
    const hash = async bytes => Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256', bytes)), x => x.toString(16).padStart(2, '0')).join('');
    const outputJSON = bytes => JSON.parse(new TextDecoder().decode(bytes));
    const same = (a, b) => {
      const canonical = v => Array.isArray(v) ? v.map(canonical) : v && typeof v === 'object'
        ? Object.fromEntries(Object.keys(v).sort().map(k => [k, canonical(v[k])])) : v;
      return JSON.stringify(canonical(a)) === JSON.stringify(canonical(b));
    };
    const result = { cases: [], proofs: [], transfer_probes: [] };
    for (const size of [0, 32768, 1048576]) {
      const channel = new MessageChannel();
      channel.port2.onmessage = ({ data }) => channel.port2.postMessage(data, [data.buffer]);
      const values = [];
      for (let i = 0; i < 5; i++) {
        const value = new Uint8Array(size);
        const start = performance.now();
        await new Promise(resolve => {
          channel.port1.onmessage = () => resolve();
          channel.port1.postMessage(value, [value.buffer]);
        });
        values.push(performance.now() - start);
      }
      channel.port1.close(); channel.port2.close();
      result.transfer_probes.push({ bytes: size, roundtrip_ms: values });
    }
    // Keep fetch/compile outside every Worker-ready interval, including the
    // first case. Module API timings above use separate uncached glue pages.
    const modules = new Map();
    for (const variant of variants) {
      const path = variant === 'simd' ? '/pkg-simd/' : '/pkg/';
      modules.set(variant, await WebAssembly.compile(await get(path + 'zkc_web_bg.wasm')));
    }
    const usedModules = new Set();
    for (const candidate of cases) {
      const pkg = await get(candidate.package);
      const pin = Uint8Array.from(candidate.pin.match(/../g), x => parseInt(x, 16));
      const authority = await get(candidate.authority);
      const inputs = await Promise.all(candidate.inputs.map(async s => ({ public: await get(s.public), witness: await get(s.witness) })));
      const setups = await Promise.all(candidate.setups.map(async s => ({ slot: s.slot, material: await get(s.path) })));
      const bindings = await Promise.all(candidate.bindings.map(async b => ({ name: b.name, material: await get(b.path) })));
      const baseline = new Map();
      const previousProofs = new Map();
      for (const variant of variants) {
        const start = performance.now();
        const client = new ProofClient({ variant, compiledModule: modules.get(variant), timeoutMs: timeout });
        const row = { name: candidate.name, variant, pin: candidate.pin, providers: candidate.options.providers,
          module_reused: usedModules.has(variant), calls: [], setup_roundtrip_ms: [], checks: {} };
        try {
          await client.ready;
          row.worker_ready_ms = performance.now() - start;
          usedModules.add(variant);
          const beginAdmit = performance.now();
          const admitted = await client.admit({ package: pkg, pin, authority, options: candidate.options });
          row.admit_roundtrip_ms = performance.now() - beginAdmit;
          row.description = admitted.description;
          row.sdk_admission_ms = admitted.timings ?? null;
          for (const setup of setups) {
            const beginSetup = performance.now();
            await client.setSetup(setup.slot, setup.material);
            row.setup_roundtrip_ms.push({ slot: setup.slot, milliseconds: performance.now() - beginSetup });
          }
          for (const b of bindings) await client.setInput(b.name, b.material);
          let outputsMatch = true;
          for (let cycle = 0; cycle < plan.samples + plan.warmups; cycle++) {
            for (const [index, input] of inputs.entries()) {
              let proof;
              for (const operation of ['prove', 'verify']) {
                const beginCall = performance.now();
                const consume = transport === 'consume';
                const publicBytes = consume ? input.public.slice() : input.public;
                const operand = consume ? (operation === 'prove' ? input.witness : proof).slice()
                  : (operation === 'prove' ? input.witness : proof);
                const reply = operation === 'prove'
                  ? await client.prove({ public: publicBytes, witness: operand }, { consume })
                  : await client.verify({ public: publicBytes, proof: operand }, { consume });
                const end_to_end_ms = performance.now() - beginCall;
                if (reply.report?.success !== true || (operation === 'verify' && reply.report?.accepted !== true)) {
                  throw new Error(JSON.stringify({ name: candidate.name, operation, report: reply.report }));
                }
                if (!(reply.outputs instanceof Uint8Array)) throw new Error('missing outputs');
                const outputs = outputJSON(reply.outputs);
                const key = `${operation}/${index}`;
                if (!baseline.has(key)) baseline.set(key, outputs);
                outputsMatch &&= same(outputs, baseline.get(key));
                if (candidate.expected_outputs && operation === 'verify') outputsMatch &&= same(outputs, candidate.expected_outputs);
                if (!outputsMatch) throw new Error(`outputs differ: ${candidate.name}/${key}`);
                const record = { operation, input_index: index, cycle,
                  phase: cycle < plan.warmups ? 'warmup' : 'sample', end_to_end_ms,
                  worker_call_ms: reply.milliseconds, outside_worker_call_ms: end_to_end_ms - reply.milliseconds,
                  success: reply.report.success, accepted: reply.report.accepted,
                  outputs_sha256: await hash(reply.outputs), outputs_bytes: reply.outputs.length,
                  proof_bytes: reply.proof.length, report_text: reply.reportText, sdk_phases_ms: reply.report.timings ?? null };
                row.calls.push(record);
                if (operation === 'prove') {
                  proof = reply.proof;
                  if (cycle === 0) {
                    previousProofs.set(`${variant}/${index}`, proof);
                    result.proofs.push({ name: candidate.name, variant, input_index: index, proof: Array.from(proof) });
                  }
                }
              }
            }
          }
          row.checks.outputs_match = outputsMatch;
          // The later variant verifies the earlier proofs; the earlier variant
          // is checked in a fresh session below after both proof sets exist.
          for (const [key, proof] of previousProofs) {
            const [other, index] = key.split('/');
            if (other === variant) continue;
            const reply = await client.verify({ public: inputs[Number(index)].public, proof });
            if (reply.report?.accepted !== true) throw new Error('variant cross-verification refused');
          }
          row.checks.cross_variant_verified = variants.length > 1;
          result.cases.push(row);
        } finally { client.dispose(); }
      }
      if (variants.length > 1) {
        const variant = variants[0];
        const client = new ProofClient({ variant, compiledModule: modules.get(variant), timeoutMs: timeout });
        try {
          await client.ready;
          await client.admit({ package: pkg, pin, authority, options: candidate.options });
          for (const s of setups) await client.setSetup(s.slot, s.material);
          for (const b of bindings) await client.setInput(b.name, b.material);
          for (const [key, proof] of previousProofs) {
            const [other, index] = key.split('/');
            if (other === variant) continue;
            const reply = await client.verify({ public: inputs[Number(index)].public, proof });
            if (reply.report?.accepted !== true) throw new Error('reverse variant cross-verification refused');
          }
        } finally { client.dispose(); }
      }
    }
    return result;
  }, { cases, variants: request.variants, plan: request.plan, timeout: request.timeout_ms, transport: request.transport });
  report.cases = payloads.cases;
  report.transfer_probes = payloads.transfer_probes;
  report.proofs = [];
  for (const proof of payloads.proofs) {
    const path = resolve(request.output, 'proofs', String(repetition), proof.name, proof.variant, String(proof.input_index));
    await mkdir(path, { recursive: true });
    const proofBytes = new Uint8Array(proof.proof);
    await writeFile(resolve(path, 'browser.proof'), proofBytes);
    report.proofs.push({ name: proof.name, variant: proof.variant, input_index: proof.input_index, path: resolve(path, 'browser.proof'),
      bytes: proofBytes.length, sha256: createHash('sha256').update(proofBytes).digest('hex') });
    if (request.native_example) {
      const candidate = request.cases.find(c => c.name === proof.name);
      await writeFile(resolve(path, 'options.json'), JSON.stringify(candidate.options));
      if (candidate.authority) await copyFile(candidate.authority, resolve(path, 'authority.json'));
      const setupFiles = [];
      for (const [i, setup] of candidate.setups.entries()) {
        await copyFile(setup.path, resolve(path, `setup-${i}.bin`));
        setupFiles.push({ slot: setup.slot, path: `setup-${i}.bin` });
      }
      await writeFile(resolve(path, 'setups.json'), JSON.stringify(setupFiles));
      const inputFiles = [];
      for (const [i, binding] of candidate.bindings.entries()) {
        await copyFile(binding.path, resolve(path, `input-${i}.bin`));
        inputFiles.push({ name: binding.name, path: `input-${i}.bin` });
      }
      await writeFile(resolve(path, 'inputs.json'), JSON.stringify(inputFiles));
      await copyFile(candidate.package, resolve(path, 'entry.zkpkg'));
      await copyFile(candidate.inputs[proof.input_index].public, resolve(path, 'public.json'));
      await copyFile(candidate.inputs[proof.input_index].witness, resolve(path, 'witness.json'));
      const native = JSON.parse(execFileSync(request.native_example, [path, candidate.pin, path], { encoding: 'utf8', timeout: request.timeout_ms }));
      assert.equal(native.prove.success, true);
      assert.equal(native.verify.accepted, true);
      assert.equal(JSON.parse(native.browser_cross_verify).accepted, true);
      const nativeProof = Array.from(await readFile(resolve(path, 'native.proof')));
      const checked = await page.evaluate(async ({ candidate, variant, proof }) => {
        const { ProofClient } = await import('/client.mjs');
        const get = async file => new Uint8Array(await (await fetch(file)).arrayBuffer());
        const client = new ProofClient({ variant });
        try {
          await client.ready;
          await client.admit({ package: await get(candidate.package), pin: Uint8Array.from(candidate.pin.match(/../g), h => parseInt(h, 16)), options: candidate.options, authority: candidate.authority ? await get(candidate.authority) : new Uint8Array() });
          for (const s of candidate.setups) await client.setSetup(s.slot, await get(s.path));
          for (const b of candidate.bindings) await client.setInput(b.name, await get(b.path));
          const reply = await client.verify({ public: await get(candidate.inputs[proof.input_index].public), proof: new Uint8Array(proof.bytes) });
          return reply.report;
        } finally { client.dispose(); }
      }, { candidate: cases.find(c => c.name === proof.name), variant: proof.variant, proof: { input_index: proof.input_index, bytes: nativeProof } });
      assert.equal(checked.accepted, true);
      report.native.push({ name: proof.name, variant: proof.variant, input_index: proof.input_index, report: native, cross_verified: true });
    }
  }
  console.log(JSON.stringify(report));
} finally {
  if (browser) await browser.close();
  await new Promise(resolve => server.close(resolve));
}
