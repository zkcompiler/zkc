// Manual integration check. Tools are pinned by the invoking development shell;
// no browser or dependency download occurs here. See crates/zkc-web/README.md.
import assert from 'node:assert/strict';
import { readFile, writeFile } from 'node:fs/promises';
import { createServer } from 'node:http';
import { resolve, sep, extname, dirname } from 'node:path';
import { pathToFileURL } from 'node:url';
import { execFileSync } from 'node:child_process';
const [webDirectory, fixtureDirectory, nativeExample] = process.argv.slice(2);
const browserEngine = process.env.ZKC_BROWSER ?? 'chromium';
assert.ok(['chromium', 'firefox'].includes(browserEngine), 'ZKC_BROWSER must be chromium or firefox');
const variant = process.env.ZKC_WEB_VARIANT ?? 'portable';
assert.ok(['portable', 'simd'].includes(variant), 'ZKC_WEB_VARIANT must be portable or simd');
const fixtures = (process.env.ZKC_BROWSER_FIXTURES ?? 'schnorr,fri-1024').split(',').map(name => name.trim());
assert.ok(fixtures.every(name => /^[a-zA-Z0-9][a-zA-Z0-9_-]*$/.test(name)) &&
  new Set(fixtures).size === fixtures.length, 'ZKC_BROWSER_FIXTURES must contain distinct fixture directory names');
if (!webDirectory || !fixtureDirectory || !nativeExample || !process.env.ZKC_PLAYWRIGHT) {
  throw new Error('usage: ZKC_PLAYWRIGHT=/path/to/playwright/index.mjs node roundtrip.mjs WEB_DIRECTORY FIXTURES NATIVE_EXAMPLE');
}
const playwrightVersion = JSON.parse(await readFile(resolve(dirname(process.env.ZKC_PLAYWRIGHT), 'package.json'), 'utf8')).version;
assert.equal(playwrightVersion, '1.64.1', 'use the documented browser driver pin');
const playwright = await import(pathToFileURL(process.env.ZKC_PLAYWRIGHT));
const root = resolve(webDirectory);
const server = createServer(async (req, res) => {
  try {
    const file = resolve(root, '.' + new URL(req.url, 'http://localhost').pathname);
    if (!file.startsWith(root + sep)) throw new Error('path');
    const bytes = await readFile(file);
    res.setHeader('Content-Type', { '.js': 'text/javascript', '.mjs': 'text/javascript', '.wasm': 'application/wasm' }[extname(file)] ?? 'text/html');
    res.end(bytes);
  } catch { res.writeHead(404); res.end(); }
});
let browser;
try {
  await new Promise((resolve, reject) => { server.once('error', reject); server.listen(0, '127.0.0.1', resolve); });
  browser = await playwright[browserEngine].launch({ headless: true });
  const browserVersion = browser.version();
  assert.ok(typeof browserVersion === 'string' && browserVersion.trim(), 'browser must report its actual version');
  const results = { browser_engine: browserEngine, browser: browserVersion, variant, playwright: playwrightVersion,
    profile: `wasm32-unknown-unknown, no parallel, no shared memory, ${variant === 'simd' ? '+simd128' : 'default target features'}`, cases: [] };
  const page = await browser.newPage();
  // This static page has no application code or implicit cross-origin isolation.
  await page.goto(`http://127.0.0.1:${server.address().port}/index.html`);
  for (const name of fixtures) {
    const dir = resolve(fixtureDirectory, name);
    const optionalJSON = async (file, fallback) => {
      try { return JSON.parse(await readFile(resolve(dir, file), 'utf8')); }
      catch (error) { if (error.code === 'ENOENT') return fallback; throw error; }
    };
    const pin = (await readFile(resolve(dir, 'pin.txt'), 'utf8')).trim();
    const native = () => JSON.parse(execFileSync(resolve(nativeExample), [dir, pin, dir], { encoding: 'utf8', timeout: 120000 }));
    const before = native();
    assert.equal(before.prove.success, true);
    assert.equal(before.verify.accepted, true);
    const bytes = async file => Array.from(await readFile(resolve(dir, file)));
    const authority = await optionalJSON('authority.json');
    const materialBindings = async (file, key) => Promise.all((await optionalJSON(file, [])).map(async binding =>
      ({ [key]: binding[key], material: await bytes(binding.path) })));
    const input = { package: await bytes('entry.zkpkg'), pin: Array.from(Buffer.from(pin, 'hex')),
      public: await bytes('public.json'), witness: await bytes('witness.json'), proof: await bytes('native.proof'),
      options: await optionalJSON('options.json', {}),
      authority: authority == null ? [] : Array.from(new TextEncoder().encode(JSON.stringify(authority))),
      setups: await materialBindings('setups.json', 'slot'), inputs: await materialBindings('inputs.json', 'name'),
      variant, legacyControls: ['schnorr', 'fri-1024'].includes(name) };
    await writeFile(resolve(dir, 'native-before.proof'), new Uint8Array(input.proof));
    const result = await page.evaluate(async input => {
      const { ProofClient } = await import('./client.mjs');
      let client = new ProofClient({ timeoutMs: 120000, variant: input.variant });
      await client.ready;
      const call = async (operation, args = {}) => {
        try {
          if (operation === 'dispose') { client.dispose(); return {}; }
          if (operation === 'admit') return await client.admit(args);
          // The public API takes exactly the arguments for the chosen call.
          const { public: publicBytes, context, budget } = args;
          return operation === 'prove'
            ? await client.prove({ public: publicBytes, witness: args.witness, context, budget })
            : await client.verify({ public: publicBytes, proof: args.proof, context, budget });
        } catch (error) { return { error: error.message, fatal: error.fatal ?? false,
          completion: error.completion, refusal: error.refusal }; }
      };
      for (const k of ['package', 'pin', 'public', 'witness', 'proof', 'authority']) input[k] = new Uint8Array(input[k]);
      const started = performance.now();
      const admission = { package: input.package, pin: input.pin, authority: input.authority, options: input.options };
      const admit = await call('admit', admission);
      const admission_ms = performance.now() - started;
      if (admit.error) throw new Error(admit.error);
      for (const binding of input.setups) await client.setSetup(binding.slot, new Uint8Array(binding.material));
      for (const binding of input.inputs) await client.setInput(binding.name, new Uint8Array(binding.material));
      // Direct Worker envelopes remain a supported boundary with explicit
      // initialization, increasing integer IDs, and generation fencing.
      const direct = new Worker('./worker.js', { type: 'module' });
      const directCall = data => new Promise((resolve, reject) => {
        const timer = setTimeout(() => { direct.terminate(); reject(new Error('direct-worker-timeout')); }, 5000);
        const receive = ({ data }) => { clearTimeout(timer); direct.removeEventListener('message', receive); resolve(data); };
        direct.addEventListener('message', receive);
        direct.postMessage(data);
      });
      const initialized = await directCall({ id: 1, generation: 1, operation: 'initialize', variant: client.variant, module: client.compiledModule });
      if (initialized.error) throw new Error(initialized.error);
      const malformedEnvelope = await directCall(null);
      direct.terminate();
      const malformedMessages = [];
      for (let i = 0; i < 16; i++) malformedMessages.push(await call('prove', { public: new Uint8Array(1 << 20) }));
      malformedMessages.push(await call('verify', { ...input, proof: 'not-bytes' }));
      const verified = await call('verify', input);
      const trials = [];
      for (let i = 0; i < 3; i++) {
        const proved = await call('prove', input);
        const checked = proved.error ? null : await call('verify', { ...input, proof: proved.proof });
        trials.push({ proved, checked });
      }
      const malformed = await call('prove', { ...input, public: new TextEncoder().encode('{') });
      const fixtureControls = {};
      if (input.legacyControls) {
        const missing = JSON.parse(new TextDecoder().decode(input.witness));
        const first = Object.keys(missing).sort()[0]; missing[first] = null;
        const referenced = JSON.parse(new TextDecoder().decode(input.public));
        referenced[Object.keys(referenced).sort()[0]] = { file: 'forbidden.bin', sha256: '00'.repeat(32) };
        fixtureControls.reference = await call('prove', { ...input, public: new TextEncoder().encode(JSON.stringify(referenced)) });
        fixtureControls.unfilled = await call('prove', { ...input, witness: new TextEncoder().encode(JSON.stringify(missing)) });
        fixtureControls.truncated = await call('verify', { ...input, proof: input.proof.slice(0, 5) });
      }
      await call('dispose');
      const disposed = await call('prove', input);
      const badpin = input.pin.slice(); badpin[0] ^= 1;
      client = new ProofClient({ timeoutMs: 120000, compiledModule: client.compiledModule, variant: client.variant });
      await client.ready;
      const wrong_pin = await call('admit', { ...admission, pin: badpin });
      if (input.legacyControls) {
        const limited_admission = await call('admit', admission);
        fixtureControls.limited = limited_admission.error ? limited_admission : await call('prove', { ...input, budget: 0 });
      }
      await call('dispose');
      const simplify = v => v && ({ ...v, proof: v.proof && Array.from(v.proof), outputs: v.outputs && Array.from(v.outputs) });
      return { malformedEnvelope, malformedMessages, admission_ms, admission_timings: admit.timings,
        verified: simplify(verified), trials: trials.map(t => ({ proved: simplify(t.proved), checked: simplify(t.checked) })),
        controls: { malformed, disposed, wrong_pin, ...Object.fromEntries(Object.entries(fixtureControls).map(([key, value]) => [key, simplify(value)])) }, crossOriginIsolated };
    }, input);
    assert.equal(result.crossOriginIsolated, false);
    assert.equal(result.malformedEnvelope.error, 'Error: web-message');
    assert.equal(result.malformedEnvelope.fatal, false);
    for (const control of result.malformedMessages) {
      assert.match(control.error, /web-message-bytes/);
      assert.equal(control.fatal, false);
    }
    assert.equal(result.verified.report?.accepted, true, JSON.stringify(result.verified));
    for (const t of result.trials) {
      assert.equal(t.proved.report?.success, true, JSON.stringify(t.proved));
      assert.equal(t.checked.report?.accepted, true, JSON.stringify(t.checked));
      assert.deepEqual(t.checked.outputs, result.verified.outputs);
    }
    assert.equal(result.controls.malformed.error, 'entry-request-format');
    assert.equal(result.controls.malformed.refusal.path, 'public');
    assert.equal(result.controls.malformed.fatal, false);
    if (input.legacyControls) {
      assert.equal(result.controls.reference.error, 'entry-input-reference');
      assert.match(result.controls.reference.refusal.path, /^public\./);
      for (const c of ['malformed', 'unfilled', 'reference']) {
        assert.equal(result.controls[c].error, before.controls[c].error);
        assert.deepEqual(result.controls[c].refusal, before.controls[c].refusal);
      }
      for (const c of ['truncated', 'limited']) {
        assert.equal(result.controls[c].report.success, before.controls[c].report.success);
        assert.equal(result.controls[c].report.accepted, before.controls[c].report.accepted);
        assert.equal(result.controls[c].report.error, before.controls[c].report.error);
        assert.equal(result.controls[c].proof.length, before.controls[c].proof_bytes);
        assert.equal(Boolean(result.controls[c].outputs), before.controls[c].has_outputs);
      }
      assert.equal(result.controls.unfilled.error, 'entry-input-unfilled');
      assert.match(result.controls.unfilled.refusal.path, /^witness\./);
      assert.equal(result.controls.truncated.report?.success, false);
      assert.equal(result.controls.truncated.report?.accepted, null);
      assert.equal(result.controls.truncated.report.error, 'proof-truncated');
      assert.deepEqual(result.controls.truncated.proof, []);
      assert.equal(result.controls.truncated.outputs, undefined);
      assert.equal(result.controls.limited.report?.success, false, JSON.stringify(result.controls.limited));
    }
    assert.match(result.controls.disposed.error, /web-client-disposed/);
    assert.match(result.controls.wrong_pin.error, /package/);
    await writeFile(resolve(dir, 'browser.proof'), new Uint8Array(result.trials[0].proved.proof));
    const after = native();
    await writeFile(resolve(dir, 'native-after.proof'), await readFile(resolve(dir, 'native.proof')));
    assert.equal(JSON.parse(after.browser_cross_verify).accepted, true);
    if (name === 'fri-1024') assert.deepEqual(result.trials[0].proved.proof, input.proof);
    results.cases.push({ name, pin, native_before: before, native_after: after, browser: result });
  }
  await writeFile(resolve(fixtureDirectory, 'browser-results.json'), JSON.stringify(results, null, 2) + '\n');
  console.log(JSON.stringify({ browser_engine: browserEngine, browser: results.browser, variant,
    cases: results.cases.map(c => ({ name: c.name, native_ms: [c.native_before.prove_ms, c.native_before.verify_ms], browser_ms: c.browser.trials.map(t => [t.proved.milliseconds, t.checked.milliseconds]), controls: Object.keys(c.browser.controls), cross_verified: true })) }, null, 2));
} finally {
  try { await browser?.close(); }
  finally { if (server.listening) await new Promise(resolve => server.close(resolve)); }
}
