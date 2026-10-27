// Manual integration check. Tools are pinned by the invoking development shell;
// no browser or dependency download occurs here. See crates/zkc-web/README.md.
import assert from 'node:assert/strict';
import { readFile, writeFile } from 'node:fs/promises';
import { createServer } from 'node:http';
import { resolve, sep, extname, dirname } from 'node:path';
import { pathToFileURL } from 'node:url';
import { execFileSync } from 'node:child_process';
const [webDirectory, fixtureDirectory, nativeExample] = process.argv.slice(2);
if (!webDirectory || !fixtureDirectory || !nativeExample || !process.env.ZKC_PLAYWRIGHT) {
  throw new Error('usage: ZKC_PLAYWRIGHT=/path/to/playwright/index.mjs node roundtrip.mjs WEB_DIRECTORY FIXTURES NATIVE_EXAMPLE');
}
const playwrightVersion = JSON.parse(await readFile(resolve(dirname(process.env.ZKC_PLAYWRIGHT), 'package.json'), 'utf8')).version;
assert.equal(playwrightVersion, '1.64.1', 'use the documented browser driver pin');
const { chromium } = await import(pathToFileURL(process.env.ZKC_PLAYWRIGHT));
const root = resolve(webDirectory);
const server = createServer(async (req, res) => {
  try {
    const file = resolve(root, '.' + new URL(req.url, 'http://localhost').pathname);
    if (!file.startsWith(root + sep)) throw new Error('path');
    const bytes = await readFile(file);
    res.setHeader('Content-Type', { '.js': 'text/javascript', '.wasm': 'application/wasm' }[extname(file)] ?? 'text/html');
    res.end(bytes);
  } catch { res.writeHead(404); res.end(); }
});
await new Promise(r => server.listen(0, '127.0.0.1', r));
const browser = await chromium.launch({ headless: true });
const results = { browser: browser.version(), playwright: playwrightVersion, profile: 'wasm32-unknown-unknown, no parallel, no shared memory, default target features', cases: [] };
try {
  const page = await browser.newPage();
  // This static page has no application code or implicit cross-origin isolation.
  await page.goto(`http://127.0.0.1:${server.address().port}/index.html`);
  for (const name of ['schnorr', 'fri-1024']) {
    const dir = resolve(fixtureDirectory, name);
    const pin = (await readFile(resolve(dir, 'pin.txt'), 'utf8')).trim();
    const native = () => JSON.parse(execFileSync(resolve(nativeExample), [dir, pin, dir], { encoding: 'utf8', timeout: 120000 }));
    const before = native();
    assert.equal(before.prove.success, true);
    assert.equal(before.verify.accepted, true);
    const bytes = async file => Array.from(await readFile(resolve(dir, file)));
    const input = { package: await bytes('entry.zkpkg'), pin: Array.from(Buffer.from(pin, 'hex')), public: await bytes('public.json'), witness: await bytes('witness.json'), proof: await bytes('native.proof') };
    await writeFile(resolve(dir, 'native-before.proof'), new Uint8Array(input.proof));
    const result = await page.evaluate(async input => {
      const worker = new Worker('./worker.js', { type: 'module' });
      let counter = 0;
      const pending = new Map();
      worker.onerror = event => { for (const resolve of pending.values()) resolve({ error: event.message, fatal: true }); pending.clear(); };
      worker.onmessage = ({ data }) => {
        const p = pending.get(data.id);
        if (p) { pending.delete(data.id); p(data); }
      };
      const call = (operation, extra = {}) => new Promise(resolve => {
        const id = ++counter;
        const timer = setTimeout(() => { pending.delete(id); worker.terminate(); resolve({ error: 'browser-check-timeout', fatal: true }); }, 120000);
        pending.set(id, value => { clearTimeout(timer); resolve(value); });
        worker.postMessage({ id, operation, ...extra });
      });
      for (const k of Object.keys(input)) input[k] = new Uint8Array(input[k]);
      const started = performance.now();
      const admit = await call('admit', { package: input.package, pin: input.pin });
      const admission_ms = performance.now() - started;
      if (admit.error) throw new Error(admit.error);
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
      const missing = JSON.parse(new TextDecoder().decode(input.witness));
      const first = Object.keys(missing).sort()[0]; missing[first] = null;
      const referenced = JSON.parse(new TextDecoder().decode(input.public));
      referenced[Object.keys(referenced).sort()[0]] = { file: 'forbidden.bin', sha256: '00'.repeat(32) };
      const reference = await call('prove', { ...input, public: new TextEncoder().encode(JSON.stringify(referenced)) });
      const unfilled = await call('prove', { ...input, witness: new TextEncoder().encode(JSON.stringify(missing)) });
      const truncated = await call('verify', { ...input, proof: input.proof.slice(0, 5) });
      await call('dispose');
      const disposed = await call('prove', input);
      const badpin = input.pin.slice(); badpin[0] ^= 1;
      const wrong_pin = await call('admit', { package: input.package, pin: badpin });
      const limited_admission = await call('admit', { package: input.package, pin: input.pin, options: {} });
      const limited = limited_admission.error ? limited_admission : await call('prove', { ...input, budget: 0 });
      await call('dispose'); worker.terminate();
      const simplify = v => v && ({ ...v, proof: v.proof && Array.from(v.proof), outputs: v.outputs && Array.from(v.outputs) });
      return { malformedMessages, admission_ms, verified: simplify(verified), trials: trials.map(t => ({ proved: simplify(t.proved), checked: simplify(t.checked) })), controls: { malformed, unfilled, reference, truncated: simplify(truncated), disposed, wrong_pin, limited: simplify(limited) }, crossOriginIsolated };
    }, input);
    assert.equal(result.crossOriginIsolated, false);
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
    assert.match(result.controls.malformed.error, /^entry-request-format: public$/);
    assert.match(result.controls.reference.error, /^entry-input-reference: public\./);
    for (const c of ['malformed', 'unfilled', 'reference']) assert.equal(result.controls[c].error, before.controls[c].error);
    for (const c of ['truncated', 'limited']) {
      assert.equal(result.controls[c].report.success, before.controls[c].report.success);
      assert.equal(result.controls[c].report.accepted, before.controls[c].report.accepted);
      assert.equal(result.controls[c].report.error, before.controls[c].report.error);
      assert.equal(result.controls[c].proof.length, before.controls[c].proof_bytes);
      assert.equal(Boolean(result.controls[c].outputs), before.controls[c].has_outputs);
    }
    assert.match(result.controls.unfilled.error, /^entry-input-unfilled: witness\./);
    assert.equal(result.controls.truncated.report?.success, false);
    assert.equal(result.controls.truncated.report?.accepted, null);
    assert.equal(result.controls.truncated.report.error, 'proof-truncated');
    assert.deepEqual(result.controls.truncated.proof, []);
    assert.equal(result.controls.truncated.outputs, undefined);
    assert.match(result.controls.disposed.error, /web-session-missing/);
    assert.match(result.controls.wrong_pin.error, /package/);
    assert.equal(result.controls.limited.report?.success, false, JSON.stringify(result.controls.limited));
    await writeFile(resolve(dir, 'browser.proof'), new Uint8Array(result.trials[0].proved.proof));
    const after = native();
    await writeFile(resolve(dir, 'native-after.proof'), await readFile(resolve(dir, 'native.proof')));
    assert.equal(JSON.parse(after.browser_cross_verify).accepted, true);
    if (name === 'fri-1024') assert.deepEqual(result.trials[0].proved.proof, input.proof);
    results.cases.push({ name, pin, native_before: before, native_after: after, browser: result });
  }
  await writeFile(resolve(fixtureDirectory, 'browser-results.json'), JSON.stringify(results, null, 2) + '\n');
  console.log(JSON.stringify({ browser: results.browser, cases: results.cases.map(c => ({ name: c.name, native_ms: [c.native_before.prove_ms, c.native_before.verify_ms], browser_ms: c.browser.trials.map(t => [t.proved.milliseconds, t.checked.milliseconds]), controls: Object.keys(c.browser.controls), cross_verified: true })) }, null, 2));
} finally { await browser.close(); server.close(); }
