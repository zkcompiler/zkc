#!/usr/bin/env python3
"""Validate independent word/CRT models with Z3 and MLIR SMT export.

This offline check does not translate native code, admit compiler rewrites,
produce proof certificates, or establish protocol security.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

PRIMES = (2013265921, 1811939329, 469762049)
PROTOCOL_MODULUS = 2**64 - 59


class ValidationError(ValueError):
    """Missing, malformed, inconclusive or contradictory validation evidence."""


def require(condition, message):
    if not condition:
        raise ValidationError(message)


def centered_query(wrapping):
    threshold = ('(bvudiv (bvadd q (_ bv1 64)) (_ bv2 64))' if wrapping else
                 '(bvadd (bvudiv q (_ bv2 64)) (bvurem q (_ bv2 64)))')
    return f'''(set-logic QF_BV)
(declare-const q (_ BitVec 64))
(declare-const c (_ BitVec 64))
(assert (bvuge q (_ bv2 64)))
(assert (bvult c q))
(define-fun expected () Bool (bvult ((_ zero_extend 1) c)
  (bvudiv (bvadd ((_ zero_extend 1) q) (_ bv1 65)) (_ bv2 65))))
(define-fun actual () Bool (bvult c {threshold}))
(assert (not (= actual expected)))'''


def crt_query(product, bound):
    return f'''(set-logic QF_LIA)
(declare-const x Int)
(assert (<= (- {bound}) x))
(assert (<= x {bound}))
(define-fun r () Int (mod x {product}))
(define-fun lifted () Int (ite (> r {product//2}) (- r {product}) r))
(assert (not (= x lifted)))'''


def mlir_query(product, bound):
    return f'''module {{ smt.solver () : () -> () {{
%x = smt.declare_fun "x" : !smt.int
%p = smt.int.constant {product}
%half = smt.int.constant {product//2}
%bound = smt.int.constant {bound}
%lower = smt.int.constant {-bound}
%low = smt.int.cmp le %lower, %x
%high = smt.int.cmp le %x, %bound
smt.assert %low
smt.assert %high
%r = smt.int.mod %x, %p
%negative = smt.int.cmp gt %r, %half
%sub = smt.int.sub %r, %p
%lift = smt.ite %negative, %sub, %r : !smt.int
%equal = smt.eq %lift, %x : !smt.int
%wrong = smt.not %equal
smt.assert %wrong
smt.check sat {{}} unknown {{}} unsat {{}}
}} }}'''


def replay_word(model):
    values = {key: int(value) for key, value in re.findall(
        r'define-fun (q|c) \(\) \(_ BitVec 64\)\s+\(_ bv(\d+) 64\)', model)}
    require(values.keys() == {'q', 'c'}, 'word model is missing q or c')
    q, c = values['q'], values['c']
    require(2 <= q < 2**64 and 0 <= c < q, 'word model violates input premises')
    require((c < ((q+1) % 2**64)//2) != (c < (q+1)//2),
            'word model does not replay the claimed disagreement')
    return values


def replay_crt(model, product, modulus, bound):
    match = re.search(r'define-fun x \(\) Int\s+((?:\(- \d+\))|\d+)', model)
    require(match is not None, 'CRT model is missing x')
    value = match.group(1)
    x = -int(value[3:-1]) if value.startswith('(-') else int(value)
    residue = x % product
    lifted = residue-product if residue > product//2 else residue
    require(-bound <= x <= bound, 'CRT model violates its bound')
    require(x % modulus != lifted % modulus, 'CRT model does not replay the disagreement')
    return {'x': x, 'lifted': lifted, 'modulus': modulus}


class Checks:
    def __init__(self, solver, translator, output):
        self.solver, self.translator, self.output = solver, translator, output
        self.records = []

    def run(self, name, arguments, stdin=None):
        try:
            result = subprocess.run(list(map(str, arguments)), input=stdin,
                                    capture_output=True, text=True, timeout=15)
        except subprocess.TimeoutExpired as error:
            raise ValidationError(f'{name}: process timeout') from error
        (self.output / f'{name}.stdout').write_text(result.stdout)
        (self.output / f'{name}.stderr').write_text(result.stderr)
        require(result.returncode == 0, f'{name}: tool failed ({result.returncode})')
        return result.stdout

    def solve(self, name, query, expected, model=False, exported=False):
        text = '(set-option :timeout 10000)\n(set-option :pp.bv-literals false)\n' + query
        if not exported:
            text += '\n(check-sat)\n'
        if model:
            if exported:
                require(text.count('(check-sat)') == 1 and text.rstrip().endswith('(reset)'),
                        'unexpected SMT export scope')
                text = text.replace('(check-sat)', '(check-sat)\n(get-model)')
            else:
                text += '\n(get-model)\n'
        path = self.output / f'{name}.smt2'
        path.write_text(text)
        result = self.run(name, [self.solver, '-T:10', '-memory:512', path])
        lines = result.splitlines()
        status = lines[0].strip() if lines else 'missing'
        require(status in {'sat', 'unsat'}, f'{name}: inconclusive result {status!r}')
        require(status == expected, f'{name}: expected {expected}, got {status}')
        require('(error' not in result, f'{name}: solver reported an error')
        self.records.append({'name': name, 'status': status,
                             'query_sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
        return result

    def validate(self, pins):
        solver_version = self.run('solver-version', [self.solver, '--version']).strip()
        translator_version = self.run('translator-version', [self.translator, '--version']).strip()
        require(re.search(r'\bZ3 version ' + re.escape(pins['z3']['version']) + r'\b', solver_version),
                'unsupported solver version')
        require(re.search(r'\bversion ' + re.escape(pins['llvm']['version']) + r'\b', translator_version),
                'unsupported MLIR version')
        self.solve('centered-word-valid', centered_query(False), 'unsat')
        replay = [{'name': 'centered-word-wrapping', **replay_word(self.solve(
            'centered-word-wrapping', centered_query(True), 'sat', model=True))}]
        product = 1
        for limbs, prime in enumerate(PRIMES, 1):
            product *= prime
            for wrong in (False, True):
                name = f'crt-{limbs}-' + ('too-wide' if wrong else 'valid')
                bound = product//2 + int(wrong)
                expected = 'sat' if wrong else 'unsat'
                result = self.solve(name, crt_query(product, bound),
                                    expected, model=wrong)
                if wrong:
                    replay.append({'name': name, **replay_crt(result, product, PROTOCOL_MODULUS, bound)})
                source = self.output / f'{name}.mlir'
                source.write_text(mlir_query(product, bound))
                exported = self.run(name + '-export', [self.translator, '--export-smtlib', source])
                result = self.solve(name + '-mlir', exported, expected, model=wrong, exported=True)
                if wrong:
                    # MLIR renames the declared symbol in the SMT-LIB export.
                    symbol = re.search(r'\(declare-const ([^ ()]+) Int\)', exported)
                    require(symbol is not None, 'missing exported integer declaration')
                    result = result.replace('define-fun ' + symbol.group(1) + ' ', 'define-fun x ')
                    replay.append({'name': name + '-mlir', **replay_crt(result, product, PROTOCOL_MODULUS, bound)})
        degree, a, b = 4, PROTOCOL_MODULUS//2, 10_000_000
        capacity = (product-1)//(2*degree*a*b)
        exact = (capacity+1)*degree*a*b
        residue = exact % product
        lifted = residue-product if residue > product//2 else residue
        require(capacity > 0 and exact % PROTOCOL_MODULUS != lifted % PROTOCOL_MODULUS,
                'one-extra-column control did not expose an incorrect lift')
        replay.append({'name': 'one-extra-column', 'safe_columns': capacity,
                       'columns': capacity+1, 'exact': exact, 'lifted': lifted})
        require(all((x % 35 if x % 35 <= 17 else x % 35-35) == x for x in range(-17, 18)),
                'independent toy reconstruction failed')
        return {'solver_version': solver_version, 'translator_version': translator_version,
                'solver_sha256': hashlib.sha256(self.solver.read_bytes()).hexdigest(),
                'translator_sha256': hashlib.sha256(self.translator.read_bytes()).hexdigest(),
                'replayed_counterexamples': replay}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--solver', type=Path, required=True)
    parser.add_argument('--mlir-translate', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    # Never overwrite a previous validation record.
    args.output.mkdir(parents=True, exist_ok=False)
    pins_path = Path(__file__).with_name('fixtures') / 'arithmetic' / 'pins.json'
    checks = Checks(args.solver.resolve(), args.mlir_translate.resolve(), args.output)
    report = {'format': 'zkc.arithmetic-validation/0', 'status': 'failed',
              'scope': 'Independent formula models; no native correspondence or checked proof certificate',
              'checker_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    try:
        pins = json.loads(pins_path.read_text())
        report['pins'] = pins
        report.update(checks.validate(pins))
        report['status'] = 'passed'
    except (ValidationError, OSError, ValueError) as error:
        report['error'] = str(error)
    finally:
        report['queries'] = checks.records
        (args.output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'report': str(args.output / 'report.json')}))
    return 0 if report['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
