#!/usr/bin/env python3
"""Independent integer results, transform regressions and candidate mutations."""
import argparse
import json
from pathlib import Path
import random
import re
import subprocess


def prefix(q, n):
    return f'''!c = !mod_arith.int<{q}:i32>
#ring = #polynomial.ring<coefficientType=!c, polynomialModulus=<1 + x**{n}>>
!p = !polynomial.polynomial<ring=#ring>
!e = !polynomial.polynomial<ring=#ring, form=eval>
'''


def convolution(a, b, q):
    # Integer convolution first, then polynomial and coefficient reduction.
    n = len(a)
    full = [0] * (2*n-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            full[i+j] += x*y
    return [(full[i] - (full[i+n] if i+n < len(full) else 0)) % q for i in range(n)]


class Checks:
    def __init__(self, args):
        self.args = args
        self.work = args.work.resolve()
        self.work.mkdir(parents=True, exist_ok=True)
        self.records = []

    def run(self, name, argv, diagnostic=None):
        result = subprocess.run(list(map(str, argv)), capture_output=True, text=True, timeout=90)
        (self.work / (name + '.stdout')).write_text(result.stdout)
        (self.work / (name + '.stderr')).write_text(result.stderr)
        self.records.append({'name': name, 'argv': list(map(str, argv)), 'exit_code': result.returncode})
        (self.work / 'commands.json').write_text(json.dumps(self.records, indent=2) + '\n')
        if diagnostic:
            assert result.returncode and diagnostic in result.stderr, (name, result.stderr)
        else:
            assert result.returncode == 0, (name, result.stderr)
        return result.stdout

    def source(self, name, code):
        path = self.work / (name + '.mlir')
        path.write_text(code)
        return path

    def check(self, name, source, candidate, diagnostic=None):
        self.run(name, [self.args.checker, source, candidate], diagnostic)

    def place(self, name, source, forward, inverse):
        placed = self.work / (name + '.placed.mlir')
        self.check(name + '-source', source, source)
        placed.write_text(self.run(name + '-placement', [self.args.placement, source]))
        self.check(name + '-compare', source, placed)
        ir = placed.read_text()
        assert len(re.findall(r' = polynomial.ntt ', ir)) == forward
        assert len(re.findall(r' = polynomial.intt ', ir)) == inverse
        return placed

    def execute(self, name, source, inputs, n, outputs, canonicalize=False):
        arithmetic = self.work / (name + '.arith.mlir')
        self.run(name + '-arithmetic', [self.args.optimizer, source,
                 *(['--canonicalize'] if canonicalize else []),
                 '--polynomial-to-mod-arith', '--mod-arith-to-arith',
                 '--canonicalize', '--cse', '-o', arithmetic])
        ty = f'tensor<{n}xi32>'
        main = 'func.func private @printI64(i64)\nfunc.func private @printNewline()\nfunc.func @main() {\n'
        for key, value in inputs.items():
            main += f'%{key} = arith.constant dense<[{", ".join(map(str, value))}]> : {ty}\n'
        main += ', '.join(f'%o{i}' for i in range(outputs))
        main += f' = func.call @compute({", ".join("%"+k for k in inputs)}) : '
        main += f'({", ".join([ty]*len(inputs))}) -> ({", ".join([ty]*outputs)})\n'
        main += f'%zero=arith.constant 0:index\n%one=arith.constant 1:index\n%end=arith.constant {n}:index\n'
        for i in range(outputs):
            main += f'''scf.for %i = %zero to %end step %one {{
%x = tensor.extract %o{i}[%i] : {ty}
%y = arith.extui %x : i32 to i64
func.call @printI64(%y) : (i64) -> ()
func.call @printNewline() : () -> ()
}}\n'''
        main += 'return\n}\n'
        text = arithmetic.read_text().rstrip()
        assert text.endswith('}')
        runtime = self.source(name + '-runtime', text[:-1] + main + '}\n')
        llvm = self.work / (name + '.llvm.mlir')
        self.run(name + '-llvm', [self.args.mlir_opt, runtime,
                 '--convert-elementwise-to-linalg', '--empty-tensor-to-alloc-tensor',
                 '--one-shot-bufferize=bufferize-function-boundaries',
                 '--buffer-deallocation-pipeline', '--convert-bufferization-to-memref',
                 '--convert-linalg-to-loops', '--canonicalize', '--cse',
                 '--expand-strided-metadata', '--lower-affine', '--convert-scf-to-cf',
                 '--convert-arith-to-llvm', '--convert-index-to-llvm',
                 '--finalize-memref-to-llvm', '--convert-func-to-llvm',
                 '--convert-cf-to-llvm', '--reconcile-unrealized-casts', '-o', llvm])
        result = self.run(name + '-execute', [self.args.runner, llvm, '-e', 'main',
                          '-entry-point-result=void', '-shared-libs=' + str(self.args.runner_utils)])
        return list(map(int, result.split()))

    def matvec(self, q, n, rows, cols, name, subtract=False):
        ty = f'tensor<{n}xi32>'
        keys = [f'a{i}_{j}' for i in range(rows) for j in range(cols)] + [f'x{j}' for j in range(cols)]
        code = prefix(q, n) + f'func.func @compute({", ".join("%"+k+":"+ty for k in keys)}) -> ({", ".join([ty]*rows)}) {{\n'
        for k in keys:
            code += f'%m{k}=mod_arith.encapsulate %{k} : {ty} -> tensor<{n}x!c>\n'
            code += f'%p{k}=polynomial.from_tensor %m{k} : tensor<{n}x!c> -> !p\n'
        for i in range(rows):
            last = None
            for j in range(cols):
                product = f't{i}_{j}'
                code += f'%{product}=polynomial.mul %pa{i}_{j}, %px{j} : !p\n'
                if last:
                    operation = 'sub' if subtract else 'add'
                    code += f'%s{i}_{j}=polynomial.{operation} %{last}, %{product} : !p\n'
                    last = f's{i}_{j}'
                else:
                    last = product
            code += f'%r{i}=polynomial.to_tensor %{last} : !p -> tensor<{n}x!c>\n'
            code += f'%o{i}=mod_arith.lift standard %r{i} : tensor<{n}x!c> -> {ty}\n'
        code += f'return {", ".join("%o"+str(i) for i in range(rows))} : {", ".join([ty]*rows)}\n}}\n'
        source = self.source(name, code)
        placed = self.place(name, source, rows*cols+cols, rows)
        for pattern in ('boundary', 'random'):
            rng = random.Random(731 + q + n + rows + cols)
            inputs = {k: ([0, q-1, 1] * ((n+2)//3))[:n] if pattern == 'boundary'
                      else [rng.randrange(q) for _ in range(n)] for k in keys}
            expected = []
            for i in range(rows):
                terms = [convolution(inputs[f'a{i}_{j}'], inputs[f'x{j}'], q) for j in range(cols)]
                expected += [(terms[0][k] - sum(t[k] for t in terms[1:]) if subtract
                              else sum(t[k] for t in terms)) % q for k in range(n)]
            actual = self.execute(name + '-' + pattern, placed, inputs, n, rows)
            assert actual == expected, name
        return source, placed

    def mutations(self, source, placed):
        original = source.read_text()
        mutations = [
            ('changed-product', original.replace('polynomial.mul', 'polynomial.add', 1), 'heir-correspondence'),
            ('changed-input', original.replace('%pa0_0, %px0', '%pa0_0, %pa0_0'), 'heir-correspondence'),
            ('centered', original.replace('lift standard', 'lift centered'), 'heir-profile'),
            ('cyclic', original.replace('<1 + x**4>', '<-1 + x**4>'), 'heir-profile'),
            ('composite', original.replace('17:i32', '65:i32'), 'heir-profile'),
            ('scalar-root-unavailable', original.replace('17:i32', '19:i32'), 'heir-profile'),
            ('wide-storage', original.replace('i32', 'i64'), 'heir-profile'),
            ('large-modulus', original.replace('17:i32', '2147483647:i32'), 'heir-profile'),
            ('unit-degree', original.replace('4x', '1x').replace('x**4', 'x**1'), 'heir-profile'),
            ('non-power-degree', original.replace('4x', '3x').replace('x**4', 'x**3'), 'heir-profile'),
            ('changed-symbol', original.replace('@compute', '@different'), 'heir-correspondence'),
            ('unexpected-attribute', original.replace('func.func @compute', 'func.func @compute').replace('polynomial.mul %pa0_0, %px0 :', 'polynomial.mul %pa0_0, %px0 {extra=true} :'), 'heir-profile'),
        ]
        accumulated = '%s0_3'
        expansion = ''
        for i in range(8):
            expansion += f'%expanded{i}=polynomial.mul {accumulated}, {accumulated} : !p\n'
            accumulated = f'%expanded{i}'
        oversized = original.replace('%r0=polynomial.to_tensor %s0_3',
                                     expansion + '%r0=polynomial.to_tensor ' + accumulated)
        mutations.append(('expression-limit', oversized, 'heir-profile'))
        for name, code, diagnostic in mutations:
            candidate = self.source(name, code)
            self.check(name, source, candidate, diagnostic)
            if diagnostic == 'heir-profile':
                output = self.run(name + '-placement-refusal', [self.args.placement, candidate], diagnostic)
                assert not output, 'a refused placement must publish no candidate'
        text = placed.read_text()
        # Change one forward transform to another primitive root in F17. Both
        # roots are individually valid; their coordinate systems differ.
        roots = re.findall(r'polynomial.ntt.*?value = #mod_arith.value<(\d+) :', text)
        assert roots, text
        root = int(roots[0])
        changed = text.replace(f'value = #mod_arith.value<{root} :',
                               f'value = #mod_arith.value<{pow(root, 3, 17)} :', 1)
        self.check('mismatched-transform', source, self.source('mismatched-transform', changed), 'heir-profile')
        # A coordinated change to every forward and inverse root is legitimate:
        # the coefficient observation remains the same despite a new basis.
        changed_all = re.sub(r'value = #mod_arith.value<(\d+) :',
                             lambda m: f'value = #mod_arith.value<{pow(int(m[1]), 3, 17)} :', text)
        self.check('consistent-basis-change', source, self.source('consistent-basis-change', changed_all))
        self.check('missing-root', source, self.source('missing-root', re.sub(
            r' <\{root = .*?\}>', '', text, count=1)), 'heir-profile')

    def folding(self):
        q, n, forward = 17, 4, 2
        a = [1, 2, 3, 4]
        evaluation = [sum(a[j] * pow(forward, (2*k+1)*j, q) for j in range(n)) % q for k in range(n)]
        for inverse in (9, 2):
            code = prefix(q, n) + f'''#r = #polynomial.primitive_root<value=#mod_arith.value<{forward}:!c>, degree=8:i32>
#ri = #polynomial.primitive_root<value=#mod_arith.value<{inverse}:!c>, degree=8:i32>
func.func @compute() -> tensor<4xi32> {{
%a=polynomial.constant int<1 + 2x + 3x**2 + 4x**3> : !p
%e=polynomial.ntt %a <{{root=#r}}> : !p
%c=polynomial.intt %e <{{root=#ri}}> : !e
%t=polynomial.to_tensor %c : !p -> tensor<4x!c>
%r=mod_arith.lift standard %t : tensor<4x!c> -> tensor<4xi32>
return %r : tensor<4xi32>
}}
'''
            source = self.source(f'fold-{inverse}', code)
            expected = [sum(evaluation[k] * pow(inverse, (2*k+1)*j, q)
                            for k in range(n)) * pow(n, -1, q) % q for j in range(n)]
            for fold in (False, True):
                actual = self.execute(f'fold-{inverse}-{fold}', source, {}, n, 1, canonicalize=fold)
                assert actual == expected, (inverse, fold, actual, expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('optimizer', 'checker', 'placement', 'mlir-opt', 'runner', 'runner-utils', 'work'):
        parser.add_argument('--' + name, type=Path, required=True)
    checks = Checks(parser.parse_args())
    source, placed = checks.matvec(17, 4, 1, 4, 'dot-product')
    checks.mutations(source, placed)
    checks.matvec(8380417, 256, 4, 4, 'module-matvec')
    checks.matvec(12289, 512, 4, 1, 'falcon-ring-products')
    checks.matvec(2013265921, 4, 1, 4, 'large-modulus-subtraction', subtract=True)
    checks.folding()
    print(f'Passed {len(checks.records)} tool invocations, including independent integer outputs and refusals.')


if __name__ == '__main__':
    main()
