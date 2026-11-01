"""Deploy compiler scalar/output regressions with the existing solc/revm harness.

Run from any directory; all tools are explicit. The simple managed fixture has
one challenge and its delivery, so its full primitive trace is independently
reconstructed without a replacement proof producer. There are no proof messages.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "common/tests/evm"))
sys.path.insert(0, str(ROOT / "common/tests/support"))
from abi import encode_verify
from hash_chain_reference import BLS12_381_R as PRIME, BLS_SUITE, Chain, fr64be
from logical_tree import decode_tree, encode_tree
from oracle import chain_trace, check_trace
from probe import PROFILES, check_solc, compile_request, execute


def source(expression, *, ordered=False, outputs="accepted:bool@V", returns=None):
    helper = (f"fn work(a:Fr,b:Fr,c:Fr)->bool{{return {expression};}}"
              if ordered else "")
    body = "let result@V=work(a,b,c);" if ordered else ""
    decision = "result" if ordered else expression
    returns = returns or f"accepted={decision}"
    return (f'module scalar;domain Fr=field("bls12-381.fr");{helper}'
            'protocol Work roles(P,V)(a:Fr@V,b:Fr@V,c:Fr@V,'
            f'challenges:Random<Fr>@V)->({outputs}){{'
            'let challenge=challenges.draw();let delivered=send V->P(challenge);'
            f'{body}return({returns});}}'
            'proof Proof=Work{prover P;verifier V;public{a,b,c};accept accepted;'
            f'construction fiat_shamir("{BLS_SUITE}",challenges);}}')


def compile_source(compiler, text):
    command = [str(compiler), "language-evm", "--source-format=zkc",
               "--entry=scalar::Proof", "--module=scalar=-"]
    process = subprocess.run(command, input=text, text=True, capture_output=True,
                             timeout=30)
    if process.returncode:
        raise AssertionError(process.stderr)
    return json.loads(process.stdout)


def artifact(solc, yul):
    return compile_request(solc, {
        "language": "Yul", "sources": {"scalar.yul": {"content": yul}},
        "settings": {"evmVersion": "cancun", "optimizer": PROFILES["colon"],
                     "outputSelection": {"*": {"*": ["evm.bytecode.object",
                         "evm.deployedBytecode.object"]}}}})


def invocation(compiled, values):
    public = [b"ZKCV\x00\x01" + (v % PRIME).to_bytes(32, "little") for v in values]
    descriptor, policy = compiled["descriptor"], compiled["policy"]
    rows = [[*r[:3], v.hex()] for r, v in zip(descriptor[4], public, strict=True)]
    tree = ["zkc.native-proof-binding/0", "sha256", descriptor[2],
            compiled["source_sha256"], *policy[1:4], descriptor, rows, ""]
    root = encode_tree(tree)
    digest = hashlib.sha256(root).digest()
    proof = b"ZKCPRF00" + digest
    chain = Chain(BLS_SUITE, root)
    templates = [decode_tree(bytes.fromhex(t[1])) for t in descriptor[3]]
    assert [t[4][0] for t in templates] == ["query", "message"]
    assert all(t[3] == [] for t in templates)
    occurrences = [encode_tree(["zkc.native-origin/0", t[1], t[2], [], t[4]])
                   for t in templates]
    chain.absorb(b"origin", occurrences[0])
    challenge = fr64be(chain.request(b"challenge", 64))
    chain.absorb(b"origin", occurrences[1])
    chain.absorb(b"value", b"ZKCV\x00\x01" + challenge.to_bytes(32, "little"))
    trace = [{"kind": "sha256", "input": root.hex(), "output": digest.hex(),
              "status": "return"}, *chain_trace(chain)]
    return public, proof, trace


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("compiler", "solc", "runner", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    args = parser.parse_args()
    for name in ("compiler", "solc", "runner"):
        setattr(args, name, getattr(args, name).resolve())
    version = check_solc(args.solc)
    cases = []
    for ordered in (False, True):
        for name, expr, values in [
            ("mul", "a*b==c", [(2, 3, 6, True), (2, 3, 7, False),
                                  (PRIME-1, PRIME-1, 1, True)]),
            ("add", "a+b==c", [(2, 3, 5, True), (2, 3, 7, False),
                                  (PRIME-1, 2, 1, True)]),
            ("sub", "a-b==c", [(2, 3, PRIME-1, True), (2, 3, 1, False)]),
            ("constant", "a+1==c", [(2, 0, 3, True), (2, 0, 4, False)]),
            ("not", "!(a==b)", [(1, 2, 0, True), (1, 1, 0, False)]),
            ("and", "a==b && b==c", [(1, 1, 1, True), (1, 1, 2, False)]),
            ("or", "a==b || b==c", [(1, 2, 2, True), (1, 2, 3, False)]),
        ]:
            cases.append((f'{"ordered" if ordered else "pure"}-{name}',
                          source(expr, ordered=ordered), values))
    for name, expr, values in [
        ("neg", 'kernel<Fr>("field.neg",a)==c',
         [(2, 0, PRIME-2, True), (2, 0, 2, False)]),
        ("inverse", 'kernel<Fr>("field.inverse",a)==c',
         [(2, 0, (PRIME+1)//2, True), (2, 0, 1, False), (0, 0, 0, None)]),
    ]:
        cases.append((name, source(expr, ordered=True), values))
    for name, outputs, returns in [
        ("nonfirst-bool", "extra:bool@V,accepted:bool@V", "extra=true,accepted=a*b==c"),
        ("opposite-bool", "extra:bool@V,accepted:bool@V", "extra=false,accepted=a*b==c"),
        ("extra-fr", "extra:Fr@V,accepted:bool@V", "extra=a+b,accepted=a*b==c"),
        ("trailing-fr", "accepted:bool@V,extra:Fr@V", "accepted=a*b==c,extra=a+b"),
        ("projected", "hidden:Fr@P,extra:Fr@V,other:bool@V,accepted:bool@V",
         "hidden=delivered,extra=a+b,other=true,accepted=a*b==c"),
    ]:
        cases.append((name, source("a*b==c", outputs=outputs, returns=returns),
                      [(2, 3, 6, True), (2, 3, 7, False)]))
    ignored = source("a*b==c", outputs="extra:Fr@V,accepted:bool@V",
                     returns="extra=extra,accepted=a*b==c")
    ignored = ignored.replace("protocol Work", 'fn inv(a:Fr)->Fr{'
                              'return kernel<Fr>("field.inverse",a);}protocol Work')
    ignored = ignored.replace("return(extra=extra", "let extra@V=inv(a);return(extra=extra")
    cases.append(("ignored-inverse", ignored,
                  [(2, 3, 6, True), (2, 3, 7, False), (0, 3, 0, None)]))
    receipts = []
    args.output.mkdir(parents=True, exist_ok=True)
    for name, text, inputs in cases:
        compiled = compile_source(args.compiler, text)
        built = artifact(args.solc, compiled["yul"])
        (args.output / f"{name}.zkc").write_text(text)
        (args.output / f"{name}.json").write_text(json.dumps(compiled, indent=2))
        (args.output / f"{name}.solc.json").write_text(json.dumps(built, indent=2))
        for a, b, c, accepted in inputs:
            public, proof, trace = invocation(compiled, (a, b, c))
            result = execute(args.runner, built, encode_verify(public, b"", proof),
                             gas=20_000_000, repeat_count=2)
            expected_status = "return" if accepted is not None else "revert"
            expected_output = (int(accepted).to_bytes(32, "big").hex()
                               if accepted is not None else "5a4b4353" + f"{2:064x}")
            for call in result["calls"]:
                assert call["status"] == expected_status, (name, call)
                assert call["output"] == expected_output, (name, call)
                check_trace(call["trace"], trace)
            receipts.append({"name": name, "values": [a, b, c],
                             "accepted": accepted, "execution": result})
            if accepted is not None and name in ("nonfirst-bool", "extra-fr"):
                trailing = execute(args.runner, built,
                    encode_verify(public, b"", proof+b"\x00"),
                    gas=20_000_000, repeat_count=2)
                for call in trailing["calls"]:
                    assert call["status"] == "revert"
                    assert call["output"] == "5a4b4344" + f"{13:064x}"
                    check_trace(call["trace"], trace)
                receipts.append({"name": name+"-trailing-proof",
                                 "accepted": accepted, "execution": trailing})
        if name == "nonfirst-bool":
            changed, count = re.subn(r"if iszero\(eq\((v\d+), mload\(0xc0\)\)\)",
                r"if iszero(eq(add(\1, 1), mload(0xc0)))", compiled["yul"])
            assert count == 1, "managed generation check missing"
            mutant = artifact(args.solc, changed)
            public, proof, trace = invocation(compiled, (2, 3, 6))
            result = execute(args.runner, mutant, encode_verify(public, b"", proof),
                             gas=20_000_000, repeat_count=2)
            for call in result["calls"]:
                assert call["status"] == "revert"
                assert call["output"] == "5a4b4354" + f"{5:064x}"
                check_trace(call["trace"], trace)
            receipts.append({"name": "stale-transcript-control", "execution": result})
        print(name, "passed", flush=True)
    receipt = {"solc_version": version, "compiler_sha256": hashlib.sha256(
        args.compiler.read_bytes()).hexdigest(), "runner_sha256": hashlib.sha256(
        args.runner.read_bytes()).hexdigest(), "cases": receipts}
    (args.output / "results.json").write_text(json.dumps(receipt, indent=2))
    print(f"{len(receipts)} deployed cases, two calls per deployment, exact traces")


if __name__ == "__main__":
    main()
