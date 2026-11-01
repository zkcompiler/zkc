"""Deploy expected-type codec controls using the existing pinned solc/revm tools.

The C++ test consumer emits production WireGenerator helpers. Round trips check
exact canonical bytes; separate raw-value views check coefficient order, widths
and canonical (non-Montgomery) memory independently of the encoder.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "support"))

from abi import encode_verify
from logical_tree import encode_tree
from probe import PROFILES, check_solc, compile_request, execute
from validate import check_return, check_revert

FIELDS = [
    ("bls12-381.fr", 1, 66, 32, 1,
     52435875175126190479447740508185965837690552500527637822603658699938581184513),
    ("bn254.fr", 40, 41, 32, 1,
     21888242871839275222246405745257275088548364400416034343698204186575808495617),
    ("ristretto255.scalar", 13, 14, 32, 1,
     7237005577332262213973186563042994240857116359379907606001950938285454250989),
    ("koala-bear", 19, 20, 4, 1, 2130706433),
    ("koala-bear.ext4-binomial3", 21, 22, 4, 4, 2130706433),
    ("koala-bear.ext8-binomial3", 26, 27, 4, 8, 2130706433),
    ("baby-bear", 90, 91, 4, 1, 2013265921),
    ("baby-bear.ext4-binomial11", 93, 94, 4, 4, 2013265921),
    ("goldilocks", 96, 97, 8, 1, 18446744069414584321),
    ("goldilocks.ext2-binomial7", 99, 100, 8, 2, 18446744069414584321),
]


def head(tag):
    return b"ZKCV\x00" + bytes([tag])


def u32(n):
    return n.to_bytes(4, "little")


def word(n):
    return n.to_bytes(32, "big")


def sequence(children):
    return head(69) + u32(len(children)) + b"".join(u32(len(c)) + c for c in children)


def variant(tag, children=()):
    return head(65) + u32(tag) + b"".join(u32(len(c)) + c for c in children)


def indices(values):
    return head(68) + u32(len(values)) + b"".join(v.to_bytes(8, "little") for v in values)


def raw_bytes(value):
    return head(70) + u32(len(value)) + value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("consumer", "solc", "runner", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    parser.add_argument("--compiler", type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    for name in ("consumer", "solc", "runner"):
        setattr(args, name, getattr(args, name).resolve())
    check_solc(args.solc)
    artifacts = {}
    receipts = []

    def run(fixture, mode, frame, expected, *, error=None, memory=2_097_152):
        key = (fixture, mode, memory)
        if key not in artifacts:
            yul = subprocess.check_output(
                [str(args.consumer), "--emit", fixture, mode, str(memory)], text=True)
            artifact = compile_request(args.solc, {
                "language": "Yul", "sources": {"wire.yul": {"content": yul}},
                "settings": {"evmVersion": "cancun", "optimizer": PROFILES["colon"],
                             "outputSelection": {"*": {"*": ["evm.bytecode.object",
                                 "evm.deployedBytecode.object"]}}}})
            artifacts[key] = artifact
            (args.output / f"wire-{len(artifacts)}.yul").write_text(yul)
        result = execute(args.runner, artifacts[key], frame, gas=20_000_000)
        label = f"{fixture}/{mode}/{len(receipts)}"
        try:
            if error:
                check_revert(result, *error, [])
            else:
                check_return(result, expected.hex(), [])
        except AssertionError as cause:
            raise AssertionError(f"{label}: {cause}") from cause
        receipts.append({"fixture": fixture, "mode": mode, "frame": frame.hex(),
                         "expected": expected.hex(), "error": error,
                         "code_size": result["code_size"],
                         "gas": result["runtime_gas"],
                         "memory_high_water": result["memory_high_water"]})

    decode_length, decode_tag, decode_value = ("decode", 2), ("decode", 3), ("decode", 4)
    element_limit, wire_capacity = ("resource", 2), ("resource", 13)
    for domain, scalar_tag, vector_tag, width, degree, prime in FIELDS:
        values = [prime-1] + list(range(1, degree))
        scalar = head(scalar_tag) + b"".join(v.to_bytes(width, "little") for v in values)
        run(f"field:{domain}", "roundtrip", scalar, scalar)
        run(f"field:{domain}", "values", scalar, b"".join(word(v) for v in values))
        for broken, error in ((scalar[:-1], decode_length), (scalar + b"\x00", decode_length),
                              (scalar[:5]+b"\xff"+scalar[6:], decode_tag),
                              (head(scalar_tag)+prime.to_bytes(width, "little")+
                               scalar[6+width:], decode_value)):
            run(f"field:{domain}", "roundtrip", broken, b"", error=error)
        coefficients = [0] * degree + values + [prime-2] * degree
        vector = head(vector_tag)+u32(3)+b"".join(v.to_bytes(width, "little") for v in coefficients)
        run(f"vector:{domain}", "roundtrip", vector, vector)
        run(f"vector:{domain}", "values", vector, b"".join(word(v) for v in coefficients))
        empty = head(vector_tag)+u32(0)
        run(f"vector:{domain}", "roundtrip", empty, empty)
        for broken in (head(vector_tag)+u32(1025), head(vector_tag)+u32(2**32-1)):
            run(f"vector:{domain}", "roundtrip", broken, b"", error=element_limit)
        for broken, error in ((head(vector_tag)+u32(3), decode_length),
                              (vector[:-1], decode_length), (vector+b"\x00", decode_length),
                              (head(vector_tag)+u32(1)+prime.to_bytes(width, "little")+
                               b"\x00"*(width*(degree-1)), decode_value)):
            run(f"vector:{domain}", "roundtrip", broken, b"", error=error)

    # One extension element counts once, rather than once per coefficient.
    full = head(27)+u32(1024)+b"".join((i % 2130706433).to_bytes(4, "little")
                                      for i in range(1024*8))
    run("vector:koala-bear.ext8-binomial3", "roundtrip", full, full)
    for fixture, frame, values in [
        ("index", head(31)+(2**64-1).to_bytes(8, "little"), word(2**64-1)),
        ("bool", head(5)+b"\x01", word(1)),
        ("bytes", raw_bytes(b"\x00\xff\x00wire"), b"\x00\xff\x00wire"),
        ("bytes", raw_bytes(b""), b""),
        ("indices", indices([0, 2**64-1]), word(0)+word(2**64-1)),
        ("indices", indices([]), b""),
    ]:
        run(fixture, "roundtrip", frame, frame)
        run(fixture, "values", frame, values)
    run("bool", "roundtrip", head(5)+b"\x02", b"", error=decode_value)
    run("index", "roundtrip", head(31)+b"\x00"*9, b"", error=decode_length)
    full_bytes = raw_bytes(b"x"*65526)
    run("bytes", "roundtrip", full_bytes, full_bytes)
    run("bytes", "roundtrip", full_bytes+b"x", b"", error=wire_capacity)
    reserved = head(66)+u32(32)+b"\x00"*(32*32)
    run("vector:bls12-381.fr", "reserved", reserved, b"",
        error=wire_capacity, memory=8192)
    for fixture, frame in [("empty", variant(0)), ("sequence:empty", sequence([])),
                            ("sequence:empty", sequence([variant(0)])),
                            ("sequence:bytes", sequence([raw_bytes(b""), raw_bytes(b"hi")]))]:
        run(fixture, "roundtrip", frame, frame)
    run("empty", "roundtrip", variant(1), b"", error=decode_tag)
    run("empty", "roundtrip", variant(0)+u32(0), b"", error=decode_length)

    coefficients = [1, 2, 3, 4, 2130706432, 0, 7, 8]
    vector = head(22)+u32(2)+b"".join(v.to_bytes(4, "little") for v in coefficients)
    item = variant(1, [raw_bytes(b"\x00\xffnested"), head(31)+(2**64-1).to_bytes(8, "little"), vector])
    frame = variant(1, [sequence([variant(0), item]), indices([0, 2**64-1]), head(5)+b"\x01"])
    run("nested", "roundtrip", frame, frame)
    view = (word(1)+word(2)+word(0)+word(1)+word(8)+b"\x00\xffnested"+
            word(2**64-1)+word(2)+b"".join(word(v) for v in coefficients)+
            word(2)+word(0)+word(2**64-1)+word(1))
    run("nested", "values", frame, view)
    for broken, error in ((frame[:-1], decode_length), (frame+b"\x00", decode_length),
                          (variant(2), decode_tag),
                          (variant(1, [sequence([]), indices([])]), decode_length),
                          (variant(1, [sequence([item+b"\x00"]), indices([]), head(5)+b"\x01"]),
                           decode_length)):
        run("nested", "roundtrip", broken, b"", error=error)
    # Every local collection fits. The complete value exceeds the shared count.
    half = sequence([head(31)+b"\x00"*8] * 512)
    aggregate = sequence([half, half])
    run("sequence:sequence:index", "roundtrip", aggregate, b"", error=element_limit)
    # Numeric count fits exactly, but the extra value nodes exceed the ceiling.
    run("sequence:index", "roundtrip", sequence([head(31)+b"\x00"*8]*1024), b"", error=element_limit)
    # Byte leaves charge memory, even though they consume no numeric elements.
    many = sequence([raw_bytes(b"x"*32)]*20)
    run("sequence:bytes", "roundtrip", many, b"", error=wire_capacity, memory=8192)
    # A complete structural scan's resource refusal precedes a bad leaf value.
    bad_leaf = head(19)+(2130706433).to_bytes(4, "little")
    overcap = sequence([bad_leaf]+[head(19)+b"\x00"*4]*1023)
    run("sequence:field:koala-bear", "roundtrip", overcap, b"", error=element_limit)
    for count in (0, 4):
        array = head(64)+b"".join(v.to_bytes(32, "little") for v in range(count))
        run(f"array:{count}", "roundtrip", array, array)
        run(f"array:{count}", "values", array, b"".join(word(v) for v in range(count)))
        run(f"array:{count}", "roundtrip", array+b"\x00", b"", error=decode_length)
    envelopes = [
        ("rows.merkle-keccak256.koala-bear/0", 33, 34, 0, 0),
        ("rows.merkle-keccak256.koala-bear.ext8-binomial3/0", 35, 36, 0, 0),
        ("rows.merkle-keccak256.koala-bear.ext4-binomial3/0", 79, 80, 0, 0),
        ("rows.merkle-poseidon2-16.koala-bear/0", 71, 72, 4, 2130706433),
        ("rows.merkle-poseidon2-16.koala-bear.ext4-binomial3/0", 71, 72, 4, 2130706433),
        ("rows.merkle-poseidon2-16.baby-bear/0", 71, 72, 4, 2013265921),
        ("rows.merkle-poseidon2-16.baby-bear.ext4-binomial11/0", 71, 72, 4, 2013265921),
        ("rows.merkle-poseidon2-8.goldilocks/0", 71, 72, 8, 18446744069414584321),
        ("rows.merkle-poseidon2-8.goldilocks.ext2-binomial7/0", 71, 72, 8, 18446744069414584321),
    ]
    for scheme, root_tag, path_tag, width, prime in envelopes:
        digest = bytes(range(32)) if not width else b"".join(
            (prime-1-i).to_bytes(width, "little") for i in range(32//width))
        root = head(root_tag)+digest
        path = head(path_tag)+u32(2)+digest*2
        run(f"root:{scheme}", "roundtrip", root, root)
        run(f"root:{scheme}", "values", root, root)
        run(f"path:{scheme}", "roundtrip", path, path)
        run(f"path:{scheme}", "roundtrip", head(path_tag)+u32(0), head(path_tag)+u32(0))
        run(f"path:{scheme}", "roundtrip", path[:-1], b"", error=decode_length)
        run(f"root:{scheme}", "roundtrip", root+b"\x00", b"", error=decode_length)
        if width:
            broken = head(root_tag)+prime.to_bytes(width, "little")+digest[width:]
            run(f"root:{scheme}", "roundtrip", broken, b"", error=decode_value)
        else:
            run(f"path:{scheme}", "roundtrip", head(path_tag)+u32(25)+digest*25, b"", error=element_limit)
    if args.compiler:
        def compiled_source(text):
            process = subprocess.run([str(args.compiler.resolve()), "language-evm",
                "--source-format=zkc", "--entry=wirecase::Proof", "--module=wirecase=-"],
                input=text, text=True, capture_output=True, timeout=60)
            assert process.returncode == 0, process.stderr
            compiled = json.loads(process.stdout)
            built = compile_request(args.solc, {"language": "Yul",
                "sources": {"entry.yul": {"content": compiled["yul"]}},
                "settings": {"evmVersion": "cancun", "optimizer": PROFILES["colon"],
                    "outputSelection": {"*": {"*": ["evm.bytecode.object",
                        "evm.deployedBytecode.object"]}}}})
            return compiled, built

        def invocation(compiled, public, payload):
            descriptor, policy = compiled["descriptor"], compiled["policy"]
            rows = [[*r[:3], v.hex()] for r, v in zip(descriptor[4], public, strict=True)]
            root = encode_tree(["zkc.native-proof-binding/0", "sha256", descriptor[2],
                compiled["source_sha256"], *policy[1:4], descriptor, rows, ""])
            digest = hashlib.sha256(root).digest()
            trace = [{"kind": "sha256", "input": root.hex(), "output": digest.hex(),
                      "status": "return"}]
            return encode_verify(public, b"", b"ZKCPRF00"+digest+payload), trace

        text = ('module wirecase;domain F=field("koala-bear.ext4-binomial3");'
            'type Indices=builtin("indices");struct Empty {}'
            'protocol Check roles(P,V)(a:F@(P,V),xs:Indices@V)->'
            '(empty:Empty@V,extra:Indices@V,accepted:bool@V){'
            'let received=send P->V(a);return(empty=Empty{},extra=xs,accepted=received==a);} '
            'proof Proof=Check{prover P;verifier V;public{a,xs};accept accepted;construction authored;}')
        compiled, built = compiled_source(text)
        for accepted in (True, False):
            public = [head(21)+u32(1)+u32(2)+u32(3)+u32(4), indices([0, 2**64-1])]
            received = public[0] if accepted else head(21)+u32(5)+u32(2)+u32(3)+u32(4)
            payload = len(received).to_bytes(8, "little")+received
            for trailing in (b"", b"\x00"):
                calldata, trace = invocation(compiled, public, payload+trailing)
                result = execute(args.runner, built, calldata, gas=20_000_000)
                if trailing:
                    check_revert(result, "decode", 13, trace)
                else:
                    check_return(result, word(int(accepted)).hex(), trace)
                receipts.append({"fixture": "entry-acceptance-and-eof", "mode": "integration",
                    "accepted": accepted, "trailing": trailing.hex(),
                    "code_size": result["code_size"], "gas": result["runtime_gas"]})
        text = ('module wirecase;domain F=field("bls12-381.fr");'
            'fn inv(a:F)->F{return kernel<F>("field.inverse",a);} '
            'protocol Check roles(P,V)(a:F@V,value:F@P)->(accepted:bool@V){'
            'let checked@V=inv(a);let received=send P->V(value);'
            'return(accepted=received==checked);} '
            'proof Proof=Check{prover P;verifier V;public{a};accept accepted;construction authored;}')
        compiled, built = compiled_source(text)
        for malformed in (b"\xff"*8, (3).to_bytes(8, "little")+b"bad"):
            calldata, trace = invocation(compiled, [head(1)+b"\x00"*32], malformed)
            result = execute(args.runner, built, calldata, gas=20_000_000)
            check_revert(result, "source", 2, trace)
            receipts.append({"fixture": "source-stop-before-unreached-frame", "mode": "integration",
                "code_size": result["code_size"], "gas": result["runtime_gas"]})
    # Fresh-buffer writes follow a completed callback. These helper controls
    # isolate the store boundary; source collect ordering has separate controls.
    for ceiling in (4, 1024):
        yul = subprocess.check_output(
            [str(args.consumer), "--emit-store", str(ceiling)], text=True)
        artifact = compile_request(args.solc, {
            "language": "Yul", "sources": {"store.yul": {"content": yul}},
            "settings": {"evmVersion": "cancun", "optimizer": PROFILES["colon"],
                         "outputSelection": {"*": {"*": ["evm.bytecode.object",
                             "evm.deployedBytecode.object"]}}}})
        artifacts[("sequence:index", "store", ceiling)] = artifact
        (args.output / f"store-{ceiling}.yul").write_text(yul)
        for name, count, index, stop, get_only, error in [
            ("first", 1, 0, 0, 0, None),
            ("last", ceiling, ceiling-1, 0, 0, None),
            ("capacity", ceiling, ceiling, 0, 0, ("resource", 2)),
            ("beyond-capacity", ceiling, ceiling+1, 0, 0, ("resource", 2)),
            ("short-buffer", 1, 1, 0, 0, ("fault", 3)),
            ("empty-buffer", 0, 0, 0, 0, ("fault", 3)),
            ("callback-stop-before-capacity", ceiling, ceiling, 1, 0, ("source", 77)),
            ("get-bounds", ceiling, ceiling, 0, 1, ("source", 3)),
            ("get-empty", 0, 0, 0, 1, ("source", 3)),
            ("allocation-capacity", ceiling+1, 0, 0, 0, ("resource", 2)),
        ]:
            calldata = b"".join(map(word, (count, index, stop, get_only)))
            result = execute(args.runner, artifact, calldata, gas=20_000_000)
            if error:
                check_revert(result, *error, [])
            else:
                check_return(result, word(123).hex(), [])
            receipts.append({"fixture": "sequence:index", "mode": f"store-{name}",
                "ceiling": ceiling, "frame": calldata.hex(), "error": error,
                "expected": None if error else word(123).hex(),
                "code_size": result["code_size"], "gas": result["runtime_gas"]})
    # Operand admission precedes source byte validation, which precedes output
    # capacity and allocation. An invalid byte must not be masked at capacity.
    yul = subprocess.check_output([str(args.consumer), "--emit-append"], text=True)
    artifact = compile_request(args.solc, {
        "language": "Yul", "sources": {"append.yul": {"content": yul}},
        "settings": {"evmVersion": "cancun", "optimizer": PROFILES["colon"],
                     "outputSelection": {"*": {"*": ["evm.bytecode.object",
                         "evm.deployedBytecode.object"]}}}})
    artifacts[("bytes", "append", 32)] = artifact
    (args.output / "append.yul").write_text(yul)
    for count, value, reserved, error in (
            (0, 255, False, None), (31, 255, False, None),
            (0, 256, False, ("source", 3)), (31, 256, False, ("source", 3)),
            (32, 255, False, ("resource", 2)), (32, 256, False, ("source", 3)),
            (33, 256, False, ("resource", 13)),
            (31, 255, True, ("resource", 1)), (31, 256, True, ("source", 3))):
        result = execute(args.runner, artifact, word(count) + word(value) + word(reserved),
                         gas=20_000_000)
        if error:
            check_revert(result, *error, [])
        else:
            check_return(result, (bytes(range(count)) + bytes([value])).hex(), [])
        receipts.append({"fixture": "bytes", "mode": "append", "count": count,
                         "value": value, "reserved": reserved,
                         "error": error, "code_size": result["code_size"],
                         "gas": result["runtime_gas"]})
    receipt = {"cases": receipts, "artifacts": len(artifacts), "solc": "0.8.38",
               "max_code_size": max(r["code_size"] for r in receipts),
               "max_gas": max(r["gas"] for r in receipts)}
    (args.output / "receipt.json").write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "cases"} |
                     {"cases": len(receipts)}))


if __name__ == "__main__":
    main()
