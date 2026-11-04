"""Independent affine controls for production BLS G1 codec/precompile helpers.

Uses the existing C++ helper emitter and pinned solc/revm infrastructure. The
Python arithmetic is a test oracle, not a production execution route. These
helper controls check results and hash frontiers. The separate curve_closure
consumer checks native proofs and complete physical ModExp/ADD/MSM traces.
"""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess

from probe import check_solc, compile_request, execute
from validate import check_return, check_revert
from wire_controls import head, sequence, settings, variant, word


# EIP-2537 curve parameters. Native compression: ark-bls12-381 0.6.0
# curves/{g1,util}.rs; the wrapper additionally requires exact re-encoding.
P = int("1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241"
        "eabfffeb153ffffb9feffffffffaaab", 16)
R = int("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001", 16)
G = (int("17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586"
         "c55e83ff97a1aeffb3af00adb22c6bb", 16),
     int("08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd"
         "03cc744a2888ae40caa232946c5e7e1", 16))


def add(a, b):
    if a is None:
        return b
    if b is None:
        return a
    x, y = a
    u, v = b
    if x == u and (y + v) % P == 0:
        return None
    slope = ((3*x*x) * pow(2*y, -1, P) if a == b
             else (v-y) * pow(u-x, -1, P)) % P
    result_x = (slope*slope-x-u) % P
    return result_x, (slope*(x-result_x)-y) % P


def scale(a, scalar):
    result = None
    while scalar:
        if scalar & 1:
            result = add(result, a)
        a = add(a, a)
        scalar >>= 1
    return result


def compressed(point):
    if point is None:
        return b"\xc0" + bytes(47)
    x, y = point
    flags = 0x80 | (0x20 if y > (-y) % P else 0)
    return bytes([flags | (x >> 376)]) + x.to_bytes(48, "big")[1:]


def frame(point):
    return head(9) + compressed(point)


def affine(point):
    if point is None:
        return bytes(128)
    return b"".join(c.to_bytes(64, "big") for c in point)


def scalar_frame(scalar):
    return head(1) + scalar.to_bytes(32, "little")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("consumer", "solc", "runner", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    args = parser.parse_args()
    for name in ("consumer", "solc", "runner", "output"):
        setattr(args, name, getattr(args, name).resolve())
    args.output.mkdir(parents=True, exist_ok=True)
    check_solc(args.solc)
    artifacts, receipts = {}, []

    def run(label, command, data, expected=b"", error=None, fork="osaka", gas=None):
        key = tuple(command), fork
        if key not in artifacts:
            yul = subprocess.check_output([str(args.consumer), *command], text=True)
            artifact = compile_request(args.solc, {
                "language": "Yul", "sources": {"curve.yul": {"content": yul}},
                "settings": settings(fork)})
            name = f"curve-{len(artifacts)}"
            (args.output / f"{name}.yul").write_text(yul)
            (args.output / f"{name}.json").write_text(json.dumps(artifact, indent=2)+"\n")
            artifacts[key] = artifact
        artifact = artifacts[key]
        result = execute(args.runner, artifact, data, gas)
        try:
            if error is None:
                check_return(result, expected.hex(), [])
            else:
                check_revert(result, *error, [])
        except AssertionError as cause:
            raise AssertionError(f"{label}/{fork}: {cause}") from cause
        receipts.append({"label": label, "fork": fork, "input": data.hex(),
                         "expected": expected.hex(), "error": error,
                         "creation_sha256": hashlib.sha256(bytes.fromhex(artifact["creation"])).hexdigest(),
                         "runtime_sha256": hashlib.sha256(bytes.fromhex(artifact["runtime"])).hexdigest(),
                         "result": result})

    # Reference sanity includes subgroup membership and nontrivial points.
    assert G[1]*G[1] % P == (G[0]**3+4) % P
    assert scale(G, R) is None
    assert scale((0, 2), R) is not None
    negative = (G[0], P-G[1])
    points = [None, G, negative, scale(G, 2), scale(G, 3), scale(G, 17)]
    assert (compressed(G)[0] ^ compressed(negative)[0]) == 0x20
    word_base = 1 << 256
    ph, pl = divmod(P, word_base)
    low_borrow = pl + 1
    assert 0 < low_borrow < P
    assert (-low_borrow) % P == (ph-1)*word_base + word_base-1
    half = (P-1)//2
    # Both midpoint comparisons require the low word; 1 and P-1 instead
    # compare against their negatives with different high words.
    assert half >> 256 == (half+1) >> 256
    assert 1 >> 256 != (P-1) >> 256
    # Canonical cube root of 2^256-1. Python pow authenticates this fixture
    # independently of the emitted ModExp and rhs helpers. Adding four must
    # carry from the low word to the high word without reducing modulo p.
    carry_x = int("1819d1be5dd50af41864af757cac03b6a364dd7c52d8f653779ff902c461c298e"
                  "a99a82f3ba2d08749c90aa1f02dab1f", 16)
    assert 0 <= carry_x < P
    assert pow(carry_x, 3, P) == word_base-1
    assert (pow(carry_x, 3, P)+4) % P == word_base+3
    assert (pow(P-1, 3, P)+4) % P == 3
    for fork in ("prague", "osaka"):
        for i, point in enumerate(points):
            for mode, expected in (("roundtrip", frame(point)), ("values", affine(point))):
                run(f"point-{i}/{mode}", ["--emit", "group:bls12-381.g1", mode],
                    frame(point), expected, fork=fork)
            run(f"unused-{i}", ["--emit-g1", "unused"], frame(point), word(1), fork=fork)
        children = [frame(point) for point in points]
        run("nested", ["--emit", "sequence:group:bls12-381.g1", "roundtrip"],
            sequence(children), sequence(children), fork=fork)
        for a, b in ((G, None), (None, G), (G, negative), (G, G), (points[3], points[5])):
            run("addition", ["--emit-g1", "add"], frame(a)+frame(b), frame(add(a, b)), fork=fork)
            run("equality", ["--emit-g1", "equal"], frame(a)+frame(b), word(a == b), fork=fork)
        for scalar in (0, 1, 2, R-1):
            run(f"scale-{scalar}", ["--emit-g1", "scale"], frame(G)+scalar_frame(scalar),
                frame(scale(G, scalar)), fork=fork)
        for point in (None, G):
            run("self-equality", ["--emit-g1", "equal"], frame(point)*2, word(1), fork=fork)

        payload = compressed(G)
        nonsquare_x = next(x for x in range(1, 100) if pow((x**3+4) % P, (P-1)//2, P) == P-1)
        noncanonical_x = bytearray(P.to_bytes(48, "big"))
        noncanonical_x[0] |= 0x80
        nonsquare = bytearray(nonsquare_x.to_bytes(48, "big"))
        nonsquare[0] |= 0x80
        invalid = {
            "short": (head(9)+payload[:-1], 2),
            "long": (head(9)+payload+b"\x00", 2),
            "tag": (head(0xff)+payload, 3),
            "uncompressed": (head(9)+bytes([payload[0] & 0x7f])+payload[1:], 4),
            "infinity-sign": (head(9)+b"\xe0"+bytes(47), 4),
            "infinity-payload": (head(9)+b"\xc0"+bytes(46)+b"\x01", 4),
            "x-at-modulus": (head(9)+bytes(noncanonical_x), 4),
            "x-all-bits": (head(9)+b"\x9f"+b"\xff"*47, 4),
            "nonsquare": (head(9)+bytes(nonsquare), 4),
            # Native blst/Arkworks negative fixture: (0,2) has order three.
            "outside-subgroup": (head(9)+b"\x80"+bytes(47), 4),
        }
        for name, (bad, code) in invalid.items():
            run(name, ["--emit", "group:bls12-381.g1", "roundtrip"], bad,
                error=("decode", code), fork=fork)
        bad = invalid["outside-subgroup"][0]
        run("unused-outside-subgroup", ["--emit-g1", "unused"], bad,
            error=("decode", 4), fork=fork)
        run("outside-subgroup-scaled-zero", ["--emit-g1", "scale"], bad+scalar_frame(0),
            error=("decode", 4), fork=fork)
        run("nested-outside-subgroup", ["--emit", "sequence:group:bls12-381.g1", "roundtrip"],
            sequence([frame(G), bad]), error=("decode", 4), fork=fork)
        # Later malformed scalar must not bypass an earlier group admission.
        run("ordered-point-before-scalar", ["--emit-g1", "scale"], bad+scalar_frame(R),
            error=("decode", 4), fork=fork)
        run("noncanonical-scalar", ["--emit-g1", "scale"], frame(G)+scalar_frame(R),
            error=("decode", 4), fork=fork)
        run("empty-success-missing-precompile", ["--emit-g1", "missing"], frame(G),
            error=("fault", 32), fork=fork)
        for tag, children in ((0, [frame(G), scalar_frame(3)]),
                              (1, [scalar_frame(3), frame(G)])):
            mixed = variant(tag, children)
            run("mixed-roundtrip", ["--emit", "group-scalar", "roundtrip"], mixed,
                mixed, fork=fork)
        # Distinct outcomes prove child order inside a single aggregate: an
        # earlier missing MSM faults, but an earlier bad scalar decodes first.
        run("mixed-group-before-scalar", ["--emit-g1", "mixed-missing"],
            variant(0, [frame(G), scalar_frame(R)]), error=("fault", 32), fork=fork)
        run("mixed-scalar-before-group", ["--emit-g1", "mixed-missing"],
            variant(1, [scalar_frame(R), frame(G)]), error=("decode", 4), fork=fork)
        for expected_size in (48, 128):
            for actual_size in (0, expected_size-1, expected_size+1):
                for decoding in (0, 1):
                    run("precompile-output-size", ["--emit-g1", "status"],
                        b"".join(word(v) for v in (1, actual_size, expected_size, decoding)),
                        error=("fault", 32), fork=fork)
            run("precompile-exact-size", ["--emit-g1", "status"],
                b"".join(word(v) for v in (1, expected_size, expected_size, 0)), word(1), fork=fork)
        for decoding, error in ((0, ("fault", 32)), (1, ("decode", 4))):
            run("precompile-status", ["--emit-g1", "status"],
                b"".join(word(v) for v in (0, 0, 128, decoding)), error=error, fork=fork)
        run("precompile-failure-payload", ["--emit-g1", "status"],
            b"".join(word(v) for v in (0, 32, 128, 1)), error=("fault", 32), fork=fork)
        run("underfunded-preflight", ["--emit-g1", "fund"], word(65536),
            error=("resource", 30), fork=fork, gas=60000)
        # Direct production-helper controls use Python integer arithmetic as
        # the oracle, including low-word borrow and negation of zero.
        for name, value in (("zero", 0), ("one", 1), ("low-equal", pl),
                            ("low-borrow", low_borrow), ("low-max", word_base-1),
                            ("high-word", word_base), ("maximum", P-1)):
            data = value.to_bytes(64, "big")
            expected = ((-value) % P).to_bytes(64, "big")
            run(f"negative-{name}", ["--emit-g1", "negative"], data, expected, fork=fork)
            run(f"negative-twice-{name}", ["--emit-g1", "negative"],
                expected, data, fork=fork)
        for name, value, sign in (("zero", 0, 0), ("one", 1, 0),
                                  ("half-lower", half, 0), ("half-upper", half+1, 1),
                                  ("maximum", P-1, 1)):
            assert int(value > (-value) % P) == sign
            run(f"sign-{name}", ["--emit-g1", "sign"], value.to_bytes(64, "big"),
                word(sign), fork=fork)
        for name, value in (("zero", 0), ("one", 1), ("generator", G[0]),
                            ("reduction", P-1), ("low-carry", carry_x)):
            expected = ((pow(value, 3, P)+4) % P).to_bytes(64, "big")
            run(f"rhs-{name}", ["--emit-g1", "rhs"], value.to_bytes(64, "big"),
                expected, fork=fork)
        # Direct wide-ModExp comparisons against Python pow, including an
        # exponent spanning two EVM words. Adapter carry/borrow/sign are above.
        for a, exponent in ((0, 0), (P-1, 3), (G[0], 3), (4, (P+1)//4), (P-2, 2)):
            data = b"".join(word(v) for v in (a >> 256, a % 2**256,
                                               exponent >> 256, exponent % 2**256))
            expected = pow(a, exponent, P).to_bytes(64, "big")
            run("wide-modexp", ["--emit-g1", "modexp"], data, expected, fork=fork)

    (args.output / "receipts.json").write_text(json.dumps({
        "scope": "helper codec and affine oracle; no native proof or curve-call trace coverage",
        "cases": receipts}, indent=2)+"\n")
    print(f"{len(receipts)} BLS G1 helper controls passed")


if __name__ == "__main__":
    main()
