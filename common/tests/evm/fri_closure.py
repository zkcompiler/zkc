"""Prepare a Direct quartic Keccak FRI proof for independent parent validation.

Without --expected this writes preparation receipts only. Deployed validation
requires an independently authored, proof-pinned COMPLETE primitive trace. This
adapter deliberately does not infer expected traces from target output.
"""

import argparse
import hashlib
import json
from pathlib import Path

from authentication_controls import Controls, FIXTURES
from coset_reference import CosetReference
from foundation_controls import check_native_outcome, field_wire, index_wire, vector_wire
from oracle_deployment import table_realization
from probe import check_solc
from source_modules import library_modules


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("compiler", "native-driver", "solc", "runner", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    parser.add_argument("--sampling", choices=("scalar", "block"), default="scalar")
    parser.add_argument("--grouping", choices=("individual", "antipodal-pairs"), default="individual")
    parser.add_argument("--table-order", choices=("natural", "bit-reversed"), default="natural")
    parser.add_argument("--authentication", choices=("per-query", "atomic-blocks"), default="per-query")
    parser.add_argument("--expected", type=Path,
                        help="independent JSON: proof_sha256, fork, trace, evm_revert (null or [class,code])")
    args = parser.parse_args()
    for name in ("compiler", "native_driver", "solc", "runner", "output"):
        setattr(args, name, getattr(args, name).resolve())
    check_solc(args.solc)
    controls = Controls(args)
    module = "fri_keccak_block" if args.sampling == "block" else "fri_keccak"
    field = "koala-bear.ext4-binomial3"
    selection = table_realization(f"rows.merkle-keccak256.{field}/0",
                                  grouping=args.grouping, table_order=args.table_order,
                                  authentication=args.authentication)
    subject = controls.compile(module, (FIXTURES / f"{module}.zkc").read_text(), module,
                               (*library_modules("protocols/polynomial/fri"), selection))
    ref, shift = CosetReference(field), (3, 1, 0, 0)
    coefficients = [(i + 1, i * i, 2 * i, 1) for i in range(8)]
    word = [ref.horner(coefficients, point) for point in ref.domain(shift, 32)]
    wires = {0: vector_wire(field, word), 1: field_wire(field, shift),
             2: index_wire(3), 3: index_wire(8)}
    # Native budget is independent of the unchanged deployment limit of 64.
    fixture = controls.native(subject, "honest", wires, budget=4096)
    check_native_outcome(fixture, True, None)
    proof = bytes.fromhex(fixture["proof"])
    outputs = fixture["outputs"]
    positions_frame = bytes.fromhex(outputs["2"])
    if (positions_frame[:10] != b"ZKCV\x00\x44" + (8).to_bytes(4, "little")
            or len(positions_frame) != 74):
        raise AssertionError("native FRI did not return eight canonical indices")
    positions = [int.from_bytes(positions_frame[i:i + 8], "little") for i in range(10, 74, 8)]
    if any(position >= 32 for position in positions):
        raise AssertionError("native FRI returned an out-of-range query")
    if outputs["3"] != vector_wire(field, [word[position] for position in positions]).hex():
        raise AssertionError("authenticated native values differ from independent polynomial evaluation")
    report = {"status": "prepared-awaiting-independent-trace", "sampling": args.sampling,
              "selection": selection, "parameters": [5, 0, 3, 8],
              "production_security": False, "proof_sha256": hashlib.sha256(proof).hexdigest(),
              "fork": subject[2]["fork"], "positions": positions}
    (subject[0] / "honest.proof").write_bytes(proof)
    (subject[0] / "preparation.json").write_text(json.dumps(report, indent=2) + "\n")
    if args.expected:
        expected = json.loads(args.expected.read_text())
        if (set(expected) != {"proof_sha256", "fork", "trace", "evm_revert"}
                or expected["proof_sha256"] != report["proof_sha256"]
                or expected["fork"] != report["fork"]):
            raise AssertionError("independent expectation does not pin this proof and fork")
        controls.check(subject, "honest", wires, fixture=fixture,
                       complete_trace=expected["trace"], revert=expected["evm_revert"])
        (subject[0] / "validation.json").write_text(json.dumps(controls.cases, indent=2) + "\n")
        report["status"] = "validated-against-independent-expectation"
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
