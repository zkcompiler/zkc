"""Execute exact fixed-roster successors with internally constructed resources."""

import hashlib
from pathlib import Path

import pytest

FIXTURE = (Path(__file__).resolve().parents[3] /
           "compiler/test/fixtures/language/distributed-succession.zkc")


@pytest.mark.parametrize("selected", [False, True])
@pytest.mark.parametrize("trips", [0, 1, 3])
@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
def test_distributed_succession_executes(toolchain, journal, directory, trips, flags, selected):
    code = FIXTURE.read_text().replace("0..3", f"0..{trips}")
    if selected:
        code = code.replace("        next <- state.advance()", """        next = if i == index<0>() roles(P, V):
            selected <- state.advance()
            selected
        else:
            selected <- state.advance()
            twice <- selected.advance()
            twice""")
    source = directory / "succession.zkc"
    source.write_text(code)
    bundle = directory / "succession.bundle"
    bundle.write_text(journal.run([
        toolchain.compiler, "language-bundle", "--source-format=zkc-layout",
        "--subject=m::Run", f"--module=m={source}", *flags,
    ]))
    # Resources are created inside Run. Native ingress has no data, service or
    # custody inputs. This also keeps the separate function Entry schema
    # migration outside the succession test's execution boundary.
    roles = [f"role{i:08x}" for i in range(3)]
    request = journal.write("inputs.json", ["zkc.bundle-inputs/0", "succession",
                                           [[r, [], []] for r in roles], []])
    pin = hashlib.sha256(bundle.read_bytes()).hexdigest()
    report = journal.json([
        toolchain.runtime, "--json", "bundle", "run", bundle, pin, request,
    ])
    assert report["status"] == "executed"
    assert report["outcome"] == ["completed"]
    outputs = {r["role"]: r["outputs"] for r in report["roles"]}
    wire = b"ZKCV\x00\x1f" + (24 + 2 * trips + (max(0, trips - 1) if selected else 0)).to_bytes(8, "little")
    assert outputs == {roles[0]: [["wire", "index@native.index/0", wire.hex()]],
                       roles[1]: [], roles[2]: []}
