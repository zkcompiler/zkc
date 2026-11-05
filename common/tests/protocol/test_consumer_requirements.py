"""Installed type-indexed consumer requirements through the default native Host."""

import hashlib
import json
from pathlib import Path

import pytest

from entry import joint_package


@pytest.mark.parametrize("record", [False, True])
@pytest.mark.parametrize("flags", [(), ("--no-simplify",)])
@pytest.mark.parametrize("manifest", [False, True])
def test_generic_relay_and_forward_execute(toolchain, journal, directory, record, flags, manifest):
    payload = "Packet" if record else "bool"
    declarations = "struct Packet:\n    pub bit: bool\n    pub count: index\n" if record else ""
    source = directory / "relay.zkc"
    source.write_text('''use zkc::relay::{Forward, NativeRelay}
''' + declarations + f'''pub protocol Demo roles(P, V)(x: {payload} @P) -> {payload} @V:
    y <- Forward<{payload}, NativeRelay>(x) @(P, V)
    return y
entry def Run(inputs: Demo::Inputs):
    result <- Demo::run(inputs)
    return result
''')
    package = directory / "relay.zkpkg"
    library = Path(__file__).resolve().parents[3] / "libraries/core/transport"
    compilation = None
    if manifest:
        project = directory / "zkc.toml"
        project.write_text('''format = "zkc.project/0"
source-format = "zkc-layout"
[modules]
relay = "relay.zkc"
[dependencies]
transport = ''' + json.dumps(str(library)) + "\n")
        compilation = journal.json([
            toolchain.runtime, "--json", "compile", "relay::Run",
            f"--compiler={toolchain.compiler}", f"--project={project}",
            f"--output={package}", *flags,
        ])
    else:
        package.write_text(journal.run([
            toolchain.compiler, "language-package", "--source-format=zkc-layout",
            f"--module=relay={source}", f"--module=zkc::relay={library / 'relay.zkc'}",
            "--entry=relay::Run", *flags,
        ]))
    original = joint_package(json.loads(package.read_text()))["original"]
    assert original.count('"protocol.exchange"') == (2 if record else 1)
    pin = hashlib.sha256(package.read_bytes()).hexdigest()
    if compilation is not None:
        assert compilation["package_sha256"] == pin
    for label, bit in [("false", False), ("true", True)]:
        value = {"bit": bit, "count": "7"} if record else bit
        inputs = journal.write(f"{label}.inputs.json", {"inputs": {"P": {"x": value}, "V": {}}})
        output = directory / f"{label}.outputs.json"
        report = journal.json([
            toolchain.runtime, "--json", "run", f"--package={package}",
            f"--sha256={pin}", f"--input={inputs}", f"--results={output}",
        ])
        assert report["status"] == "executed"
        assert json.loads(output.read_text())["value"] == {"P": {}, "V": {"result": value}}
