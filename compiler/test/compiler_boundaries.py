"""Exercise source/MLIR expansion, lossless labels, and pass scope through CLI."""
import json
from pathlib import Path
from commands import Commands
from tools import compiler, examples, optimizer, records

root = Path(__file__).resolve().parents[2]

commands = Commands(records())


def run(tool, *args, text, refuses=None):
    """What the tool printed, which a refusal leaves empty."""
    return commands.run([tool, *args], stdin=text, refuses=refuses)

body = [["op", f"s{i}", "bool.and", [], ["v0", "v0"], [f"v{i+1}"]]
        for i in range(16000)] + [["return", ["v16000"]]]
source = ["zkc.protocol/1", [["bool.and", "bool.and", [], ""]],
          [["function", "many", [["v0", "bool"]], ["bool"], body, ["many", []]]], [], [], []]
text = json.dumps(source, separators=(",", ":"))
assert len(text) < 1024 * 1024
ir = run(compiler, "protocol-import", "-", text=text)
assert len(ir) > 1024 * 1024
assert json.loads(run(compiler, "protocol-export", "-", text=ir)) == source
run(optimizer, "--lower-pir-to-plan", text=ir, refuses="expected-finite-program")
# The pair is the claim: source input and MLIR input have separate budgets, a
# megabyte and sixty-four. The first row also appears in the frontend's table of
# malformed shapes, where it is one shape among many rather than half of this.
run(compiler, "protocol-source", "-", text=" " * (1024 * 1024 + 1), refuses="byte-limit")
run(compiler, "protocol-export", "-", text=" " * (64 * 1024 * 1024 + 1), refuses="byte-limit")
for mode in ("protocol-export", "export"):
    run(compiler, mode, "-", text="module {\n" * 65 + "}\n" * 65,
        refuses="mlir-depth-limit")

run(compiler, "protocol-admit", str(examples / "two-factor.construction.pir"),
    text="", refuses="interactive-format")

source = json.loads((Path(root) / "examples/tables/source.json").read_text())
for spelling in [r"\uD800", r"\uDC00", r"\uD800\u0041"]:
    source[3][0] = "unicode_placeholder"
    text = json.dumps(source).replace("unicode_placeholder", spelling)
    run(compiler, "compile", "-", text=text, refuses="invalid-json")
for label in ["한글", "😀"]:
    source[3][0] = label
    result = run(compiler, "compile", "-", text=json.dumps(source))
    assert json.loads(result)[7][0] == label
print(f"compiler boundaries: {commands.save()} checks; MLIR expansion, separate budgets, Unicode identity, pass scope")
