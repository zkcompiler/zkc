#!/usr/bin/env python3
"""Check structured constructor strings with Lean's actual parser and kernel."""

import argparse
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import support.evidence  # noqa: E402
import support.lake  # noqa: E402

spec = importlib.util.spec_from_file_location("structured_snapshot", HERE / "bridges/structured/snapshot.py")
renderer = importlib.util.module_from_spec(spec)
spec.loader.exec_module(renderer)


def check(output, lake):
    output.mkdir(parents=True, exist_ok=True)
    names = ["plain", 'quote"slash\\literal\\u0041', "line\nreturn\rtab\t",
             "\x00\x08\x0c\x1f\x7f", "증명_α_🙂", "α" * 256,
             '"\nend Rendered\naxiom injected : False\n--']
    modules = []
    for index, name in enumerate(names):
        helper = ["function", name, "math", "private", [["bool"]], [["bool"]], [], [],
                  ["block", [], ["return", [0]]]]
        entry = ["function", "main", "protocol", "public", [["bool"]], [["bool"]], [], [],
                 ["block", [[["call", name], [0], [["bool"]], [], ""]], ["return", [0]]]]
        data = ["zkc.structured-source/0", "original", "sha256:" + "0" * 64,
                "main", "P", [], [helper, entry]]
        namespace = f"RenderedCase{index}"
        if index == 4:
            # Exercise the actual CLI under an ASCII locale as well as the
            # in-process renderer. File encoding must not depend on the host.
            snapshot_path = output / "unicode.json"
            snapshot_path.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
            rendered_path = output / "Unicode.lean"
            environment = dict(os.environ, LC_ALL="C", PYTHONUTF8="0", PYTHONCOERCECLOCALE="0")
            subprocess.run([sys.executable, renderer.__file__, snapshot_path, rendered_path,
                            "--namespace", namespace], env=environment, check=True, timeout=30)
            assert rendered_path.read_bytes() == renderer.render(data, namespace).encode("utf-8")
        source = renderer.render(data, namespace).replace("module\n\n", "", 1)
        # Numeric codepoints are an independent expectation; never render this
        # expected value through the string function being tested.
        points = str([ord(char) for char in name])
        source += f'''
example : ({namespace}.snapshot.definitions[0]?.map
    (fun definition => definition.name.toList.map Char.toNat)) = some {points} := by
  decide +kernel
example : (Zkc.Source.Structured.check {namespace}.snapshot).isOk = true := by
  decide +kernel
'''
        modules.append(source)
    # Imports/section commands from each rendering are legal at the file top
    # only. One import serves all independently named data declarations.
    header = "import Zkc.Source.Structured.Import\nset_option maxRecDepth 4096\n"
    bodies = [source.replace("public import Zkc.Source.Structured.Import\n", "")
              .replace("@[expose] public section\n", "") for source in modules]
    path = output / "Rendered.lean"
    path.write_text(header + "\n".join(bodies), encoding="utf-8")
    run = subprocess.run([lake, "env", "lean", path], cwd=HERE,
                         capture_output=True, encoding="utf-8", timeout=60)
    (output / "lean.log").write_text(run.stdout + run.stderr, encoding="utf-8")
    if run.returncode:
        raise AssertionError(run.stdout + run.stderr)
    for invalid in ["α" * 257, "🙂" * 129, "\ud800"]:
        try:
            renderer.text(invalid)
        except ValueError:
            continue
        raise AssertionError("renderer accepted an invalid or oversized UTF-8 string")
    report = {"status": "pass", "kernel_cases": len(names), "refusal_cases": 3,
              "ascii_locale_cli_cases": 1,
              "renderer_sha256": support.lake.sha(Path(renderer.__file__)),
              "subject_sha256": support.lake.sha(path)}
    (output / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=support.evidence.records("structured-renderer"))
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    print(json.dumps(check(args.output.resolve(), support.lake.resolve(args.lake)), indent=2))
