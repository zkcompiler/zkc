"""Validate extension declarations with installed tools and schemas only."""

import argparse
import json
from pathlib import Path
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--tool", required=True, type=Path)
    parser.add_argument("--include", action="append", default=[])
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="zkc-installed-declarations-") as temporary:
        source = Path(temporary) / "declarations.td"

        def generate(action, text, refused=None):
            source.write_text(text)
            command = [str(args.tool), action]
            for directory in args.include:
                command.extend(["-I", directory])
            result = subprocess.run([*command, str(source)], text=True, capture_output=True)
            if refused:
                assert result.returncode != 0 and refused in result.stderr, result.stderr
            else:
                assert result.returncode == 0, result.stderr
            return result.stdout

        installed = 'include "zkc/Contracts/Installation.td"\n'
        before = json.loads(generate("-dump-contract-declarations", installed))
        added = '''defset list<ZKC_Declaration> MoreRecords = {
  def NewValue : ZKC_Type<"installed_check_value">;
}
def More : ZKC_Contribution<"installed-check", ["base"], MoreRecords>;
'''
        after = json.loads(generate("-dump-contract-declarations", installed + added))
        assert len(after["types"]) == len(before["types"]) + 1
        assert any(row["name"] == "installed_check_value" for row in after["types"])
        generate("-dump-contract-declarations", installed + added.replace('["base"]', '["absent"]'),
                 "missing contribution dependency")
        generate("-dump-contract-declarations", installed + added +
                 'def Duplicate : ZKC_Contribution<"installed-check", [], []>;',
                 "duplicate contribution identifier")
        native = 'include "zkc/Dialect/Installation.td"\n'
        generate("-gen-type-bindings", native)
        generate("-gen-contract-mappings", native)
        generate("-gen-type-bindings", native +
                 'def Unowned : ZKC_Type<"unowned">;', "no contribution owner")
        extra = added
        generate("-gen-type-bindings", native + extra, "missing native binding decision")
        generate("-gen-type-bindings", native + extra +
                 'def Unavailable : ZKC_UnavailableBinding<NewValue, "logical-only fixture">;')
        print("Installed declaration tools: composition and missing-support controls passed")


if __name__ == "__main__":
    main()
