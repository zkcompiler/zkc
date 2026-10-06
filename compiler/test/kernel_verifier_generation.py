#!/usr/bin/env python3
"""Check standard ODS forwarding coverage and the exact coarse carrier role."""
import json
from pathlib import Path
import re
import subprocess

from cases import case, counted
from tools import records as evidence, tool
from types import SimpleNamespace


def main():
    compiler_generator = tool("tablegen")
    settings = json.loads((compiler_generator.parent / "generation-settings.json").read_text())
    args = SimpleNamespace(tblgen=settings["mlir_tablegen"],
                           record_tblgen=settings["llvm_tablegen"],
                           source_include=settings["source_include"],
                           dependency_include=settings["dependency_include"])
    command = [args.tblgen, "-I", args.source_include]
    for path in args.dependency_include:
        command += ["-I", path]
    command.append(str(Path(args.source_include) / "zkc/Dialect/IR.td"))
    records = json.loads(subprocess.check_output([args.record_tblgen, *command[1:], "--dump-json"], text=True))
    generated = subprocess.check_output([*command, "-gen-op-defs"], text=True)
    output = evidence("kernel-verifier-generation")
    (output / "records.json").write_text(json.dumps(records))
    (output / "operations.cpp.inc").write_text(generated)
    standard = records["!instanceof"]["KernelOp"]
    with case("nonempty standard kernel inventory"):
        assert standard
    for name in standard:
        with case("standard verifier forwarding: " + name):
            record = records[name]
            assert record["hasVerifier"] == 1
            assert "verifyLogicalKernel" in record["extraClassDefinition"]
            assert re.search(r"\b" + re.escape(name) + r"::verify\(\)\s*\{\s*"
                             r"return ::zkc::detail::verifyLogicalKernel\(getOperation\(\)\);\s*\}",
                             generated), name
    for name in records["!instanceof"]["Op"]:
        if name in standard:
            continue
        with case("nonstandard verifier preserved: " + name):
            assert "verifyLogicalKernel" not in (records[name].get("extraClassDefinition") or "")
    with case("exact coarse predicate and summary"):
        role = records["Zkc_ProtocolData"]
        predicate = records[role["predicate"]["def"]]["predExpr"]
        # The named predicate keeps generated verifiers independent of concrete
        # dialect type headers. Semantic admission is exercised by kernel tests.
        assert predicate == "(::zkc::detail::isLogicalKernelData($_self))", predicate
        assert role["summary"] == "logical protocol data or capability"
    print(f"{counted()} verifier generation cases exercised ({len(standard)} standard kernels)")


if __name__ == "__main__":
    main()
