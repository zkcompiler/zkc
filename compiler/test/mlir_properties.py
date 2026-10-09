"""Owned MLIR properties must be refused before generated conversion drops them."""

import json
import re

from cases import case
from commands import Commands
from tools import ROOT, records


commands = Commands(records())
UNKNOWN = "mlir-unknown-property"

# MLIR's generated custom prop-dict parser bypasses the registered conversion
# hook. A dialect adopting it needs its own strict parser before this guard can
# be removed. Generic <{...}> assembly is covered below and by properties.cpp.
for declaration in sorted((ROOT / "compiler/include/zkc").rglob("*.td")):
    with case(f"strict custom property path: {declaration.name}"):
        code = re.sub(r"//[^\n]*|/\*.*?\*/", "", declaration.read_text(),
                      flags=re.DOTALL)
        assert not re.search(r"\bprop-dict\b", code), declaration


def properties(text, operation, change):
    """Change only the first selected operation's explicit property dictionary."""
    pattern = re.escape(f'"{operation}"') + r'\([^\n)]*\) <\{(.*?)\}>'
    match = re.search(pattern, text)
    assert match, operation
    start, end = match.span(1)
    changed = change(text[start:end])
    assert changed != text[start:end], operation
    return text[:start] + changed + text[end:]


def extra(text, operation, key="surprise"):
    return properties(text, operation,
                      lambda fields: fields + f', {key} = "must-not-disappear"')


def reject_both(label, text, code=UNKNOWN, export="protocol-export"):
    # Independent cases: failure in the optimizer must not hide the compiler.
    with case(f"{label}: optimizer"):
        commands.verified(text, code)
    with case(f"{label}: compiler"):
        commands.source(export, text, refuses=code)


source = (ROOT / "compiler/test/fixtures/mathematical/local-execution.mlir").read_text()
for mode, options, families in (
    ("mathematical", [], (
        ("protocol.module", "profile"), ("local.binding", "contract"),
        ("protocol.func", "sym_name"), ("protocol.local_call", "callee"),
        ("algebra.exec.field_add", "binding"), ("local.if", "site"))),
    ("physical", ["--zkc-participant-pipeline"], (
        ("protocol.module", "profile"), ("protocol.participant", "instance"),
        ("protocol.entry", "targets"), ("plan.kernel", "site"),
        ("local.if", "site"))),
):
    ir = commands.verified(source, None, *options, "--mlir-print-op-generic")
    if mode == "physical":
        expected = json.loads(commands.source("protocol-export", ir))
        printed = commands.verified(ir)
        assert json.loads(commands.source("protocol-export", printed)) == expected
    for operation, required in families:
        reject_both(f"{mode}: {operation} extra field", extra(ir, operation))
        typo = properties(ir, operation, lambda fields: re.sub(
            rf"\b{required}\s*=", f"{required}_typo =", fields, count=1))
        reject_both(f"{mode}: {operation} required-field typo", typo)
    reject_both(f"{mode}: namespaced property",
                extra(ir, "protocol.module", "debug.note"))
    no_fields = re.sub(r'("local.yield"\([^\n)]*\))',
                       r'\1 <{surprise = "must-not-disappear"}>', ir, count=1)
    assert no_fields != ir
    reject_both(f"{mode}: empty property schema", no_fields, "empty properties")

for operation in ("poly.exec.fold", "pcs.exec.commit", "oracle.exec.commit", "relation.r1cs"):
    malformed = (f'module {{ "{operation}"() '
                 '<{surprise = "must-not-disappear"}> : () -> () }')
    reject_both(f"{operation}: conversion precedes verification", malformed)

# A relation exercises custom assembly, optional generic printing, typed casts
# in another exporter, and the shared dialect base outside the protocol family.
relation = ["zkc.relation.r1cs/0", "koala-bear", "4", "1", "1",
            [[[["2", "1"]], [["3", "1"]], [["1", "1"]]]]]
relation_ir = commands.source("relation-import", json.dumps(relation), "Circuit")
with case("relation: custom and generic assembly preserve valid properties"):
    generic = commands.verified(relation_ir, None, "--mlir-print-op-generic")
    assert json.loads(commands.source("relation-export", generic)) == relation
    assert json.loads(commands.source("relation-export", relation_ir)) == relation
with case("relation: generic property mutation"):
    generic = commands.verified(relation_ir, None, "--mlir-print-op-generic")
    reject_both("relation export: unknown property", extra(generic, "relation.r1cs"),
                export="relation-export")

print(f"MLIR property admission: {commands.save()} tool checks")
