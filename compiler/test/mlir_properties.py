"""Owned MLIR properties must be refused before generated conversion drops them."""

import json
import re

from cases import case
from commands import Commands
from tools import ROOT, corpus, records


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


source = (corpus / "local-control.pir").read_text()
for mode, import_command, families in (
    ("common", "protocol-import", (
        ("pir.module", "stage"),
        ("pir.operation_binding", "contract"),
        ("pir.protocol", "sym_name"),
        ("pir.instance", "protocol"),
        ("pir.entry", "targets"),
        ("pir.local_call", "callee"),
        ("algebra.sum", "binding"),
        ("pir.local_if", "site"),
        ("pir.local_for", "site"),
    )),
    ("physical", "protocol-physical-ir", (
        ("pir.module", "stage"),
        ("pir.participant", "instance"),
        ("plan.kernel", "site"),
        ("pir.local_if", "site"),
        ("pir.local_for", "site"),
    )),
):
    ir = commands.source(import_command, source)
    with case(f"{mode}: valid properties and typed operation registration"):
        expected = json.loads(commands.source("protocol-export", ir))
        printed = commands.verified(ir)
        assert json.loads(commands.source("protocol-export", printed)) == expected

    for operation, required in families:
        reject_both(f"{mode}: {operation} extra field", extra(ir, operation))
        typo = properties(ir, operation, lambda fields: re.sub(
            rf"\b{required}\s*=", f"{required}_typo =", fields, count=1))
        reject_both(f"{mode}: {operation} required-field typo", typo)

    # A namespaced key is still unknown when placed in the owned dictionary.
    reject_both(f"{mode}: namespaced property",
                extra(ir, "pir.module", "debug.note"))

    with case(f"{mode}: ordinary unknown module attribute stays refused"):
        prefix, suffix = ir.rsplit("}) : () -> ()", 1)
        ordinary = prefix + '}) {surprise = "retained"} : () -> ()' + suffix
        commands.source("protocol-export", ordinary,
                        refuses="interactive-module")

    # Property-free terminators already reject nonempty property dictionaries
    # in MLIR itself. The asserted prose here belongs to upstream MLIR, not a
    # stable zkc identifier. Do not turn this into a successful no-op.
    no_fields = re.sub(r'("pir.local_yield"\([^\n)]*\))',
                       r'\1 <{surprise = "must-not-disappear"}>', ir, count=1)
    assert no_fields != ir
    reject_both(f"{mode}: empty property schema", no_fields, "empty properties")

common = commands.source("protocol-import", source)
with case("discardable debug metadata survives optimizer"):
    # pir.module already has a closed exporter schema. Use an operation that
    # admits discardable metadata so this tests preservation of that policy.
    metadata = '''module {
      "claim.kind"() <{sym_name = "K", types = [], meaning = "example"}>
        {debug.note = "retained"} : () -> ()
    }'''
    assert 'debug.note = "retained"' in commands.verified(metadata)

with case("ordinary unknown operation attribute stays refused"):
    match = re.search(r'"algebra.sum"[^\n]*?\}>', common)
    assert match
    ordinary = (common[:match.end()] + ' {surprise = "retained"}'
                + common[match.end():])
    commands.source("protocol-export", ordinary,
                    refuses="interactive-unknown-attribute")

# The registration policy also covers dialects absent from this protocol.
# These deliberately incomplete operations must fail at property conversion,
# before their operand/type/domain verifiers could reject the incomplete shape.
for operation in ("poly.fold", "pcs.commit", "oracle.commit", "claim.kind",
                  "relation.r1cs"):
    malformed = (f'module {{ "{operation}"() '
                 '<{surprise = "must-not-disappear"}> : () -> () }')
    reject_both(f"{operation}: conversion precedes verification", malformed)

# A relation exercises custom assembly, optional generic printing, typed casts
# in another exporter, and the shared dialect base outside the protocol family.
relation = ["zkc.relation.r1cs/1", "koala-bear", "4", "1", "1",
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
