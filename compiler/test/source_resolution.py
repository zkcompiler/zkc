"""Source-derived occurrence resolution without weakening construction custody."""

import copy
import json
from pathlib import Path
from commands import Commands
from tools import corpus, examples, records



commands = Commands(records())


def run(mode, source, *paths, refuses=None):
    """A source given as text or as the record it serializes to."""
    printed = commands.source(mode, source if isinstance(source, str) else json.dumps(source),
                              *paths, refuses=refuses)
    if refuses:
        assert commands.last.returncode == 1, commands.last.stderr
    return printed


def relabel(body, mapping, prefix="renamed_"):
    for operation in body:
        if operation[0] in ("return", "yield"):
            continue
        before = operation[1]
        operation[1] = prefix + before
        mapping[before] = operation[1]
        if operation[0] == "loop":
            relabel(operation[5], mapping, prefix)


def sites(body):
    result = []
    for operation in body:
        if operation[0] in ("return", "yield"):
            continue
        result.append(operation[1])
        if operation[0] == "loop":
            result.extend(sites(operation[5]))
    return result


# The directory name carries a space on purpose: a tool that split
# its arguments would fail here and nowhere else.
temporary = records() / 'site resolution'
temporary.mkdir()
directory = Path(temporary)
for name in ("dleq", "committed-two-factor"):
    path = corpus / f"generic-{name}.pir"
    source = json.loads(run("protocol-source", path.read_text()))
    text = (examples / f"{name}.construction.pir").read_text()
    # Normalized identity is the default and the explicit clause means the
    # same; exact identity is chosen by its clause and differs only there.
    descriptor = json.loads(run("protocol-source", text))
    explicit = json.loads(run(
        "protocol-source", text.replace("construction main {",
                                        "construction main identity normalized {")))
    exact = json.loads(run(
        "protocol-source", text.replace("construction main {",
                                        "construction main identity exact {")))
    assert descriptor == explicit and descriptor[8] == "normalized", descriptor
    assert exact == [*descriptor[:8], "exact"], exact
    assert json.loads(run("protocol-source", run("protocol-format", descriptor))) == descriptor
    descriptor_path = directory / "descriptor.json"
    descriptor_path.write_text(json.dumps(descriptor))
    result = json.loads(run("protocol-construct", source, descriptor_path))
    assert result[0] == "zkc.construction-result/1" and result[1] == descriptor
    generated = result[2]
    for definition in source[1]:
        configs = [c for c in source[2] if c[2] == definition[1]]
        for config in configs:
            function = next(f for f in generated[2] if f[1] == config[1])
            assert sites(function[4]) == [f"site{i}" for i in range(len(definition[6]) - 1)]

    changed = copy.deepcopy(source)
    definition_maps = {}
    for definition in changed[1]:
        mapping = definition_maps[definition[1]] = {}
        relabel(definition[6], mapping)
    for config in changed[2]:
        for choice in config[4]:
            choice[0] = definition_maps[config[2]][choice[0]]
    for protocol in changed[3][3]:
        relabel(protocol[7], {})
    relabelled_descriptor = copy.deepcopy(descriptor)
    for draw in relabelled_descriptor[5][1]:
        config = next(c for c in changed[2] if c[1] == draw[0])
        draw[1] = definition_maps[config[2]][draw[1]]
    descriptor_path.write_text(json.dumps(relabelled_descriptor))
    other = json.loads(run("protocol-construct", changed, descriptor_path))
    # Original local algorithms now have identical resolved sites. Full
    # candidates remain distinct because checking binds the original source.
    original_names = {c[1] for c in source[2]}
    assert [f for f in result[2][2] if f[1] in original_names] == [
        f for f in other[2][2] if f[1] in original_names
    ]
    assert result != other
    candidate_path = directory / "candidate.json"
    candidate_path.write_text(json.dumps(other))
    run("protocol-check-construction", changed, descriptor_path, candidate_path)
    candidate_path.write_text(json.dumps(result))
    run("protocol-check-construction", changed, descriptor_path, candidate_path,
        refuses="construction-candidate-mismatch")

    bad_descriptor = copy.deepcopy(relabelled_descriptor)
    bad_descriptor[5][1][0][1] = "unknown"
    descriptor_path.write_text(json.dumps(bad_descriptor))
    run("protocol-construct", changed, descriptor_path, refuses="source-site-selection")
    descriptor_path.write_text(json.dumps(relabelled_descriptor))
    bad = copy.deepcopy(changed)
    bad[1].append(["generic_function", "UnusedInvalid", [], [], [], [],
                   [["op", "x", "unknown.operation", [], [], [], []], ["return", []]]])
    run("protocol-construct", bad, descriptor_path, refuses="generic-operation")

    # Construction uses the same lossless string syntax as other source
    # commands. LLVM JSON's replacement of isolated surrogates is not an
    # acceptable interpretation of a public binding label, in either mode.
    for identity in ("exact", "normalized"):
        malformed = copy.deepcopy(descriptor)
        malformed[8] = identity
        malformed[4][0][0] = "\ud800"
        descriptor_path.write_text(json.dumps(malformed))
        run("protocol-construct", source, descriptor_path, refuses="source-string")
        run("protocol-check-construction", source, descriptor_path,
            candidate_path, refuses="source-string")

# Selectors from the generic fixture must not resolve in an unrelated source.
concrete_source = json.loads((examples / "dleq.json").read_text())
descriptor_path.write_text(json.dumps(descriptor))
run("protocol-construct", concrete_source, descriptor_path, refuses="source-site-selection")

print(f"source resolution: {commands.save()} command checks, group and polynomial/PCS custody controls")
