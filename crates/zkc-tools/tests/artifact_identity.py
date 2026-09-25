#!/usr/bin/env python3
"""Original-source identity vectors and cross-artifact construction tests.

Use --inspection-only to check library and explicit-source identity vectors.
Full mode also constructs artifacts and checks their source correspondence
using the compiler, native tools and independent Lean reference.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "tests/support"))
from journal import Journal, TIMEOUT, positive_timeout  # noqa: E402

p = argparse.ArgumentParser(description=__doc__)
for name in ("zkc", "compiler", "output-dir"):
    p.add_argument("--" + name, required=True)
p.add_argument("--lean")
p.add_argument("--fixture-exporter")
p.add_argument("--inspection-only", action="store_true")
p.add_argument("--reference", help="independent Lean artifact-reference")
p.add_argument("--primitive", help="public cryptographic primitive service")
p.add_argument("--timeout", type=positive_timeout, default=TIMEOUT)
a = p.parse_args()
assert a.inspection_only or (a.lean and a.fixture_exporter)
assert bool(a.reference) == bool(a.primitive)
out = Path(a.output_dir).resolve()
out.mkdir(parents=True, exist_ok=False)
repository = Path(__file__).resolve().parents[3]
checks = []
comparisons = []
memo = {}
journal = Journal(out / "commands", timeout=a.timeout)
if a.reference:
    sys.path.insert(0, str(repository / "tests/support"))
    from run_reference import run_reference


def call(argv):
    return journal.attempt(argv, text=False)


def save(name, value):
    path = out / (name + ".json")
    path.write_text(json.dumps(value))
    return path


def native(command, *paths):
    r = call([a.compiler, command, *paths])
    assert r.returncode == 0, (command, r.stderr.decode())
    return json.loads(r.stdout)


def common(source):
    return source[3] if source[0] == "zkc.library/1" else source


def walk(body):
    for op in body:
        if op[0] not in ("return", "yield"):
            yield op
        if op[0] == "loop":
            yield from walk(op[5])


def final_definition(source, name):
    configs = {c[1]: c for c in source[2]}
    while name in configs:
        name = configs[name][2]
    return name


def relabel(source, descriptor):
    source, descriptor = copy.deepcopy(source), copy.deepcopy(descriptor)
    maps = {}
    groups = [(common(source)[2], 4), (common(source)[3], 7)]
    if source[0] == "zkc.library/1":
        groups.append((source[1], 6))
    for records, body_index in groups:
        for record in records:
            sites = {op[1]: "alias" + str(n) for n, op in enumerate(walk(record[body_index]))}
            maps[record[1]] = sites
            for op in walk(record[body_index]):
                op[1] = sites[op[1]]
    if source[0] == "zkc.library/1":
        for config in source[2]:
            target = final_definition(source, config[1])
            for choice in config[4]:
                choice[0] = maps[target][choice[0]]
    for draw in descriptor[5][1]:
        target = draw[0]
        if target not in maps:
            target = final_definition(source, target)
        draw[1] = maps[target][draw[1]]
    return source, descriptor, maps


def rename_ssa(source):
    source = copy.deepcopy(source)

    def body(ops, env):
        def bind(name):
            env[name] = "renamed_" + name
            return env[name]
        for op in ops:
            tag = op[0]
            if tag in ("return", "yield"):
                op[1] = [env[v] for v in op[1]]
            elif tag in ("op", "local", "call"):
                # Inputs and outputs are the final two fields in each carrier.
                op[-2] = [env[v] for v in op[-2]]
                op[-1] = [bind(v) for v in op[-1]]
            elif tag == "message":
                op[5] = env[op[5]]
                op[6] = bind(op[6])
            elif tag == "loop":
                inner = {}
                for pair in op[3]:
                    inner[pair[0]] = "renamed_" + pair[0]
                    pair[0], pair[1] = inner[pair[0]], env[pair[1]]
                for capture in op[4]:
                    inner[capture] = env[capture]
                op[4] = [env[v] for v in op[4]]
                body(op[5], inner)
                op[6] = [bind(v) for v in op[6]]

    groups = [(common(source)[2], 2, 4, False), (common(source)[3], 4, 7, True)]
    if source[0] == "zkc.library/1":
        groups.append((source[1], 4, 6, False))
    for records, arg_index, body_index, public in groups:
        for record in records:
            env = {p[0]: p[0] if public else "renamed_" + p[0] for p in record[arg_index]}
            if not public:
                for port in record[arg_index]:
                    port[0] = env[port[0]]
            body(record[body_index], env)
    return source


def inspect(name, source, descriptor, config=None):
    argv = [a.zkc, "inspect-artifact-identity", save(name + ".source", source),
            save(name + ".descriptor", descriptor)]
    if config is not None:
        argv.append(save(name + ".configuration", config))
    r = call(argv)
    assert r.returncode == 0, (name, r.stdout.decode(), r.stderr.decode())
    result = json.loads(r.stdout)
    assert result["admission"] == "not-checked"
    if a.reference:
        reference = call([a.reference, "identity", *argv[2:]])
        assert reference.returncode == 0, (name, reference.stdout.decode())
        tree = json.loads(reference.stdout)
        assert tree[0] == "zkc.identity-inspection/1"
        assert tree[1:4] == [result[k] for k in
                            ("resolved_source", "resolved_descriptor", "normalized_protocol")], name
        if config is not None:
            assert tree[4] == result["resolved_configuration"], name
        comparisons.append({"name": name, "kind": "identity", "status": "equal"})
    save(name + ".identity", result)
    checks.append(name)
    return result


def encode(value):
    if isinstance(value, str):
        data = value.encode()
        return b"\0" + len(data).to_bytes(8, "little") + data
    assert isinstance(value, list)
    return b"\1" + len(value).to_bytes(8, "little") + b"".join(map(encode, value))


def expected_binding(source, descriptor, inputs, identity):
    by_name = {r[0]: r for r in inputs[2]}
    public = [by_name[r[0]] for r in descriptor[4]]
    # One root tag: the descriptor inside names the identity policy.
    if descriptor[8] == "normalized":
        tree = ["zkc.artifact-binding/1", identity["normalized_protocol"], identity["resolved_descriptor"],
                inputs[1], public, identity["resolved_configuration"]]
    else:
        tree = ["zkc.artifact-binding/1", source, descriptor, inputs[1], public, inputs[4]]
    return hashlib.sha256(encode(tree)).hexdigest()


def nominal(kind):
    """The full spelling of a logical kind, for a record that carries a bare one.

    The fixtures wrote bare kinds once and write full spellings now, so this
    has to leave one alone rather than give it a second domain.
    """
    if kind == "bool" or ":" in kind:
        return kind
    domain = "bls12-381.g1" if kind in ("group", "groups") else (
        "multilinear.kzg.bls12-381/1" if kind in ("commitment", "proof", "verifier_key", "prover_key") else "bls12-381.fr")
    return kind + ":" + domain


def inputs2(value, assignments, receives):
    value = copy.deepcopy(value)
    value[0] = "zkc.artifact-inputs/1"
    for r in value[2]:
        r[1] = nominal(r[1])
    for r in value[3]:
        if r[1] not in ("rng", "nonce", "prover_key_file"):
            r[1] = nominal(r[1])
    value[4] = ["zkc.public-configuration/1", [[r[0], nominal(r[1]), r[2]] for r in value[4][1]], assignments, receives]
    return value


def construct(name, source, descriptor):
    sp, dp = save(name + ".source", source), save(name + ".descriptor", descriptor)
    result = native("protocol-construct", sp, dp)
    assert result[0] == "zkc.construction-result/1" and result[1] == descriptor
    physical = native("protocol-compile", save(name + ".common", result[2]))
    return [sp, dp, save(name + ".construction", result), save(name + ".physical", physical)], physical


def execute(name, paths, inputs, proof, producer=False, code=None):
    input_path = save(name + ".inputs", inputs)
    r = call([a.zkc, "produce-artifact" if producer else "validate-artifact", *paths,
              input_path, a.compiler, a.lean, proof, "10000"])
    result = json.loads(r.stdout)
    if code:
        assert r.returncode == 1 and result["code"] == code, (name, result)
    else:
        assert r.returncode == 0 and result["status"] == ("produced" if producer else "accepted"), (name, result)
    save(name + ".report", result)
    checks.append(name)
    # A forged compiler manifest is rejected at custody checking; the source
    # interpreter intentionally does not consume that manifest. Compare actual
    # source executions and root refusals here, with full public primitive calls.
    if a.reference and not producer and code in (None, "proof-header"):
        ref = run_reference(a.reference, a.primitive, paths[0], paths[1], input_path,
                            proof, out / (name + ".reference"), memo=memo,
                            transcript_budget=10000)
        assert ref[0] == "zkc.artifact-observation/1", (name, ref)
        assert (ref[1][0] == "accepted") == (code is None), (name, ref[1], result)
        assert ref[2] == result["events"], (name, "events", ref[2], result["events"])
        assert int(ref[4]) == result["proof_bytes"], (name, "proof cursor")
        assert int(ref[5]) == sum(e[0] == "challenge" for e in result["events"])
        assert int(ref[6]) == sum(e[0] in ("message", "challenge") for e in result["events"])
        comparisons.append({"name": name, "kind": "execution", "status": "equal",
                            "outcome": ref[1][0], "events": len(ref[2]),
                            "proof_bytes": int(ref[4])})
    return result


if not a.inspection_only:
    r = call([a.fixture_exporter, out])
    assert r.returncode == 0, r.stderr.decode()

for client in ("dleq", "committed-two-factor"):
    original_library = native("protocol-source", repository / "tests/fixtures" / ("generic-" + client + ".pir"))
    explicit = native("protocol-prepare", save(client + ".library", original_library))
    descriptor = json.loads((repository / "examples/protocols" / (client + ".construction.json")).read_text())
    descriptor[8] = "normalized"
    for flavor, source in [("generic", original_library), ("explicit", explicit)]:
        name = client + "-" + flavor
        baseline = inspect(name, source, descriptor)
        relabelled, desc2, maps = relabel(source, descriptor)
        variants = [("labels", relabelled, desc2), ("ssa", rename_ssa(source), descriptor)]
        unused = copy.deepcopy(source)
        common(unused)[2].append(["function", "Unused", [], [], [["return", []]], ["Unused", []]])
        variants.append(("unused", unused, descriptor))
        reordered = copy.deepcopy(source)
        for group in common(reordered)[1:]:
            group.reverse()
        if flavor == "generic":
            reordered[1].reverse()
            reordered[2].reverse()
        variants.append(("order", reordered, descriptor))
        choices = copy.deepcopy(source)
        changed_choices = 0
        if flavor == "explicit":
            for binding in common(choices)[1]:
                old = binding[0]
                binding[0] = "alias_" + old
                for function in common(choices)[2]:
                    for op in function[4]:
                        if op[0] == "op" and op[2] == old:
                            op[2] = binding[0]
                if binding[1] == "poly.fold":
                    binding[3] = "arkworks/poly.fold" if binding[3] == "arkworks-msb/poly.fold" else "arkworks-msb/poly.fold"
                    changed_choices += 1
        else:
            definitions = {d[1]: d for d in choices[1]}
            for config in choices[2]:
                for op in definitions[final_definition(choices, config[1])][6]:
                    if op[0] == "op" and op[2] == "poly.fold":
                        previous = dict(config[4]).get(op[1])
                        config[4] = [r for r in config[4] if r[0] != op[1]]
                        config[4].append([op[1], "arkworks/poly.fold" if previous == "arkworks-msb/poly.fold" else "arkworks-msb/poly.fold"])
                        changed_choices += 1
                    elif client == "dleq" and op[0] == "op" and op[2] == "curve.scale":
                        config[4].append([op[1], "arkworks/curve.scale"])
        if client == "committed-two-factor":
            assert changed_choices > 0
        variants.append(("implementation", choices, descriptor))
        for label, changed, d in variants:
            vector = inspect(name + "-" + label, changed, d)
            assert vector["normalized_protocol"] == baseline["normalized_protocol"], (name, label)
            assert vector["resolved_descriptor"] == baseline["resolved_descriptor"], (name, label)
            assert vector["source_sha256"] != baseline["source_sha256"], (name, label)
        if a.inspection_only:
            continue
        paths, physical = construct(name, source, descriptor)
        # Recover original application selectors independently from source, only
        # for this harness. Production Rust does not receive this map.
        instances = {r[1]: r[2] for r in common(source)[4]}
        original_sites = {r[1]: [op[1] for op in walk(r[7])] for r in common(source)[3]}
        receives = []
        for participant in physical[4]:
            for op in walk(participant[7]):
                if op[0] == "receive" and op[5].split(":")[0] in ("commitment", "proof"):
                    assert op[1].startswith("site")
                    site = original_sites[instances[participant[2]]][int(op[1][4:])]
                    receives.append([participant[2], participant[3], site, "vk"])
        assignments = [] if client == "dleq" else [["V", "expected_f", "vk"], ["V", "expected_g", "vk"]]
        prod, val = [inputs2(json.loads((out / (client + "." + role + ".json")).read_text()), assignments, receives)
                     for role in ("producer", "validator")]
        vector = inspect(name + "-configured", source, descriptor, val[4])
        proof = out / (name + ".proof")
        produced = execute(name + "-produce", paths, prod, proof, True)
        accepted = execute(name + "-validate", paths, val, proof)
        assert produced["binding_sha256"] == accepted["binding_sha256"] == expected_binding(source, descriptor, val, vector)
        reordered_inputs = copy.deepcopy(val)
        reordered_inputs[2].reverse()
        reordered_result = execute(name + "-input-order", paths, reordered_inputs, proof)
        assert reordered_result["binding_sha256"] == accepted["binding_sha256"]
        for label, changed, d in variants:
            changed_paths, _ = construct(name + "-" + label, changed, d)
            changed_val = copy.deepcopy(val)
            if label == "labels":
                for r in changed_val[4][3]:
                    r[2] = maps[instances[r[0]]][r[2]]
            checked = execute(name + "-cross-" + label, changed_paths, changed_val, proof)
            assert checked["binding_sha256"] == accepted["binding_sha256"]
            assert checked["events"] == accepted["events"], (name, label, "source events")
        changed = copy.deepcopy(val)
        changed[1] = "01"
        execute(name + "-context", paths, changed, proof, code="proof-header")
        d = copy.deepcopy(descriptor)
        d[4].reverse()
        changed_paths, _ = construct(name + "-public-order", source, d)
        execute(name + "-public-order", changed_paths, val, proof, code="proof-header")
        # Removing a verifier guard leaves a well-formed algorithm, but it is a
        # different protocol even when this particular honest execution passes.
        without_guard = copy.deepcopy(source)
        removed = False
        bindings = {b[0]: b[1] for b in common(without_guard)[1]}
        definitions = ([(f, 6, True) for f in without_guard[1]] if flavor == "generic"
                       else [(f, 4, False) for f in common(without_guard)[2]])
        for function, body_index, generic in definitions:
            for index, operation in enumerate(function[body_index]):
                if operation[0] == "op" and (operation[2] if generic else
                                               bindings[operation[2]]) == "control.require":
                    function[body_index].pop(index)
                    removed = True
                    break
            if removed:
                break
        assert removed, name
        changed_paths, _ = construct(name + "-guard", without_guard, descriptor)
        execute(name + "-guard", changed_paths, val, proof, code="proof-header")
        # Whole ORIGINAL admission rejects a malformed unused function even
        # though it would be excluded from selected identity. Candidate is honest.
        invalid = copy.deepcopy(source)
        common(invalid)[2].append(["function", "InvalidUnused", [["x", "bool"]], ["field:bls12-381.fr"],
                                  [["return", ["x"]]], ["InvalidUnused", []]])
        bad_paths = list(paths)
        bad_paths[0] = save(name + ".invalid-unused", invalid)
        execute(name + "-invalid-unused", bad_paths, val, proof, code="artifact-construction-refused")
        # Forged construction operation map cannot establish correspondence.
        construction = json.loads(paths[2].read_text())
        assert construction[4]
        construction[4][0][5] = "forged_source_site"
        bad_paths = list(paths)
        bad_paths[2] = save(name + ".forged-map", construction)
        execute(name + "-forged-map", bad_paths, val, proof, code="artifact-construction-refused")
        # Exact identity retains its whole-source root interpretation.
        old = copy.deepcopy(descriptor)
        old[8] = "exact"
        old_paths, _ = construct(name + "-old", source, old)
        old_proof = out / (name + ".old.proof")
        old_result = execute(name + "-old-produce", old_paths, prod, old_proof, True)
        execute(name + "-old-validate", old_paths, val, old_proof)
        execute(name + "-old-input-order", old_paths, reordered_inputs, old_proof)
        assert old_result["binding_sha256"] == expected_binding(source, old, val, None)
        assert old_result["binding_sha256"] != accepted["binding_sha256"]

summary = {"status": "pass", "mode": "inspection-only" if a.inspection_only else "execution",
           "checks": checks, "comparisons": comparisons,
           "tools": {name: {"path": getattr(a, name),
               "sha256": hashlib.sha256(Path(getattr(a, name)).read_bytes()).hexdigest()}
               for name in ("zkc", "compiler", "lean", "reference", "primitive") if getattr(a, name)}}
save("summary", summary)
print(json.dumps({"status": "pass", "mode": summary["mode"], "checks": len(checks)}))
