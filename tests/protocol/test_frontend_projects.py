"""Five-family project integration: real execution and bounded source evidence.

No builds happen here; the compiler, Rust and Lean binaries come from the toolchain.
Groth16 proving and the native CheckedIndex seam live in the companion Rust test;
source admission below does not stand in for either proving path.
"""
import copy
import hashlib
import json
from pathlib import Path
import re
import shutil
import time

import pytest
from journal import Journal, names
from run_reference import run_reference

ROOT = Path(__file__).resolve().parents[2]
LIBRARIES = ROOT / "examples/libraries"
PROJECTS = ROOT / "examples/projects"


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, separators=(",", ":")) + "\n")
    return path


def options(libraries):
    return [f"--library={p}" for p in libraries]


def lower(tools, journal, authored, libraries, prefix="", relations=False):
    if relations:
        frozen = write(journal.directory / f"{prefix}snapshot.json", journal.json([
            tools.compiler, "protocol-resolve", authored, *options(libraries)]))
        common = journal.json([tools.compiler, "protocol-materialize", frozen])
    else:
        common = journal.json([tools.compiler, "protocol-source", authored, *options(libraries)])
    source = write(journal.directory / f"{prefix}source.json", common)
    journal.run([tools.compiler, "protocol-admit", source])
    checker = tools.checker("interactive-protocol")
    assert journal.json([checker, "--admit", source])[0] == "checked"
    physical = write(journal.directory / f"{prefix}physical.json", journal.json([
        tools.compiler, "protocol-compile", source]))
    assert journal.json([checker, "--check", source, physical])[0] == "checked"
    return source, physical


@pytest.mark.parametrize("family", ["groth16", "pcs", "air", "group", "views"])
def test_five_imported_sources_have_independent_carrier_checks(toolchain, directory, family):
    journal = Journal(directory)
    source, physical = lower(toolchain, journal, PROJECTS / family / "main.pir",
                             [LIBRARIES / family / "lib.pir"], relations=family == "groth16")
    # Named real primitives identify the executed path; a Boolean stand-in would
    # fail this structural check even if it returned the expected final bit.
    expected = {"groth16": ["pairing.check", "curve.msm", "matrix.mul_vector", "poly.coset_interpolate"],
                "pcs": ["pcs.check"], "air": ["poly.even_odd_fold", "poly.coset_interpolate", "oracle.open"],
                "group": ["random.draw", "curve.scale", "curve.equal"],
                "views": ["resource_unit.create", "resource_unit.consume", "control.require"]}
    text = source.read_text()
    for primitive in expected[family]:
        assert primitive in text, (family, primitive)
    write(directory / "admission.json", {"family": family, "status": "independently-admitted",
          "source_bytes": source.stat().st_size, "physical_bytes": physical.stat().st_size,
          "scope": "carrier admission only; see execution cases and Rust preparation tests"})


def bool_execution(tools, journal, source, physical, entry, ready, ok, label):
    checker = tools.checker("interactive-protocol")
    ports = {"ready": ready, "ok": ok}
    native = write(journal.directory / f"{label}-native-inputs.json", ["zkc.run/2", entry, "views", [],
        [["P", [], [[n, ["wire", (b"ZKCV\x01\x05" + bytes([v])).hex()]] for n, v in ports.items()], []]], []])
    reference = write(journal.directory / f"{label}-reference-inputs.json", ["zkc.reference-inputs/1", entry, "views",
        [["P", [[n, ["bool", str(v).lower()]] for n, v in ports.items()]]], [], [], []])
    actual = journal.json([tools.runtime, "run-protocol", source, physical, native, checker])
    expected = journal.json([checker, "--reference", source, reference])
    write(journal.directory / f"{label}-native.json", actual)
    write(journal.directory / f"{label}-reference.json", expected)
    assert actual["resources"] == [] and expected[5] == []
    assert actual["wire"]["messages"] == actual["wire"]["payload_bytes"] == 0
    return actual, expected


@pytest.mark.parametrize("layout", ["empty", "stored", "terminal"])
@pytest.mark.parametrize("count,trips", [("zero", 0), ("one", 1), ("many", 3)])
def test_opaque_views_execute_branches_traversal_and_terminal_stops(toolchain, directory, layout, count, trips):
    journal = Journal(directory)
    source, physical = lower(toolchain, journal, PROJECTS / "views/main.pir", [LIBRARIES / "views/lib.pir"])
    baseline, baseline_physical = lower(toolchain, journal, PROJECTS / "views/closed.pir", [], "closed-")
    for ready, ok in [(True, True), (False, True), (True, False), (False, False)]:
        label = f"{ready}-{ok}"
        native, reference = bool_execution(toolchain, journal, source, physical, layout + count, ready, ok, label)
        requests = [event[1][2] for event in reference[4] if event[0] == "request"]
        terminal = ok and layout == "terminal" and (trips > 0 or ready)
        if not ok:
            assert native["outcome"][0] == "stopped"
            assert reference[3][:2] == ["reject", "require"]
            assert requests == ["control.require"]
        elif terminal:
            assert native["outcome"][0] == "stopped"
            assert native["stop"]["detail"] == "refused"
            assert reference[3][:2] == ["refused", "explicit-stop"]
            # Invalid is a normal error arm, never recovery after a terminal stop.
        else:
            assert native["outcome"] == ["returned", {"P": [["bool", ready]]}]
            assert reference[3] == ["returned", [["bool", str(ready).lower()]]]
        if ok:
            assert requests.count("control.require") == trips + 1
            if layout == "empty":
                assert requests.count("resource_unit.create") == trips + 1
                assert requests.count("resource_unit.consume") >= trips
            elif layout == "stored":
                assert not any(r.startswith("resource_unit.") for r in requests)
        if layout != "terminal":
            direct, direct_ref = bool_execution(toolchain, journal, baseline, baseline_physical,
                                                "main", ready, ok, "closed-" + label)
            assert native["outcome"] == direct["outcome"]
            if ok:
                assert reference[3] == direct_ref[3]
            else:
                assert reference[3][:2] == direct_ref[3][:2]
                # Selected owner/entry origins intentionally differ from the closed model.
                assert reference[3][2] != direct_ref[3][2]


def artifact_inputs(family):
    def value(name, values):
        vector = isinstance(values, list)
        payload = len(values).to_bytes(4, "little") if vector else b""
        payload += b"".join(n.to_bytes(4, "little") for n in (values if vector else [values]))
        wire = b"ZKCV\x01" + bytes([20 if vector else 19]) + payload
        return [name, ("vector:" if vector else "field:") + "koala-bear", wire.hex()]
    public, private = [], []
    if family == "air":
        left = list(range(3, 11))
        right = [left[(5 * i + 1) % 8] for i in range(8)]
        sums = [sum(right[:i + 1]) for i in range(8)]
        public = [value("initial", left[0]), value("final_value", left[-1]), value("total", sums[-1])]
        private = [value("left", left), value("right", right), value("sum_values", sums)]
    validator = ["zkc.artifact-inputs/1", b"frontend-project-execution".hex(), public, [],
                 ["zkc.public-configuration/1", [], [], []]]
    producer = copy.deepcopy(validator)
    producer[3] = private
    return producer, validator


def artifact_case(tools, folder, authored, libraries, descriptor, family, bind=True):
    folder.mkdir(parents=True, exist_ok=True)
    journal = Journal(folder)
    source, _ = lower(tools, journal, authored, libraries)
    # Construct against the project: source-level selectors are resolved in the
    # same captured owner environment, never guessed from generated hash names.
    # An unbound descriptor already names the carrier's own declarations.
    subject = [authored, descriptor, *options(libraries)] if bind else [source, descriptor]
    built = journal.json([tools.compiler, "protocol-construct", *subject])
    construction = write(folder / "construction.json", built)
    bound_descriptor = write(folder / "descriptor.json", built[1])
    common = write(folder / "constructed.json", built[2])
    physical = write(folder / "constructed-physical.json", journal.json([
        tools.compiler, "protocol-compile", common]))
    producer, validator = artifact_inputs(family)
    producer_path = write(folder / "producer.json", producer)
    validator_path = write(folder / "validator.json", validator)
    proof = folder / "proof.bin"
    shared = [source, bound_descriptor, construction, physical]
    produce = journal.json([tools.runtime, "produce-artifact", *shared, producer_path,
        tools.compiler, tools.checker("interactive-protocol"), proof, 100000, "--trace=full"])
    validate = journal.json([tools.runtime, "validate-artifact", *shared, validator_path,
        tools.compiler, tools.checker("interactive-protocol"), proof, 100000, "--trace=full"])
    assert produce["status"] == "produced", produce
    assert validate["status"] == "accepted", validate
    reference = run_reference(tools.checker("artifact-reference"), tools.primitive, source, bound_descriptor,
                              validator_path, proof, folder / "reference")
    assert reference[1][0] == "accepted", reference
    assert reference[2] == validate["events"]
    write(folder / "producer-result.json", produce)
    write(folder / "validator-result.json", validate)
    tampered = folder / "tampered.bin"
    encoded = proof.read_bytes()
    assert encoded
    tampered.write_bytes(encoded[:-1] + bytes([encoded[-1] ^ 1]))
    bad = journal.attempt([tools.runtime, "validate-artifact", *shared, validator_path,
        tools.compiler, tools.checker("interactive-protocol"), tampered, 100000, "--trace=full"])
    refusal = json.loads(bad.stdout)
    assert refusal["status"] == "refused", refusal
    codes = {"rejected:require"} if family == "air" else {"rejected:require", "refused:invalid-encoding"}
    assert refusal["code"] in codes, refusal
    write(folder / "tamper-result.json", refusal)
    return journal, shared, producer, produce, validate


@pytest.mark.parametrize("family", ["air", "group"])
def test_complete_air_and_selected_group_execute_constructed_paths(toolchain, directory, family):
    imported = artifact_case(toolchain, directory / "imported", PROJECTS / family / "main.pir",
        [LIBRARIES / family / "lib.pir"], PROJECTS / family / "main.construction.pir", family)
    if family == "air":
        base = ROOT / "examples/protocols/air-oracle/air-permutation"
        authored, descriptor = base.with_suffix(".pir"), base.with_suffix(".construction.pir")
    else:
        authored, descriptor = PROJECTS / family / "closed.pir", PROJECTS / family / "closed.construction.pir"
    closed = artifact_case(toolchain, directory / "closed", authored, [], descriptor, family)
    # Transcript identity includes selected source origins. Different selections
    # may produce different challenges/proofs; never erase that distinction.
    write(directory / "comparison.json", {"imported": imported[4]["status"], "closed": closed[4]["status"],
        "construction_identity": "distinct source selections; proof bytes not asserted equal",
        "independent_reference": "each source replayed with exact public primitive requests",
        "scope": "complete N=8 AIR/FRI path" if family == "air" else "checked group/scalar and RNG helpers"})
    if family == "air":
        journal, shared, producer, _, _ = imported
        bad = copy.deepcopy(producer)
        # Short trace: valid codec, wrong actual AIR shape, not a syntax-only test.
        wire = bytes.fromhex(bad[3][0][2])
        bad[3][0][2] = (wire[:6] + (7).to_bytes(4, "little") + wire[10:-4]).hex()
        path = write(journal.directory / "short-trace.json", bad)
        result = journal.attempt([toolchain.runtime, "produce-artifact", *shared, path,
            toolchain.compiler, toolchain.checker("interactive-protocol"), journal.directory / "bad-proof.bin", 100000])
        report = json.loads(result.stdout)
        assert (report["status"], report["code"]) == ("refused", "rejected:require"), report
        write(journal.directory / "shape-refusal.json", report)


def replaced(text, *pairs):
    """Text with each edit made, failing if any edit found nothing to change.

    A mutation that silently matched nothing would leave the test checking the
    unmutated source, and an equality it asserts would hold trivially.
    """
    for old, new in pairs:
        assert old in text, old
        text = text.replace(old, new)
    return text


def edited(path, *pairs):
    """Rewrite a copied source with `replaced`."""
    path.write_text(replaced(path.read_text(), *pairs))


def copied_project(directory, family):
    library = directory / "library"
    shutil.copytree(LIBRARIES / family, library)
    app = directory / "main.pir"
    shutil.copyfile(PROJECTS / family / "main.pir", app)
    return app, library / "lib.pir"


@pytest.mark.parametrize("family,mutation,code", [
    ("group", "wrong-domain", "library-bound"),
    ("group", "rng-reuse", "library-resource-use"),
    ("views", "reuse-view", "library-resource-use"),
    ("views", "wrong-instance", "library-type-mismatch"),
    ("views", "private-layout", "source-name-private"),
    ("air", "wrong-domain", "source-call-type"),
    ("air", "private-schedule", "source-syntax"),
])
def test_family_source_mutations_refuse_exact_boundaries(toolchain, directory, family, mutation, code):
    app, library = copied_project(directory, family)
    text = library.read_text()
    if mutation == "wrong-domain" and family == "group":
        text = replaced(text, ('domain F: field = "bls12-381.fr";', 'domain F: field = "bn254.fr";'))
    elif mutation == "rng-reuse":
        text = replaced(text, ('return (scalar, after);',
            'let (again, reused) = random::draw::<"bls12-381.fr">(coins); return (again, reused);'))
    elif mutation == "reuse-view":
        text = replaced(text, ('let previous = C::finish(state, ok);',
                               'let previous = C::finish(state, ok); let twice = C::finish(state, ok);'))
    elif mutation == "wrong-instance":
        text = text[:-2] + '''
          fn Swap<A: ViewAPI, B: ViewAPI>(x: A::View) -> B::View { return x; }
        }'''
    elif mutation == "private-layout":
        edited(app, ('use views::{', 'use views::layouts::EmptyViews as Leaked; use views::{'))
    elif mutation == "wrong-domain" and family == "air":
        edited(app, ('P left: Vector<koala-bear::Element>', 'P left: Vector<bls12-381.fr::Element>'))
    elif mutation == "private-schedule":
        edited(app, ('    return (accepted_all);', '''
          match accepted_all capture() -> (scheduled) {
            Ready(tag) => { yield (tag); }
          }
          return (scheduled);'''))
    library.write_text(text)
    journal = Journal(directory)
    result = journal.attempt([toolchain.compiler, "protocol-source", app, *options([library])])
    assert result.returncode > 0 and names(result.stderr, code) and not result.stdout, result.stderr
    # Imported declaration failures retain the actual file, not application-only offsets.
    assert str(app) in result.stderr or str(library) in result.stderr


@pytest.mark.parametrize("family", ["pcs", "group", "views"])
def test_alias_relocation_visibility_and_body_controls(toolchain, directory, family):
    journal = Journal(directory)
    app, library = copied_project(directory, family)
    def source():
        return journal.json([toolchain.compiler, "protocol-source", app, *options([library])])
    original = source()
    alias = {"pcs": "pcs", "group": "group", "views": "views"}[family]
    edited(app, (f"dependency {alias} =", "dependency renamed ="), (f"use {alias}::", "use renamed::"))
    assert source() == original
    relocated = directory / "relocated"
    shutil.copytree(library.parent, relocated)
    library = relocated / "lib.pir"
    assert source() == original
    # Resolve body mutations before execution; common-consumer agreement alone
    # cannot catch an importer that dropped this edit for both consumers.
    text = library.read_text()
    if family == "pcs":
        text = replaced(text, ("return accepted;", "return false;"))
    elif family == "group":
        text = replaced(text, ("return same;", "return false;"))
    else:
        text = replaced(text, ("return answer;", "return false;"))
    library.write_text(text)
    assert source() != original
    # An exact declared resolution selects a different library, never a spelling match.
    edited(app, ('resolution="source-v1"', 'resolution="absent"'))
    journal.run([toolchain.compiler, "protocol-source", app, *options([library])],
                refuses="source-dependency-missing")


def capacity_project(directory, rows, depth, repeated, distinct, descriptors):
    """Separate relation-size, selection-depth, sharing and descriptor axes."""
    identity = 'library(namespace="zkc.examples.capacity", name="views", version="1", resolution="bounded")'
    library = directory / "lib.pir"
    declarations = [f"module {{ {identity};", '''
      pub interface Cell { type State drop; association Subject;
        local make(ok: bool) -> State; local finish(x: State, ok: bool) -> bool; }
      pub component Base<R: association>: Cell {
        type State = (); association Subject = R;
        local make(ok: bool) -> State { return (); }
        local finish(x: State, ok: bool) -> bool { return ok; }
      }
      pub component Wrap<C: Cell>: Cell {
        type State = C::State; association Subject = C::Subject;
        local make(ok: bool) -> State { return C::make(ok); }
        local finish(x: State, ok: bool) -> bool { return C::finish(x, ok); }
      }
      pub enum Packed<C: Cell> { Ready(C::State) }
      pub fn Run<C: Cell>(ok: bool) -> bool {
        let state = C::make(ok);
        let packed: Packed<C> = Packed::Ready(state);
        match packed capture(ok) -> (answer) {
          Ready(value) => { let answer = C::finish(value, ok); yield (answer); }
        }
        return answer;
      }
    ''']
    modulus = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    for selection in range(distinct):
        def coefficient(row, column):
            digest = hashlib.sha256(f"{selection}:{row}:{column}".encode()).digest()
            return str(1 + int.from_bytes(digest, "big") % (modulus - 1))
        relation = ["zkc.relation.r1cs/1", "bn254.fr", "3", "0", "1",
                    [[[[str(c), coefficient(r, c)]] for c in range(3)] for r in range(rows)]]
        write(directory / f"relation{selection}.json", relation)
        declarations.append(f'pub relation R{selection} = r1cs("relation{selection}.json");')
    # Separate repeated type occurrences from repeated selections.
    declarations.append('pub fn Descriptors<C: Cell>(x: (' + ', '.join(['Packed<C>'] * descriptors) + ')) -> bool effects (local) { return true; }')
    declarations.append('}')
    library.write_text('\n'.join(declarations))
    client = [f'module {{ dependency cap = {identity}; use cap::{{Cell, Base, Wrap, Run, Descriptors, Packed, ' + ', '.join(f'R{i}' for i in range(distinct)) + '};']
    for occurrence in range(repeated):
        selected = f'Base<R{occurrence % distinct}>'
        selected = 'Wrap<' * depth + selected + '>' * depth
        client.append(f'link Run{occurrence} = Run<{selected}>;')
        client.append(f'link Types{occurrence} = Descriptors<{selected}>;')
    client += ['protocol Demo { roles (P); inputs (P ok: bool); outputs (P bool);',
               'local P: let answer = Run0(ok); return answer; }',
               'instance run: Demo { roles (P = P); } entry main = run; }']
    app = directory / "main.pir"
    app.write_text('\n'.join(client))
    return app, library


@pytest.mark.parametrize("rows,depth,repeated,distinct,descriptors", [
    *[(rows, depth, 1, 1, 2) for rows in (1, 24, 200) for depth in (0, 1, 2, 3, 4, 8)],
    (24, 2, 8, 1, 2), (24, 2, 8, 8, 2), (24, 2, 1, 1, 16),
])
def test_bounded_relation_selection_descriptor_measurements(toolchain, directory, rows, depth, repeated, distinct, descriptors):
    app, library = capacity_project(directory, rows, depth, repeated, distinct, descriptors)
    journal = Journal(directory)
    measurement = {"rows": rows, "selection_depth": depth, "repeated_selections": repeated,
        "distinct_selections": distinct, "repeated_descriptors": descriptors, "full_width_coefficients": True,
        "timing_claim": "none", "stages": [], "status": "not-executed"}
    def stage(name, command):
        started = time.monotonic()
        result = journal.attempt(command)
        measurement["stages"].append({"stage": name, "returncode": result.returncode,
            "seconds": time.monotonic() - started, "stdout_bytes": len(result.stdout.encode()),
            "diagnostics": result.stderr, "outcome": result.stdout if result.returncode else "succeeded"})
        if result.returncode:
            measurement["status"] = "refused-at-" + name
        write(directory / "capacity.json", measurement)
        return result
    resolved = stage("resolve", [toolchain.compiler, "protocol-resolve", app, *options([library])])
    assert resolved.returncode == 0, resolved.stderr
    snapshot = write(directory / "snapshot.json", json.loads(resolved.stdout))
    materialized = stage("materialize", [toolchain.compiler, "protocol-materialize", snapshot])
    assert materialized.returncode == 0, materialized.stderr
    source = write(directory / "source.json", json.loads(materialized.stdout))
    checker = toolchain.checker("interactive-protocol")
    native_admit = stage("native-source-admission", [toolchain.compiler, "protocol-admit", source])
    reference = stage("lean-admission-and-expansion", [checker, "--admit", source])
    compiled = stage("native-expansion-and-compilation", [toolchain.compiler, "protocol-compile", source])
    measurement.update(snapshot_bytes=snapshot.stat().st_size, source_bytes=source.stat().st_size)
    if depth >= 4:
        # This is the measured 128-byte occurrence-path boundary. C++ admits
        # unexpanded source, then both independent expansion routes refuse.
        assert native_admit.returncode == 0
        assert reference.returncode > 0 and json.loads(reference.stdout) == ["refused", "algorithm-origin-limit"]
        assert compiled.returncode > 0 and names(compiled.stderr, "algorithm-origin-limit") and not compiled.stdout
        repeated_result = stage("repeat-native-refusal", [toolchain.compiler, "protocol-compile", source])
        assert repeated_result.returncode == compiled.returncode and repeated_result.stderr == compiled.stderr
        measurement.update(status="bounded-refusal", code="algorithm-origin-limit", boundary="128 UTF-8 occurrence bytes")
        write(directory / "capacity.json", measurement)
        return
    assert native_admit.returncode == reference.returncode == compiled.returncode == 0
    physical = write(directory / "physical.json", json.loads(compiled.stdout))
    assert journal.json([checker, "--check", source, physical])[0] == "checked"
    def variants(value):
        if isinstance(value, list):
            for child in value:
                yield from variants(child)
        elif isinstance(value, str) and value.startswith("variant:"):
            yield value
    types = list(variants(json.loads(materialized.stdout)))
    assert types
    # Each standalone descriptor has exact captured full-width relation bytes.
    relation = json.dumps(json.loads((directory / "relation0.json").read_text()), separators=(",", ":"))
    assert any(relation in json.loads(bytes.fromhex(t[8:]))[1] for t in types)
    inputs = write(directory / "inputs.json", ["zkc.run/2", "main", "capacity", [],
        [["P", [], [["ok", ["wire", "5a4b4356010501"]]], []]], []])
    actual = stage("native-execution", [toolchain.runtime, "run-protocol", source, physical, inputs, checker])
    assert actual.returncode == 0, actual.stderr
    native = json.loads(actual.stdout)
    assert native["outcome"] == ["returned", {"P": [["bool", True]]}]
    reference_inputs = write(directory / "reference-inputs.json", ["zkc.reference-inputs/1", "main", "capacity",
        [["P", [["ok", ["bool", "true"]]]]], [], [], []])
    expected = stage("lean-execution", [checker, "--reference", source, reference_inputs])
    assert expected.returncode == 0
    logical = json.loads(expected.stdout)
    assert logical[3] == ["returned", [["bool", "true"]]]
    assert logical[5] == native["resources"] == []
    measurement.update(status="executed", physical_bytes=physical.stat().st_size, usage=native["usage"],
        descriptor_occurrences=len(types), distinct_descriptor_spellings=len(set(types)),
        descriptor_bytes=sum(len(t.encode()) for t in types))
    write(directory / "capacity.json", measurement)


def test_bounded_project_library_refusal_is_deterministic(toolchain, directory):
    journal = Journal(directory)
    app = directory / "main.pir"
    app.write_text("module { fn Main(x: bool) -> bool { return x; } }")
    # 64 supplied roots plus the application exceeds ProjectInput::maxLibraries.
    command = [toolchain.compiler, "protocol-source", app, *[f"--library={directory / f"root{i}.pir"}" for i in range(64)]]
    results = [journal.attempt(command) for _ in range(2)]
    for result in results:
        assert result.returncode > 0 and not result.stdout
        assert names(result.stderr, "project-library-limit")
    assert results[0].stderr == results[1].stderr
    write(directory / "boundary.json", {"supplied_roots": 64, "application_roots": 1,
        "status": "refused", "code": "project-library-limit", "repeat_equal": True})


def test_named_and_positional_client_calls_preserve_ordered_values(toolchain, directory):
    journal = Journal(directory)
    app, library = copied_project(directory, "views")
    placed, count = re.subn(r"local \[walk\] P: let answer = (\w+)\(ready, ok\);",
        r"let [walk] answer = local P { return \1(ready, ok); };", app.read_text())
    assert count, count
    app.write_text(placed)
    original, physical = lower(toolchain, journal, app, [library], "positional-")
    edited(app, ('(ready, ok);', '(ok: ok, ready: ready);'))
    named, named_physical = lower(toolchain, journal, app, [library], "named-")
    # A call-label edit is not an identity edit. Preserve every origin, leaf order
    # and effect site, rather than compare only the final accepted bit.
    assert json.loads(original.read_text()) == json.loads(named.read_text())
    assert json.loads(physical.read_text()) == json.loads(named_physical.read_text())
    edited(app, ("let [walk] answer =", "let [walk] answer: bool ="))
    annotated, annotated_physical = lower(toolchain, journal, app, [library], "annotated-")
    assert json.loads(named.read_text()) == json.loads(annotated.read_text())
    for ready in (False, True):
        left = bool_execution(toolchain, journal, original, physical, "emptymany", ready, True, f"positional-{ready}")
        right = bool_execution(toolchain, journal, named, named_physical, "emptymany", ready, True, f"named-{ready}")
        assert left[0]["outcome"] == right[0]["outcome"]
        assert left[0]["resources"] == right[0]["resources"]
        assert left[1] == right[1]  # complete Lean event/resource/stop observation
        explicit = bool_execution(toolchain, journal, annotated, annotated_physical, "emptymany", ready, True, f"annotated-{ready}")
        assert explicit[0]["outcome"] == left[0]["outcome"]
        assert explicit[1] == left[1]


def test_imported_draw_selector_is_owner_qualified_and_ambiguity_refuses(toolchain, directory):
    journal = Journal(directory)
    app, library = copied_project(directory, "group")
    second = directory / "other.pir"
    second.write_text(replaced(library.read_text(), ('name="group"', 'name="group-other"')))
    edited(app, ('  use group::', '''
      dependency other = library(namespace="zkc.examples", name="group-other", version="1", resolution="source-v1");
      use group::'''))
    descriptor = directory / "construction.pir"
    descriptor.write_text((PROJECTS / "group/main.construction.pir").read_text())
    roots = options([library, second])
    selected = journal.json([toolchain.compiler, "protocol-construct", app, descriptor, *roots])
    assert selected[0] == "zkc.construction-result/1"
    edited(descriptor, ('group::BlsGroup.draw', 'BlsGroup.draw'))
    journal.run([toolchain.compiler, "protocol-construct", app, descriptor, *roots],
                refuses="construction-source-selector-ambiguous")


def test_imported_relation_capture_and_constructor_authority(toolchain, directory):
    journal = Journal(directory)
    app, library = copied_project(directory, "groth16")
    snapshot = write(directory / "snapshot.json", journal.json([
        toolchain.compiler, "protocol-resolve", app, *options([library])]))
    before = journal.json([toolchain.compiler, "protocol-materialize", snapshot])
    asset = library.parent / "circuit.json"
    relation = json.loads(asset.read_text())
    relation[5][0][0][0][1] = "2"
    write(asset, relation)
    changed = write(directory / "changed.json", journal.json([
        toolchain.compiler, "protocol-resolve", app, *options([library])]))
    after = journal.json([toolchain.compiler, "protocol-materialize", changed])
    assert before != after
    asset.unlink()
    assert journal.json([toolchain.compiler, "protocol-materialize", snapshot]) == before
    # A client spelling its function like the owner's permitted constructor
    # cannot mint a prepared assignment. Authority follows exact declarations.
    write(asset, relation)
    source = replaced(app.read_text(), ('use helpers::{', 'use helpers::{BoundAssignment,'))
    source = source[:-2] + '''
      fn BindAssignment(assignment: Vector<bn254.fr::Element>, statement: Vector<bn254.fr::Element>)
          -> BoundAssignment<bn254.fr> {
        return BoundAssignment { assignment, statement, private_assignment: assignment };
      }
    }'''
    app.write_text(source)
    journal.run([toolchain.compiler, "protocol-resolve", app, *options([library])],
                refuses="source-checked-construction")


def test_group_implementation_mutation_changes_actual_execution(toolchain, directory):
    journal = Journal(directory)
    app, library = copied_project(directory, "group")
    checker = toolchain.checker("interactive-protocol")
    results = []
    for mutated in (False, True):
        if mutated:
            edited(library, ('return same;', 'return false;'))
        source, physical = lower(toolchain, journal, app, [library], f"{mutated}-")
        inputs = write(directory / f"{mutated}-inputs.json", ["zkc.run/2", "main", "group-mutation", [],
            [["P", [], [], []], ["V", [["rng", "coins", "1", "entry"]],
             [["coins", ["host", "coins"]]], []]], []])
        report = journal.json([toolchain.runtime, "run-protocol", source, physical, inputs, checker])
        assert report["outcome"] == ["returned", {"P": [], "V": [["bool", not mutated]]}]
        results.append(report["outcome"])
    assert results[0] != results[1]


def test_air_config_specific_and_generic_all_selectors_match(toolchain, directory):
    journal = Journal(directory)
    authored = PROJECTS / "air/main.pir"
    libraries = [LIBRARIES / "air/lib.pir"]
    descriptor = PROJECTS / "air/main.construction.pir"
    selected = journal.json([toolchain.compiler, "protocol-construct", authored, descriptor, *options(libraries)])
    generic_descriptor = directory / "generic-all.construction.pir"
    generic_descriptor.write_text(replaced(descriptor.read_text(),
                                           ("helpers::Draw draw", "helpers::DrawAlgorithm draw"),
                                           ("helpers::Query draw", "helpers::QueryAlgorithm draw")))
    generic = journal.json([toolchain.compiler, "protocol-construct", authored, generic_descriptor, *options(libraries)])
    # This corpus has one concrete configuration per generic. Both source-level
    # selectors must choose the same work without referring to emitted hashes.
    assert generic[2] == selected[2]
    write(directory / "selected.json", selected)
    write(directory / "generic-all.json", generic)


def logical_tree(data, at=0):
    """One node of the logical tree encoding, and where the next one starts."""
    tag, size = data[at], int.from_bytes(data[at + 1:at + 9], "little")
    at += 9
    if tag == 0:
        return data[at:at + size].decode(), at + size
    items = []
    for _ in range(size):
        item, at = logical_tree(data, at)
        items.append(item)
    return items, at


@pytest.mark.parametrize("selection", ["definitions", "overlapping"])
@pytest.mark.parametrize("identity", ["exact", "normalized"])
def test_air_definition_selectors_reach_configurations_without_a_project(toolchain, directory, identity,
                                                                          selection):
    # With no project to bind them, the descriptor names generic definitions of
    # the carrier. The compiler, the runtime and the Lean reference each derive
    # that such a selector selects the configured functions instantiating it,
    # and that selectors reaching the same function select it once: the
    # reference replays the original source to the runtime's events.
    journal = Journal(directory)
    carrier = write(directory / "air.json", journal.json([toolchain.compiler, "protocol-source",
                                                          PROJECTS / "air/main.pir",
                                                          *options([LIBRARIES / "air/lib.pir"])]))
    configured = next(f[1] for f in journal.json([toolchain.compiler, "protocol-prepare", carrier])[2]
                      if f[5][0] == "DrawAlgorithm")
    descriptor = journal.json([toolchain.compiler, "protocol-source", PROJECTS / "air/main.construction.pir"])
    descriptor[5][1] = [["DrawAlgorithm", "draw"], ["QueryAlgorithm", "draw"]]
    if selection == "overlapping":
        descriptor[5][1].insert(0, [configured, "draw"])
    descriptor[8] = identity
    path = write(directory / "selectors.json", descriptor)
    folder = directory / "carrier"
    journal, shared, _, _, validate = artifact_case(toolchain, folder, PROJECTS / "air/main.pir",
        [LIBRARIES / "air/lib.pir"], path, "air", bind=False)
    source = shared[0]
    assert json.loads(shared[1].read_text()) == descriptor
    origins = {f[1]: f[5][0] for f in journal.json([toolchain.compiler, "protocol-prepare", source])[2]}
    drawn = {origins[logical_tree(bytes.fromhex(event[1]))[0][4][3]]
             for event in validate["events"] if event[0] == "challenge"}
    assert drawn == {"DrawAlgorithm", "QueryAlgorithm"}, drawn
    reference = toolchain.checker("artifact-reference")
    if identity == "normalized":
        rust = journal.json([toolchain.runtime, "inspect-artifact-identity", source, path])
        lean = journal.json([reference, "identity", source, path])
        assert lean[2] == rust["resolved_descriptor"]
        assert lean[2][5][1] == [[name, "site0"] for name, _ in descriptor[5][1]]

    def replay(refused):
        result = journal.attempt([reference, "reference", source, refused, folder / "validator.json",
                                  folder / "proof.bin", folder / "reference/replies.json"])
        assert result.returncode == 1, result.stdout
        return json.loads(result.stdout)

    # Naming one selector twice is malformed.
    repeated = copy.deepcopy(descriptor)
    repeated[5][1].append(copy.deepcopy(repeated[5][1][0]))
    twice = write(directory / "repeated.json", repeated)
    journal.run([toolchain.compiler, "protocol-construct", source, twice], refuses="construction-draw-selector")
    assert replay(twice) == ["refused", "construction-draws"]
    # A site the definition does not have selects nothing anywhere.
    descriptor[5][1][0][1] = "absent"
    absent = write(directory / "absent.json", descriptor)
    journal.run([toolchain.compiler, "protocol-construct", source, absent],
                refuses="source-site-selection" if identity == "normalized" else "construction-draw-selector")
    assert replay(absent) == ["refused", "construction-draw-site"]
    if identity == "normalized":
        refused = journal.attempt([toolchain.runtime, "inspect-artifact-identity", source, absent])
        assert refused.returncode == 1 and json.loads(refused.stdout)["code"] == "identity-draw-site"
