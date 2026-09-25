"""Project queries retain exact provenance and honest partial phase results."""

import json

from cases import case
from commands import Commands
from tools import compiler, records

record_dir = records()
commands = Commands(record_dir)


def analyze(text):
    return json.loads(commands.source("protocol-analyze", text))


def identity(name):
    return f'library(namespace="queries", name="{name}", version="1", resolution="r1")'


def declaration(report, name):
    return next(d for d in report["declarations"] if d["display_name"] == name)


def write(root, name, text):
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    return path


with case("missing imports retain independent checked types, bodies and uses"):
    text = f'''module {{
      dependency missing = {identity("missing")};
      use missing::Absent;
      fn Dependent(x: bool) -> bool {{ return Absent(x); }}
      fn Transitive(x: bool) -> bool {{ return Dependent(x); }}
      fn Identity(x: bool) -> bool {{ return x; }}
      fn Independent(x: bool) -> bool {{ return Identity(x); }}
    }}'''
    report = analyze(text)
    assert report["state"] == "incomplete", report
    assert "source-dependency-missing" in {d["code"] for d in report["diagnostics"]}
    independent = declaration(report, "Independent")
    assert independent["signature_checked"]
    assert independent["body_state"] == "source_checked"
    assert independent["inputs"][0]["display"] == "bool"
    assert any(u["owner"] == independent["id"] for u in report["uses"])
    for name in ("Dependent", "Transitive"):
        dependent = declaration(report, name)
        assert not dependent["signature_checked"]
        assert dependent["body_state"] != "source_checked"
    assert report["phases"]["resolution"] == "incomplete"
    assert report["phases"]["pir_admission"] == "not_requested"
    assert report["phases"]["runtime_readiness"] == "not_requested"
    commands.source("protocol-source", text, refuses="source-dependency-missing")

with case("resource exhaustion is distinct from an ordinary semantic error"):
    deep = "module {" + "".join(f"const N{i}:index=N{i+1};" for i in range(70)) + "const N70:index=1;}"
    report = analyze(deep)
    assert report["phase"] == "resource_limit", report
    assert any(d["code"] == "source-constant-depth" and d["category"] == "resource_limit"
               for d in report["diagnostics"])
    commands.source("protocol-source", deep, refuses="source-constant-depth")
    invalid = analyze("module {fn Wrong(x: bool) -> index {return x;}}")
    assert invalid["phase"] == "semantic_error", invalid
    assert all(d["category"] == "error" for d in invalid["diagnostics"])

with case("source checking never claims admission, execution or a security lint"):
    report = analyze("module {fn Verify(x: bool) -> bool {return x;}}")
    assert report["state"] == "source_checked", report
    assert report["phases"]["resolution"] == "complete"
    assert report["phases"]["pir_admission"] == "not_requested"
    assert report["phases"]["runtime_readiness"] == "not_requested"
    assert report["decision_result_usage"] == "unavailable_no_decision_metadata"
    assert report["unused_binding_warnings"] == "checked_retained_bodies"
    assert report["acceptance_dependence"] == "not_analyzed"
    assert report["cryptographic_soundness"] == "not_claimed"
    assert report["cache"] == "not_implemented"

with case("imported names and semantic edges survive physical relocation"):
    root = record_dir / "relocation"
    library = f'''module {{ {identity("bits")};
      pub fn Identity(value: bool) -> bool {{ return value; }}
    }}'''
    app = write(root, "app.pir", f'''module {{
      dependency bits = {identity("bits")}; use bits::Identity;
      fn Main(value: bool) -> bool {{ return Identity(value); }}
    }}''')
    lib = write(root, "lib.pir", library)
    before = json.loads(commands.run([compiler, "protocol-analyze", app, f"--library={lib}"]))
    origin = next(d for d in before["resolved_declarations"]
                  if d["identity"]["library"] == "bits")
    imported = declaration(before, "Identity")
    assert imported["name"] == origin["symbol"]
    assert imported["identity"] == origin["identity_key"]
    assert imported["span"]["file"] == 1
    body_edges = [d for d in before["dependencies"] if d["category"] == "body"]
    assert any(d["target"] == imported["identity"] for d in body_edges)
    relocated = write(root, "moved/lib.pir", library)
    after = json.loads(commands.run([compiler, "protocol-analyze", app, f"--library={relocated}"]))
    assert after["resolved_declarations"] == before["resolved_declarations"]
    assert after["dependencies"] == before["dependencies"]
    assert after["files"] != before["files"]

with case("a child diagnostic uses its own file and an exact declaration cause"):
    root = record_dir / "diagnostic"
    app = write(root, "app.pir", "module {mod child;}")
    child = write(root, "child.pir", "module {fn Wrong(x: bool) -> index {return x;}}")
    report = json.loads(commands.run([compiler, "protocol-analyze", app]))
    diagnostic = report["diagnostics"][0]
    assert diagnostic["primary"]["file"] == 1, diagnostic
    assert report["files"][1]["filename"] == str(child)
    assert any(c["kind"] == "declaration" and c["span"]["file"] == 1
               for c in diagnostic["causes"]), diagnostic
    error = commands.source("protocol-source", None, str(app), refuses=diagnostic["code"])
    assert error == ""  # Refusals have diagnostics only; never a partial carrier.

with case("generic common-source names are distinct from resolver symbols"):
    root = record_dir / "generic_names"
    lib = write(root, "lib.pir", f'''module {{ {identity("generic")};
      pub fn Identity<F: Field>(value: F::Element) -> F::Element {{ return value; }}
    }}''')
    app = write(root, "app.pir", f'''module {{
      dependency generic = {identity("generic")}; use generic::Identity;
    }}''')
    report = json.loads(commands.run([compiler, "protocol-analyze", app, f"--library={lib}"]))
    assert report["state"] == "source_checked", report
    generic = declaration(report, "Identity")
    resolved = next(d for d in report["resolved_declarations"] if d["display_name"] == "Identity")
    assert generic["name"] == resolved["symbol"]
    assert generic["lowered_name"] == resolved["origin"]
    assert generic["lowered_name"] != generic["name"]
    commands.run([compiler, "protocol-source", app, f"--library={lib}"])

with case("a failed imported call relates the callee in its owning file"):
    root = record_dir / "related"
    lib = write(root, "lib.pir", f'''module {{ {identity("numbers")};
      pub fn Identity(value: index) -> index {{ return value; }}
    }}''')
    app = write(root, "app.pir", f'''module {{
      dependency numbers = {identity("numbers")}; use numbers::Identity;
      fn Main(value: bool) -> bool {{ return Identity(value); }}
    }}''')
    report = json.loads(commands.run([compiler, "protocol-analyze", app, f"--library={lib}"]))
    assert report["phase"] == "semantic_error", report
    diagnostic = report["diagnostics"][0]
    assert diagnostic["primary"]["file"] == 0
    assert any(r["span"]["file"] == 1 for r in diagnostic["related"]), diagnostic
    target = declaration(report, "Identity")
    assert any(c["subject"] == target["identity"] for c in diagnostic["causes"])
    commands.run([compiler, "protocol-source", app, f"--library={lib}"], refuses=diagnostic["code"])


INTERFACE = '''interface Cell {type Value drop; local step(value: Value) -> Value;}'''
COMPONENT = '''component Bit: Cell {
  type Value = bool; local step(value: Value) -> Value { return value; }
}'''
HELPERS = '''fn Helper<C: Cell>(value: C::Value) -> C::Value { return C::step(value); }
fn Client<C: Cell>(value: C::Value) -> C::Value { return Helper::<C>(value); }'''
LIBRARY = f'''module {{ {identity("calls")}; {INTERFACE} {COMPONENT} {HELPERS}
  link Closed = Client<Bit>;
}}'''

with case("a failed generic body retains formed interfaces without claiming a link"):
    invalid = LIBRARY.replace("return C::step(value);", "let next = C::step(value); return C::step(value);")
    report = analyze(invalid)
    assert report["phase"] == "semantic_error", report
    assert "library-resource-use" in {d["code"] for d in report["diagnostics"]}
    assert report["phases"]["formed_interface"]["count"] == 1
    assert report["phases"]["linked_selection"]["count"] == 0
    assert report["checked_libraries"]["query_state"] == "retained_partial_checked_capabilities"
    assert report["checked_libraries"]["unselected_component_conformance"] == "only_reported_components_checked"
    commands.source("protocol-source", invalid, refuses="library-resource-use")

with case("library queries expose labels, substitutions and exact link dependencies"):
    report = analyze(LIBRARY)
    assert report["state"] == "source_checked", report
    libraries = report["checked_libraries"]
    interface = libraries["interfaces"][0]
    assert interface["functions"][0]["signature"]["input_labels"] == ["value"]
    client = next(c for c in libraries["clients"] if c["display_name"] == "Client")
    call = next(i for i in client["body"]["instructions"]
                if i["kind"] == "call" and "function" in i["target"])
    assert call["target"]["function"]["name"] == "Helper"
    assert call["target"]["signature"]["input_labels"] == ["value"]
    assert call["target"]["substitutions"]["statics"]
    linked = libraries["links"][0]
    assert linked["identity"]
    assert linked["dependencies"]
    for dependency in linked["dependencies"]:
        assert dependency["interface_identity"]
        assert dependency["implementation_identity"]
        assert dependency["normalized_selection"]
        assert "capture_identity" in dependency and "dependencies" in dependency
    assert all("logical_signature" in f and "exact_subject" in f for f in linked["functions"])
    assert report["phases"]["formed_interface"]["count"] == 1
    assert report["phases"]["checked_generic_body"]["count"] >= 2
    assert report["phases"]["linked_selection"]["count"] == 1
    assert {d["category"] for d in report["dependencies"]} >= {"interface", "link_layout"}

with case("body edits preserve formed interface and invalidate checked body and link keys"):
    before = analyze(LIBRARY)["checked_libraries"]
    changed = LIBRARY.replace("return C::step(value);", "let next = C::step(value); return C::step(next);")
    after = analyze(changed)["checked_libraries"]
    assert before["interfaces"][0]["identity"] == after["interfaces"][0]["identity"]
    old_helper = next(c for c in before["clients"] if c["display_name"] == "Helper")
    new_helper = next(c for c in after["clients"] if c["display_name"] == "Helper")
    assert old_helper["identity"] != new_helper["identity"]
    assert before["links"][0]["identity"] != after["links"][0]["identity"]

with case("project inspection retains elaborated calls in every captured owner"):
    root = record_dir / "project_inspection"
    lib = write(root, "lib.pir", f'''module {{ {identity("inspection")};
      fn Private(value: bool) -> bool {{ return value; }}
      pub fn Public(value: bool) -> bool {{ return Private(value); }}
    }}''')
    app = write(root, "app.pir", f'''module {{
      dependency bits = {identity("inspection")}; use bits::Public;
      fn Main(value: bool) -> bool {{ return Public(value); }}
    }}''')
    report = json.loads(commands.run([compiler, "protocol-inspect", app, f"--library={lib}"]))
    calls = report["elaborated_calls"]
    assert len(calls) == 2, calls
    assert {call["file"] for call in calls} == {0, 1}, calls
    assert all(call["kind"] == "algorithm" for call in calls)
    assert {item["location"]["file"] for item in report["occurrences"]} == {str(app), str(lib)}

print(f"frontend project queries: {commands.save()} commands checked")
