"""Ordinary usage warnings and checker-owned obligation explanations."""

import json

from cases import case
from commands import Commands
from tools import compiler, records

record_dir = records()
commands = Commands(record_dir)


def analyze(text):
    return json.loads(commands.source("protocol-analyze", text))


def warnings(report):
    assert report["unused_binding_warnings"] == "checked_retained_bodies", report
    result = report["warnings"]
    assert all(w["category"] == "warning" for w in result), result
    assert all(w["code"] == "source-unused-binding" for w in result), result
    return result


def identity(name):
    return f'library(namespace="explanations", name="{name}", version="1", resolution="r1")'


with case("unused lexical alias warns even when its underlying value is used"):
    text = '''module {
      fn Main(x: bool) -> bool { let unused = x; return x; }
    }'''
    report = analyze(text)
    result = warnings(report)
    assert report["state"] == "source_checked", report
    assert report["diagnostics"] == [], report
    assert len(result) == 1, result
    assert result[0]["primary"]["offset"] == text.index("let unused"), result
    assert any(c["kind"] == "declaration" for c in result[0]["causes"]), result
    commands.source("protocol-source", text)

with case("explicit discard names opt out"):
    report = analyze('''module {
      fn Main(x: bool) -> bool { let _ = x; let _ignored = x; return x; }
    }''')
    assert report["state"] == "source_checked", report
    assert warnings(report) == [], report

with case("Verify name has only ordinary usage semantics"):
    report = analyze('''module {
      fn Verify(x: bool) -> bool { return x; }
      fn Main(x: bool) -> bool { let checked = Verify(x); return x; }
    }''')
    assert len(warnings(report)) == 1, report
    assert report["decision_result_usage"] == "unavailable_no_decision_metadata"
    assert report["acceptance_dependence"] == "not_analyzed"
    assert report["cryptographic_soundness"] == "not_claimed"

with case("ordinary use does not claim acceptance dependence"):
    report = analyze('''module {
      fn Verify(x: bool) -> bool { return x; }
      fn Ignore(x: bool) -> bool { return true; }
      fn Main(x: bool) -> bool {
        let checked = Verify(x); return Ignore(checked);
      }
    }''')
    assert report["state"] == "source_checked", report
    assert warnings(report) == [], report
    assert report["acceptance_dependence"] == "not_analyzed"
    assert report["cryptographic_soundness"] == "not_claimed"

AGGREGATE = '''module {
  struct Pair(a: bool, b: bool);
  fn Main(x: bool) -> bool { let pair = Pair(a=x, b=x); return RESULT; }
}'''
with case("aggregate projection counts as use without unused sibling warnings"):
    report = analyze(AGGREGATE.replace("RESULT", "pair.a"))
    assert report["state"] == "source_checked", report
    assert warnings(report) == [], report

with case("unused aggregate produces one source binding warning"):
    report = analyze(AGGREGATE.replace("RESULT", "x"))
    result = warnings(report)
    assert len(result) == 1, result
    assert "'pair'" in result[0]["message"], result

with case("captured aliases in exclusive arms are not new unused bindings"):
    report = analyze('''module {
      fn Main(flag: bool, x: bool) -> bool {
        if flag capture(x) -> (answer) { yield x; }
        else { let yes = true; yield yes; }
        return answer;
      }
    }''')
    assert report["state"] == "source_checked", report
    assert warnings(report) == [], report

with case("warnings survive missing imports only for retained checked bodies"):
    text = f'''module {{
      dependency missing = {identity("missing")}; use missing::Absent;
      fn Independent(x: bool) -> bool {{ let unused = x; return x; }}
      fn Dependent(x: bool) -> bool {{ let unchecked = x; return Absent(x); }}
    }}'''
    report = analyze(text)
    assert report["state"] == "incomplete", report
    result = warnings(report)
    assert len(result) == 1, result
    assert result[0]["primary"]["offset"] == text.index("let unused"), result
    assert any(d["code"] == "source-dependency-missing" for d in report["diagnostics"])
    commands.source("protocol-source", text, refuses="source-dependency-missing")

with case("a failed body does not yield speculative unused warnings"):
    report = analyze('''module {
      fn Broken(x: bool) -> index { let unused = x; return x; }
    }''')
    assert report["state"] == "incomplete", report
    assert report["diagnostics"], report
    assert warnings(report) == [], report

with case("warnings retain their declaring source file"):
    root = record_dir / "child"
    root.mkdir()
    app = root / "app.pir"
    child = root / "child.pir"
    app.write_text("module {mod child;}")
    child.write_text("module {fn Main(x: bool) -> bool {let unused = x; return x;}}")
    report = json.loads(commands.run([compiler, "protocol-analyze", app]))
    result = warnings(report)
    assert len(result) == 1, result
    assert result[0]["primary"]["file"] == 1, result
    assert report["files"][1]["filename"] == str(child), report

OBLIGATION = '''module {
  interface FieldAPI { domain F: field = "koala-bear";
    local step(x: field<F>) -> field<F>;
  }
  component Impl: FieldAPI { domain F: field = "bls12-381.fr";
    local step(x: field<F>) -> field<F> { return x; }
  }
  fn Client<C: FieldAPI>(x: field<C::F>) -> field<C::F> { return C::step(x); }
  link Closed = Client<Impl>;
}'''

with case("failed core proof retains exact static obligation and finite checker"):
    report = analyze(OBLIGATION)
    diagnostic = next(d for d in report["diagnostics"] if d["code"] == "library-bound")
    obligations = [c for c in diagnostic["causes"] if c["kind"] == "unsatisfied_obligation"]
    assert len(obligations) == 1, diagnostic
    subject = json.loads(obligations[0]["subject"])
    assert subject["relation"] == "", subject
    assert len(subject["arguments"]) == 2, subject
    assert subject["arguments"][0] != subject["arguments"][1], subject
    assert any("koala-bear" in a for a in subject["arguments"]), subject
    assert any("bls12-381.fr" in a for a in subject["arguments"]), subject
    assert any(c["kind"] == "checker" and c["subject"] == "zkc::requirements::derive"
               for c in diagnostic["causes"]), diagnostic
    assert any(c["kind"] == "declaration" for c in diagnostic["causes"]), diagnostic
    for kind, name in (("selected_component", "Impl"), ("imported_interface", "FieldAPI")):
        owner = next(d for d in report["resolved_declarations"] if d["display_name"] == name)
        assert any(c["kind"] == kind and c["subject"] == owner["identity_key"]
                   for c in diagnostic["causes"]), diagnostic
    commands.source("protocol-source", OBLIGATION, refuses="library-bound")
    assert "required predicate not derivable: equality" in commands.last.stderr

with case("obligation context points to the exact imported interface file"):
    root = record_dir / "obligation"
    root.mkdir()
    library = root / "library.pir"
    app = root / "app.pir"
    interface = OBLIGATION[OBLIGATION.index("  interface"):OBLIGATION.index("  component")]
    library.write_text(f'module {{ {identity("fields")}; {interface.replace("interface", "pub interface", 1)} }}')
    app.write_text(f'''module {{
      dependency fields = {identity("fields")}; use fields::FieldAPI;
      {OBLIGATION[OBLIGATION.index("  component"):]}
    ''')
    report = json.loads(commands.run([compiler, "protocol-analyze", app, f"--library={library}"]))
    diagnostic = next(d for d in report["diagnostics"] if d["code"] == "library-bound")
    interface = next(d for d in report["resolved_declarations"] if d["display_name"] == "FieldAPI")
    assert diagnostic["primary"]["file"] == 0, diagnostic
    assert any(c["kind"] == "imported_interface" and c["span"]["file"] == 1
               and c["subject"] == interface["identity_key"]
               for c in diagnostic["causes"]), diagnostic
    assert any(c["kind"] == "unsatisfied_obligation" for c in diagnostic["causes"]), diagnostic

with case("ordinary type failures do not invent an unsatisfied obligation"):
    report = analyze("module {fn Broken(x: bool) -> index {return x;}}")
    assert report["diagnostics"], report
    assert all(c["kind"] != "unsatisfied_obligation"
               for d in report["diagnostics"] for c in d["causes"]), report

print(f"frontend explanations: {commands.save()} commands checked")
