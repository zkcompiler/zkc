"""Assurance reports: `zkc.assurance-report/0`, one per subject manifest.

A report records a checked application of a registered endpoint to
artifact-indexed evidence. It is assembled from the subject manifest, the
declaration records (with the registry and the registered endpoints), and the
subject pipeline's evidence for the subject. The generator is fail-closed:
anything it cannot classify or connect makes the claim `unresolved`, with the
reason. `lean/docs/spec/assurance-report.md` specifies the format.
"""

import hashlib
import json
from pathlib import Path
import re
import tomllib

from .declarations import ALLOWED_AXIOMS, forbidden_axioms

LEAN = Path(__file__).resolve().parents[2]
ROOT = LEAN.parent
FORMAT = "zkc.assurance-report/0"
EVIDENCE_FORMAT = "zkc.subject-evidence/0"
ENDPOINTS = ("ideal-meaning", "executable-bytes")
STATEMENTS = ("fixed", "adaptive")

# Trusted links every claim about a covered endpoint rests on. A typed
# public-value binding discharges statement determination only, never the
# native absorption of the public values, which stays assumed until a theorem
# about native transcript bytes exists.
REQUIRED_LINKS = {
    "ideal-meaning": ["exporter.structured-denotation", "exporter.checked-candidate",
                      "transport.canonical-decoding", "transcript.encoding-injective",
                      "binding.native-absorption"],
    "executable-bytes": ["exporter.structured-denotation", "runtime.program-reader",
                         "runtime.acceptance-inclusion", "runtime.installed-kernels",
                         "runtime.codec-function", "transcript.encoding-injective",
                         "binding.native-absorption"],
}
DIGEST = re.compile(r'(\w+)\s*:?=\s*"sha256:([0-9a-f]{64})"')


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load_manifest(path):
    """A subject manifest, read tolerantly: fields this generator does not use
    are ignored, so the pipeline may add fields without breaking reports."""
    manifest = tomllib.loads(Path(path).read_text())
    if "name" not in manifest:
        raise ValueError(f"{path}: manifest has no name")
    return manifest


def load_evidence(directory, name):
    """The pipeline's evidence for one subject, or None when absent."""
    if directory is None:
        return None
    for candidate in (Path(directory) / f"{name}.json", Path(directory) / name / "evidence.json"):
        if candidate.exists():
            evidence = json.loads(candidate.read_text())
            evidence["_path"] = str(candidate)
            return evidence
    return None


class Registry:
    def __init__(self, entries, endpoints):
        self.entries = entries or []
        self.endpoints = endpoints or []
        self.by_identifier = {entry["identifier"]: entry for entry in self.entries}
        self.by_schema = {}
        for entry in self.entries:
            if entry.get("schema"):
                self.by_schema.setdefault(entry["schema"], entry)

    def classify(self, head):
        return self.by_schema.get(head) if head else None

    def endpoint(self, endpoint, prop, statement):
        for row in self.endpoints:
            if (row["endpoint"], row["property"], row["statement"]) == (endpoint, prop, statement):
                return row["theorem"]
        return None


def assumption(entry, source, statement=None, discharge="assumed"):
    return {"id": entry["identifier"], "category": entry["category"], "schema": entry.get("schema"),
            "statement": entry["statement"], "instantiated": statement, "discharge": discharge,
            "source": source}


def telescope(record, registry, origin):
    """Classify every premise of a detailed record's elaborated telescope,
    implicit and instance binders included. Returns the registered assumptions
    and the reasons for premises that are not registered."""
    detail = record.get("detail") or {}
    binders = detail.get("premise_telescope")
    texts = detail.get("premises", [])
    if binders is None:
        return [], [f"{origin} {record['name']} was not recorded in detail"]
    found, reasons = [], []
    for position, binder in enumerate(binders):
        if not binder.get("premise"):
            continue
        text = texts[position] if position < len(texts) else None
        entry = registry.classify(binder.get("head"))
        if entry is None:
            reasons.append(f"omitted premise: {binder['binder']} premise {text or binder.get('head')} of "
                           f"{origin} {record['name']} is not a registered assumption")
        else:
            found.append(assumption(entry, f"premise of {origin} {record['name']}", text))
    return found, reasons


def attached(manifest):
    """Digests the manifest's generated modules carry, with each file's digest."""
    rows = []
    for key, value in sorted((manifest.get("generated") or {}).items()):
        paths = value if isinstance(value, list) else [value]
        for relative in paths:
            path = ROOT / relative
            if not path.exists():
                rows.append({"role": key, "path": relative, "status": "missing"})
                continue
            records = {name: f"sha256:{digest}" for name, digest in DIGEST.findall(path.read_text())}
            rows.append({"role": key, "path": relative, "sha256": sha256(path), "records": records})
    return rows


def connection(manifest, manifest_path, modules, evidence):
    """Whether pipeline evidence connects the generated data to the artifacts the
    pipeline produced. A digest attached to generated data is not by itself
    evidence that the data came from those artifacts."""
    if evidence is None:
        return {"status": "unresolved", "reason": "no pipeline evidence for this subject"}, \
            ["no pipeline evidence connects the generated data to the source, export and program bytes"]
    reasons = []
    if evidence.get("subject") != manifest["name"]:
        reasons.append(f"mismatched artifact: the evidence is for {evidence.get('subject')!r}")
    if evidence.get("manifest_sha256") not in (None, sha256(manifest_path)):
        reasons.append("mismatched artifact: the evidence was produced from another manifest")
    produced = set((evidence.get("artifacts") or {}).values())
    generated = evidence.get("generated") or {}
    if not modules:
        reasons.append("the manifest declares no generated data")
    for module in modules:
        if module.get("status") == "missing":
            reasons.append(f"mismatched artifact: generated module {module['path']} is missing")
            continue
        recorded = (generated.get(module["path"]) or {}).get("sha256")
        if recorded is None:
            reasons.append(f"the evidence does not cover {module['path']}")
        elif recorded != module["sha256"]:
            reasons.append(f"mismatched artifact: {module['path']} differs from the module the "
                           "pipeline regenerated")
        for name, digest in module["records"].items():
            if digest not in produced:
                reasons.append(f"mismatched artifact: {module['path']} records {name} = {digest}, "
                               "which the pipeline did not produce")
    status = "connected" if not reasons else (
        "mismatched" if any(r.startswith("mismatched") for r in reasons) else "unresolved")
    return {"status": status, "evidence": evidence.get("_path"),
            "evidence_sha256": sha256(evidence["_path"]) if evidence.get("_path") else None,
            "artifacts": evidence.get("artifacts") or {}}, reasons


def validation(evidence):
    """The validation outcome the checks emitted, as emitted."""
    if evidence is None:
        return {"outcome": "unresolved", "checks": []}
    checks = evidence.get("checks") or []
    outcomes = [check.get("outcome") for check in checks]
    if not checks:
        outcome = "unresolved"
    elif "refused" in outcomes:
        outcome = "refused"
    elif "unsupported" in outcomes:
        outcome = "unsupported"
    elif all(value == "accepted" for value in outcomes):
        outcome = "accepted"
    else:
        outcome = "unresolved"
    return {"outcome": outcome, "checks": checks}


def checker(records):
    """Toolchain, dependency pins and declared compatibility patches."""
    pins, manifests, patches = {}, {}, []
    for relative in ("lake-manifest.json", "integrations/arklib/lake-manifest.json",
                     "integrations/clean/lake-manifest.json"):
        path = LEAN / relative
        if path.exists():
            manifests[f"lean/{relative}"] = sha256(path)
            for package in json.loads(path.read_text()).get("packages", []):
                if package.get("type") == "git":
                    pins[package["name"]] = package["rev"]
    for relative in ("integrations/arklib/compatibility.json", "integrations/clean/compatibility.json"):
        path = LEAN / relative
        if path.exists():
            declared = json.loads(path.read_text())
            patches.append({"package": declared["package"], "revision": declared["revision"],
                            "patch_sha256": declared["patch_sha256"], "record": f"lean/{relative}"})
    toolchains = sorted({header.get("toolchain") for header in records.headers.values()})
    return {"lean": toolchains, "lake_manifests": manifests, "pins": dict(sorted(pins.items())),
            "compatibility": patches, "packages": sorted(records.packages())}


def declaration(records, name, role):
    """A declaration's facts for the report, and the reasons it cannot be used."""
    if name is None:
        return None, []
    record = records.get(name)
    if record is None:
        return {"name": name, "status": "missing"}, [f"{role} {name} is not a declaration of "
                                                    f"{', '.join(sorted(records.packages()))}"]
    forbidden = forbidden_axioms(record)
    facts = {"name": name, "module": record["module"], "kind": record["kind"],
             "statement_hashes": record["statement"], "axioms": record["axioms"],
             "statement": (record.get("detail") or {}).get("statement")}
    reasons = [f"{role} {name} depends on {', '.join(forbidden)}"] if forbidden else []
    return facts, reasons


def claim(manifest, prop, records, registry, evidence_validation, connected_reasons):
    section = manifest.get("claims") or {}
    endpoint, statement = section.get("endpoint"), section.get("statement")
    family = manifest.get("family") or {}
    reasons = []
    if endpoint not in ENDPOINTS:
        reasons.append(f"unsupported endpoint claim: {endpoint!r} is not a covered compiled endpoint "
                       f"({', '.join(ENDPOINTS)})")
    if statement not in STATEMENTS:
        reasons.append(f"unsupported endpoint claim: statement form {statement!r}")
    theorem = registry.endpoint(endpoint, prop, statement)
    if theorem is None and not reasons:
        reasons.append(f"unsupported endpoint claim: no registered endpoint states {prop} for "
                       f"{endpoint} with a {statement} statement")
    endpoint_facts, endpoint_reasons = declaration(records, theorem, "registered endpoint")
    instance_facts, instance_reasons = declaration(records, family.get("instance"), "evidence instance")
    if family.get("instance") is None:
        instance_reasons = ["the manifest names no evidence instance"]
    reasons += endpoint_reasons + instance_reasons
    assumptions = []
    for name, origin in ((theorem, "endpoint"), (family.get("instance"), "evidence instance")):
        record = records.get(name) if name else None
        if record is not None:
            found, omitted = telescope(record, registry, origin)
            assumptions += found
            reasons += omitted
    carried = {row["id"] for row in assumptions}
    for identifier in REQUIRED_LINKS.get(endpoint, []):
        entry = registry.by_identifier.get(identifier)
        if entry is None:
            reasons.append(f"required trusted link {identifier} is not registered")
        elif identifier not in carried:
            assumptions.append(assumption(entry, f"required for the {endpoint} endpoint"))
    requested = list((manifest.get("assumptions") or {}).get("requested", []))
    for identifier in requested:
        if identifier not in registry.by_identifier:
            reasons.append(f"requested assumption {identifier} is not a registry identifier")
    models = []
    for name in (theorem, family.get("instance")):
        record = records.get(name) if name else None
        for schema in ((record or {}).get("detail") or {}).get("registered", []):
            entry = registry.classify(schema)
            if entry is not None and entry["category"] == "model" and \
                    entry["identifier"] not in [m["id"] for m in models]:
                models.append({"id": entry["identifier"], "definition": schema, "statement": entry["statement"]})
    reasons += connected_reasons
    outcome = evidence_validation["outcome"]
    if outcome in ("refused", "unsupported"):
        verdict = outcome
    elif outcome != "accepted":
        verdict = "unresolved"
        reasons.append("the pipeline recorded no accepted validation for this subject")
    else:
        verdict = "unresolved" if reasons else "established"
    regime = {"expected": section.get("regime"),
              "evidence": (instance_facts or {}).get("statement") if instance_facts else None}
    bound = {"theorem": theorem, "statement": (endpoint_facts or {}).get("statement")} \
        if endpoint_facts and endpoint_facts.get("status") != "missing" else {"status": "unresolved"}
    return {"property": prop, "covered_endpoint": endpoint, "statement": statement,
            "validation": evidence_validation["outcome"], "endpoint": endpoint_facts or {"status": "unresolved"},
            "evidence": instance_facts or {"status": "unresolved"}, "assumptions": assumptions,
            "requested_assumptions": requested, "models": models, "regime": regime, "bound": bound,
            "outcome": verdict, "reasons": reasons}


def context(manifest, ledger, records, registry):
    """Theorems the claims ledger cites for this subject. They are context, not
    the endpoint application, and never establish a claim."""
    rows = []
    for row in (ledger or {}).get("proved", []):
        if manifest["name"] not in row.get("subjects", []):
            continue
        for name in row["theorems"]:
            record = records.get(name)
            if record is None:
                rows.append({"name": name, "status": "not emitted"})
                continue
            premises = []
            for binder in record.get("premises", []):
                if binder.get("premise"):
                    entry = registry.classify(binder.get("head"))
                    premises.append({"binder": binder["binder"], "head": binder.get("head"),
                                     "registered": entry["identifier"] if entry else None})
            forbidden = forbidden_axioms(record)
            rows.append({"name": name, "module": record["module"], "statement_hashes": record["statement"],
                         "axioms": record["axioms"], "premises": premises,
                         "status": "unresolved" if forbidden else "clean"})
    return rows


def build(manifest_path, records, ledger=None, evidence_directory=None):
    manifest = load_manifest(manifest_path)
    entries, endpoints = records.registry()
    registry = Registry(entries, endpoints)
    evidence = load_evidence(evidence_directory, manifest["name"])
    modules = attached(manifest)
    connected, connected_reasons = connection(manifest, manifest_path, modules, evidence)
    checks = validation(evidence)
    reasons = []
    if entries is None:
        reasons.append("the registry was not emitted: the security package was not selected")
    properties = list((manifest.get("claims") or {}).get("properties", []))
    if not properties:
        reasons.append("the manifest claims no property")
    claims = [claim(manifest, prop, records, registry, checks, connected_reasons) for prop in properties]
    verdicts = [c["outcome"] for c in claims]
    if reasons or not claims or "unresolved" in verdicts:
        outcome = "unresolved"
    elif "refused" in verdicts:
        outcome = "refused"
    elif "unsupported" in verdicts:
        outcome = "unsupported"
    else:
        outcome = "established"
    try:
        relative = str(Path(manifest_path).resolve().relative_to(ROOT))
    except ValueError:
        relative = str(manifest_path)
    return {
        "format": FORMAT,
        "subject": manifest["name"],
        "outcome": outcome,
        "reasons": reasons,
        "manifest": {"path": relative, "sha256": sha256(manifest_path), "schema": manifest.get("schema"),
                     "entries": manifest.get("entries") or {}},
        "artifacts": {"attached": modules, "connected": connected},
        "checker": checker(records),
        "claims": claims,
        "context": context(manifest, ledger, records, registry),
        "allowed_axioms": list(ALLOWED_AXIOMS),
    }


def render_subjects(reports):
    """Subject rows for `lean/docs/support.md`."""
    lines = ["| Subject | Entry | Endpoint | Property | Statement | Assumptions | Report |",
             "|---|---|---|---|---|---|---|"]
    for report in reports:
        entry = report["manifest"]["entries"].get("proof", "")
        for item in report["claims"] or [{}]:
            identifiers = ", ".join(f"`{row['id']}`" for row in item.get("assumptions", []))
            reason = item.get("reasons", report["reasons"])
            verdict = item.get("outcome", report["outcome"])
            note = f"{verdict}: {reason[0]}" if reason and verdict != "established" else verdict
            lines.append(f"| {report['subject']} | `{entry}` | {item.get('covered_endpoint', '')} | "
                         f"{item.get('property', '')} | {item.get('statement', '')} | {identifiers} | {note} |")
    return "\n".join(lines) + "\n"
