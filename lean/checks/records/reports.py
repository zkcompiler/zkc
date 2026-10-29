"""Assurance reports: `zkc.assurance-report/0`, one per compiled subject.

Requested meanings come only from bound source claims. Typed receipt indices,
actual proofs and their dependencies are extracted by Lean. Legacy endpoint
helpers remain for mathematical ledger and negative-control auditing; they do
not select requested claims for the public report builder. `lean/docs/spec/assurance-report.md` specifies the format.
"""

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tomllib
import uuid

from .declarations import ALLOWED_AXIOMS, forbidden_axioms
from bridges.structured.source_views import modules as source_view_modules

LEAN = Path(__file__).resolve().parents[2]
ROOT = LEAN.parent
FORMAT = "zkc.assurance-report/0"
EVIDENCE_FORMAT = "zkc.subject-evidence/0"
ENDPOINTS = ("ideal-meaning", "executable-bytes")
STATEMENTS = ("fixed", "adaptive")

# Legacy endpoint audit metadata, retained for its ledger/control helpers. A typed
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
        self.by_identifier = {}
        self.by_schema = {}
        for entry in self.entries:
            identifier = entry["identifier"]
            if identifier in self.by_identifier:
                raise ValueError(f"conflicting registry identifier: {identifier}")
            self.by_identifier[identifier] = entry
        for entry in self.entries:
            if entry.get("schema"):
                schema = entry["schema"]
                if schema in self.by_schema and self.by_schema[schema] != entry:
                    raise ValueError(f"conflicting registry schema: {schema}")
                self.by_schema[schema] = entry

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
    generated = dict(manifest.get("generated") or {})
    for selection in (manifest.get("source_views") or {}).get("selections", []):
        for module in source_view_modules(selection):
            generated[f"source-views:{module}"] = "lean/" + module.replace(".", "/") + ".lean"
    for key, value in sorted(generated.items()):
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
    for relative in ("lake-manifest.json", "security/lake-manifest.json", "integrations/arklib/lake-manifest.json",
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


# The evidence structure of each property, and the regimes a manifest may name.
EVIDENCE = {"soundness": "ZkcSecurity.Endpoint.SoundnessEvidence",
            "knowledge-soundness": "ZkcSecurity.Endpoint.KnowledgeEvidence"}
REGIMES = {"exact-uniform challenges": "ZkcSecurity.Endpoint.Regime.exact"}
# The binders a claim's application or evidence may take besides registered
# premises: universes and types, instances of these classes, and the bound
# application context, a string.
INSTANCES = {"Field", "CommRing", "Fintype", "DecidableEq", "Inhabited", "Nonempty", "SampleableType",
             "AddCommGroup", "Module"}


# The short names of the registered endpoint theorems, by claim, and the
# contract declaration of each property: the names a claims namespace holds.
ENDPOINT_NAMES = {
    ("ideal-meaning", "soundness", "fixed"): "fixed_soundness",
    ("ideal-meaning", "soundness", "adaptive"): "adaptive_soundness",
    ("executable-bytes", "soundness", "fixed"): "fixed_soundness_bytes",
    ("executable-bytes", "soundness", "adaptive"): "adaptive_soundness_bytes",
    ("ideal-meaning", "knowledge-soundness", "fixed"): "knowledge_soundness",
    ("executable-bytes", "knowledge-soundness", "fixed"): "knowledge_soundness_bytes",
}
CONTRACTS = {"soundness": "falseStatement", "knowledge-soundness": "holds"}


# Manifest fields that once named a claim's declarations directly. The names
# now derive from the claims namespace alone; a field that names anything else
# would let a report join one subject's artifacts to another's application.
OVERRIDES = (("claims", "artifacts"), ("claims", "contract"), ("claims", "application"),
             ("family", "instance"))


def claim_names(manifest):
    """The declarations of a subject's claim, all derived from its claims
    namespace: the artifacts, the contract, the evidence and the application."""
    section = manifest.get("claims") or {}
    namespace = section.get("namespace")
    properties = section.get("properties") or []
    prop = properties[0] if len(properties) == 1 else None
    short = ENDPOINT_NAMES.get((section.get("endpoint"), prop, section.get("statement")))
    if namespace is None:
        return {"namespace": None, "artifacts": None, "contract": None, "instance": None, "application": None}
    return {"namespace": namespace,
            "artifacts": f"{namespace}.artifacts",
            "contract": f"{namespace}.Contract.{CONTRACTS.get(prop, 'falseStatement')}",
            "instance": f"{namespace}.evidence",
            "application": f"{namespace}.{short}" if short else None}


def module_suffix(namespace, leaf):
    """The path suffix of a claims namespace's generated module."""
    return "/".join(namespace.split(".")) + f"/{leaf}.lean"


def join_reasons(manifest, names, evidence, records):
    """Why the claim's declarations are not joined to this subject's validated
    artifacts: each name derives from the subject's claims namespace, the
    namespace's generated artifacts and claims modules are among the modules the
    pipeline regenerated for this subject, the application and its evidence are
    declared in that claims module, and the pipeline built that module as the
    claim's application."""
    reasons = []
    namespace = names["namespace"]
    if namespace is None:
        return ["the manifest names no claims namespace, so no generated application belongs to it"]
    for table, field in OVERRIDES:
        value = (manifest.get(table) or {}).get(field)
        derived = names["instance" if field == "instance" else field]
        if value is not None and value != derived:
            reasons.append(f"conflicting override: {table}.{field} names {value}, not the subject's {derived}")
    generated = manifest.get("generated") or {}
    for key, leaf in (("artifacts", "Artifacts"), ("claims", "Claims")):
        path = generated.get(key)
        if not isinstance(path, str) or not Path(path).as_posix().endswith(module_suffix(namespace, leaf)):
            reasons.append(f"mismatched artifact: the manifest's generated {key} module is not "
                           f"{module_suffix(namespace, leaf)} of the claims namespace")
    claims_module = f"{namespace}.Claims"
    for key in ("application", "instance"):
        name = names[key]
        record = records.get(name) if name else None
        if record is not None and record.get("module") != claims_module:
            reasons.append(f"mismatched artifact: {key} {name} is declared in {record.get('module')}, not in the "
                           f"subject's generated claims module {claims_module}")
    built = [check for check in ((evidence or {}).get("checks") or [])
             if check.get("name") == "claim-application" and check.get("outcome") == "accepted"]
    if not any(check.get("module") == claims_module and check.get("application") == names["application"]
               for check in built):
        reasons.append(f"the pipeline recorded no accepted claim-application check that built {claims_module} "
                       f"with the application {names['application']}")
    return reasons


def heads(arguments):
    return {argument.get("head") for argument in arguments or [] if argument.get("head")}


def binder_reasons(record, origin):
    """Every binder must be a type, an allowed instance, the application context
    or a premise; a premise is classified separately. Any other binder is a
    parameter the claim does not account for, such as a structure of
    assumptions."""
    reasons = []
    for position, binder in enumerate(((record.get("detail") or {}).get("binders")) or []):
        if binder.get("premise"):
            continue
        head = binder.get("type_head")
        if head == "sort" or (binder.get("binder") == "instance" and head in INSTANCES
                               and binder.get("model_instance") is True) or \
                (binder.get("binder") == "explicit" and head == "String"):
            continue
        reasons.append(f"hidden parameter: binder {position} of {origin} {record['name']} has type {head}, "
                       "which is neither a type, an allowed instance, the application context nor a registered "
                       "premise")
    return reasons


def premises_of(telescope_binders, texts, registry, origin):
    found, reasons = [], []
    for position, binder in enumerate(telescope_binders):
        if not binder.get("premise"):
            continue
        text = texts[position] if position < len(texts) else None
        entry = registry.classify(binder.get("head"))
        if entry is None:
            reasons.append(f"omitted premise: {binder['binder']} premise {text or binder.get('head')} of "
                           f"{origin} is not a registered assumption")
        else:
            found.append(assumption(entry, f"premise of {origin}", text))
    return found, reasons


def hypotheses(record, registry):
    """The evidence's named hypotheses, each a checked instance of the schema of
    the registry entry it cites, reconciled with the evidence's premises."""
    detail = record.get("detail") or {}
    found, discharged, reasons = [], [], []
    listed = detail.get("hypotheses")
    if not isinstance(listed, list):
        return found, discharged, [f"the named hypotheses of {record['name']} were not recorded"]
    named_premises = set()
    for item in listed:
        identifier = item.get("identifier")
        entry = registry.by_identifier.get(identifier)
        if entry is None:
            reasons.append(f"hypothesis {identifier} of {record['name']} is not a registry identifier")
            continue
        schema = entry.get("schema")
        if schema is None or schema not in (item.get("claim_head"), item.get("claim_head_reducible")):
            reasons.append(f"wrong schema: hypothesis {identifier} of {record['name']} states "
                           f"{item.get('claim_head')}, which is not an instance of its schema {schema}")
            continue
        status = item.get("status") or {}
        kind = status.get("kind")
        arguments = [argument.get("text") for argument in item.get("claim_arguments") or []]
        row = assumption(entry, f"named hypothesis of {record['name']}", item.get("claim"),
                         discharge="proved" if kind == "proof" else "assumed")
        row["arguments"] = arguments
        if kind == "proof":
            discharged.append(row)
        elif kind == "premise":
            named_premises.add(schema)
            found.append(row)
        elif kind == "assumed" and status.get("cites") == identifier:
            found.append(row)
        else:
            reasons.append(f"hypothesis {identifier} of {record['name']} has an unrecognized status")
    for binder in detail.get("premise_telescope") or []:
        if binder.get("premise") and binder.get("head") not in named_premises:
            reasons.append(f"omitted assumption: premise {binder.get('head')} of {record['name']} is not a "
                           "named hypothesis")
    return found, discharged, reasons


def application_check(section, prop, family, theorem, records, registry):
    """The claim's application declaration: the registered endpoint applied to the
    manifest's evidence, stated at the subject's artifacts, contract and regime.
    Returns the facts, the assumptions its own premises and its property's
    premises carry, and the reasons it cannot establish the claim."""
    names = claim_names({"claims": section, "family": family})
    name = names["application"]
    if name is None:
        return None, [], ["the manifest names no application declaration"]
    facts, reasons = declaration(records, name, "application")
    record = records.get(name)
    if record is None:
        return facts, [], reasons
    detail = record.get("detail") or {}
    if not detail:
        return facts, [], reasons + [f"application {name} was not recorded in detail"]
    endpoint_record = records.get(theorem) if theorem else None
    expected = ((endpoint_record or {}).get("detail") or {}).get("type_head")
    if expected is None or detail.get("type_head") != expected:
        reasons.append(f"application {name} states {detail.get('type_head')}, not the registered property "
                       f"{expected}")
    if detail.get("value_head") != theorem:
        reasons.append(f"application {name} is not the registered endpoint {theorem} applied to evidence")
    instance = names["instance"]
    stated = heads(detail.get("type_arguments"))
    if instance is None or instance not in stated or instance not in heads(detail.get("value_arguments")):
        reasons.append(f"wrong evidence: application {name} does not apply the endpoint to the manifest's "
                       f"evidence {instance}")
    artifacts = names["artifacts"]
    if artifacts is None or artifacts not in stated:
        reasons.append(f"mismatched artifact: application {name} is not stated at the subject's artifacts "
                       f"{artifacts}")
    contract = names["contract"]
    if contract is None or contract not in stated:
        reasons.append(f"substituted relation: application {name} is not stated at the subject's contract "
                       f"{contract}")
    if prop == "soundness":
        regime = REGIMES.get(section.get("regime"))
        if regime is None or regime not in stated:
            reasons.append(f"application {name} is not stated at the manifest's regime {section.get('regime')!r}")
    reasons += binder_reasons(record, "application")
    # The application's own premises: a generated application has none, so any
    # premise it states is an assumption the report must classify.
    outer, outer_reasons = telescope(record, registry, "application")
    reasons += outer_reasons
    property_detail = detail.get("property") or {}
    found, omitted = premises_of(property_detail.get("premise_telescope") or [], [], registry,
                                 f"the property of {name}")
    found = outer + found
    reasons += omitted
    if facts is not None:
        facts["bound"] = property_detail.get("statement")
    return facts, found, reasons


def evidence_check(section, prop, family, records, registry):
    """The manifest's evidence instance: the property's evidence structure at the
    subject's artifacts and contract, with no unaccounted parameter and checked
    named hypotheses."""
    names = claim_names({"claims": section, "family": family})
    instance = names["instance"]
    if instance is None:
        return None, [], [], ["the manifest names no evidence instance"]
    facts, reasons = declaration(records, instance, "evidence instance")
    record = records.get(instance)
    if record is None:
        return facts, [], [], reasons
    detail = record.get("detail") or {}
    if not detail:
        return facts, [], [], reasons + [f"evidence instance {instance} was not recorded in detail"]
    if detail.get("type_head") != EVIDENCE.get(prop):
        reasons.append(f"evidence instance {instance} is a {detail.get('type_head')}, not {EVIDENCE.get(prop)}")
    stated = heads(detail.get("type_arguments"))
    for key, label in (("artifacts", "mismatched artifact"), ("contract", "substituted relation")):
        if names[key] not in stated:
            reasons.append(f"{label}: evidence instance {instance} is not indexed by {names[key]}")
    reasons += binder_reasons(record, "evidence instance")
    found, telescope_reasons = telescope(record, registry, "evidence instance")
    reasons += telescope_reasons
    named, discharged, hypothesis_reasons = hypotheses(record, registry)
    reasons += hypothesis_reasons
    return facts, found + named, discharged, reasons


def claim(manifest, prop, records, registry, evidence_validation, connected_reasons, evidence=None,
          reused_records=None):
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
    reasons += endpoint_reasons
    application_facts, application_assumptions, application_reasons = application_check(
        section, prop, family, theorem, records, registry) if theorem else (None, [], [])
    reasons += application_reasons
    instance_facts, instance_assumptions, discharged, instance_reasons = evidence_check(
        section, prop, family, records, registry)
    reasons += instance_reasons
    assumptions = application_assumptions + instance_assumptions
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
    names = claim_names(manifest)
    reasons += join_reasons(manifest, names, evidence, records)
    if reused_records is not None:
        reasons.append(reused_reason(reused_records))
    models = []
    for name in (theorem, names["application"], names["instance"]):
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
    bound = {"theorem": names["application"], "statement": (application_facts or {}).get("statement"),
             "property": (application_facts or {}).get("bound")} \
        if application_facts and application_facts.get("status") != "missing" else {"status": "unresolved"}
    return {"property": prop, "covered_endpoint": endpoint, "statement": statement,
            "validation": evidence_validation["outcome"], "endpoint": endpoint_facts or {"status": "unresolved"},
            "application": application_facts or {"status": "unresolved"},
            "evidence": instance_facts or {"status": "unresolved"}, "assumptions": assumptions,
            "discharged": discharged, "requested_assumptions": requested, "models": models, "regime": regime,
            "contract": names["contract"], "artifacts_declaration": names["artifacts"],
            "bound": bound, "outcome": verdict, "reasons": reasons}


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


def reused_reason(directory):
    """Records carry declaration hashes but no identity of the sources they were
    emitted from, so records reused from a saved directory are not tied to the
    sources the pipeline validated. The report and every claim it holds are then
    unresolved."""
    return (f"the declaration records were reused from {directory}, not emitted from this checkout, so they are "
            "not tied to the sources the pipeline validated")


def endpoint_audit_report(manifest_path, records, ledger=None, evidence_directory=None, reused_records=None):
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
    if reused_records is not None:
        reasons.append(reused_reason(reused_records))
    properties = list((manifest.get("claims") or {}).get("properties", []))
    if not properties:
        reasons.append("the manifest claims no property")
    claims = [claim(manifest, prop, records, registry, checks, connected_reasons, evidence, reused_records)
              for prop in properties]
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
        default_entry = report["manifest"]["entries"].get("proof", "")
        for item in report.get("security_claims", report["claims"]) or [{}]:
            entry = item.get("source_entry") or ((item.get("request") or {}).get("subject") or {}).get("entry", default_entry)
            identifiers = ", ".join(f"`{row['id']}`" for row in item.get("assumptions", []))
            reason = item.get("reasons", report["reasons"])
            verdict = item.get("status", item.get("outcome", report.get("status", report["outcome"])))
            note = f"{verdict}: {reason[0]}" if reason and verdict != "established" else verdict
            lines.append(f"| {report['subject']} | `{entry}` | {item.get('covered_endpoint', '')} | "
                         f"{item.get('property', '')} | {item.get('statement') or ''} | {identifiers} | {note} |")
    return "\n".join(lines) + "\n"


BOUND_CLAIMS_FORMAT = "zkc.bound-source-claims/0"
RECEIPT_TYPE = "Zkc.Claims.Receipt"
ADMITTED_RECEIPT_TYPE = "ZkcSecurity.Claims.AdmittedReceipt"
SECURITY_RECEIPT_TYPES = {ADMITTED_RECEIPT_TYPE, "ZkcSecurity.Claims.CanonicalReceipt",
                          "ZkcSecurity.Claims.AuthorExtensionReceipt"}
REQUEST_TYPE = "Zkc.Claims.Wire.Request"
ROUTES = {"endpoint", "theorem", "derivation"}
# The source receipt's expected obligations and product come from Lean's closed
# authority. Legacy endpoint inventories above retain their existing consumers.


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
                      allow_nan=False).encode("ascii")


def data_digest(value):
    return "sha256:" + hashlib.sha256(canonical(value)).hexdigest()


def request_projection(request):
    """Wire.Request preserves the complete native envelope, including targets."""
    return json.loads(json.dumps(request))


def claim_details(evidence):
    """Declarations requested by the pipeline; not a source of meanings."""
    return [item[key] for item in (evidence or {}).get("claim_receipts", [])
            for key in ("request_declaration", "receipt_declaration") if item.get(key)]


def owned_module_path(module):
    # Module ownership follows physical providers, independently of declaration
    # namespaces (notably ZkcSecurity declarations in ZkcArkLib modules).
    from .declarations import PACKAGES
    candidates = [directory / Path(*module.split(".")).with_suffix(".lean")
                  for directory, _ in PACKAGES.values()]
    found = [path for path in candidates if path.is_file()]
    if len(found) != 1:
        raise ValueError(f"owned module {module} has {len(found)} source providers")
    return found[0]


def verified_dependencies(packages):
    """Read-only preflight shared with reports; never prepare dependencies."""
    import subprocess
    from .declarations import PACKAGES
    verified, reasons, seen = [], [], set()
    for package in sorted(packages):
        if package not in PACKAGES:
            reasons.append(f"unknown package provider: {package}")
            continue
        directory = PACKAGES[package][0]
        manifest_path = directory / "lake-manifest.json"
        if not manifest_path.is_file():
            reasons.append(f"missing dependency manifest: {manifest_path}")
            continue
        manifest = json.loads(manifest_path.read_text())
        compatibility_path = directory / "compatibility.json"
        compatibility = json.loads(compatibility_path.read_text()) if compatibility_path.is_file() else None
        for pin in manifest.get("packages", []):
            if pin.get("type") != "git":
                continue
            source = (directory / manifest.get("packagesDir", ".lake/packages") /
                      pin["name"].removeprefix("«").removesuffix("»")).resolve()
            key = (str(source), pin["rev"])
            if key in seen:
                continue
            seen.add(key)
            try:
                head = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"],
                                               text=True, stderr=subprocess.DEVNULL).strip()
                if head != pin["rev"]:
                    raise ValueError("HEAD differs from locked revision")
                changed = set(subprocess.check_output(
                    ["git", "-C", str(source), "diff", "--name-only", "-z", "HEAD"],
                    stderr=subprocess.DEVNULL).decode().split("\0")) - {""}
                untracked = set(subprocess.check_output(
                    ["git", "-C", str(source), "ls-files", "--others", "--exclude-standard", "-z"],
                    stderr=subprocess.DEVNULL).decode().split("\0")) - {""}
                config = compatibility if compatibility and compatibility["package"] == pin["name"] else None
                if config:
                    if config["revision"] != pin["rev"] or sha256(directory / config["patch"]) != config["patch_sha256"]:
                        raise ValueError("compatibility pin or patch digest differs")
                    files = config["files"]
                    added = {name for name, values in files.items() if values["base_sha256"] is None}
                    if changed - files.keys() or untracked - added:
                        raise ValueError("undeclared dependency changes")
                    for name, values in files.items():
                        path = source / name
                        expected = values["patched_sha256"]
                        if (expected is None and path.exists()) or (expected is not None and
                                (not path.is_file() or sha256(path) != expected)):
                            raise ValueError(f"compatibility source differs: {name}")
                elif changed or untracked:
                    raise ValueError("dependency source has undeclared changes")
                verified.append({"package": pin["name"], "revision": head,
                                 "compatibility": config})
            except (OSError, ValueError, subprocess.CalledProcessError) as error:
                reasons.append(f"unverified dependency {pin['name']}: {error}")
    return verified, reasons


def verified_environment(records):
    """Verify dependencies again when assembling a report from fresh records."""
    facts = checker(records)
    verified, reasons = verified_dependencies(records.packages())
    facts["verified_dependencies"] = verified
    return facts, reasons


def semantic_dependencies(closure, records, environment):
    """A body-sensitive audit digest; never a replacement for type checking."""
    modules, identities, reasons = {}, [], []
    for item in closure:
        if not item.get("owned"):
            continue
        module = item.get("module")
        if not module:
            reasons.append(f"dependency {item.get('name')} has no module identity")
            continue
        if module not in modules:
            try:
                path = owned_module_path(module)
                modules[module] = {"path": str(path.relative_to(ROOT)), "sha256": sha256(path)}
            except ValueError as error:
                reasons.append(str(error))
        identities.append({key: item.get(key) for key in ("name", "module", "statement")})
    if not modules:
        reasons.append("no owned semantic dependency modules were emitted")
    payload = {"modules": modules, "declarations": sorted(identities, key=lambda item: item["name"]),
               "environment": environment}
    return {"digest": data_digest(payload), **payload}, reasons


def module_attached(module, modules):
    try:
        source = owned_module_path(module).resolve()
    except ValueError:
        return False
    return any((ROOT / item["path"]).resolve() == source for item in modules)


def receipt_attribution(receipt):
    """Optional method notes may be absent, malformed or unrecognizable."""
    try:
        provenance = receipt.get("provenance") or {}
        closure = receipt.get("dependencies") or []
        actual_names = {item.get("name") for item in receipt.get("proof_dependencies", closure)}
        route = receipt.get("root_route")
        declared_route = (provenance.get("root") or "").rsplit(".", 1)[-1]
        discharger = receipt.get("discharger")
        diagnostics = []
        if route == "constructor" and declared_route == "theorem":
            route = "theorem"
        if route not in ROUTES or declared_route != route:
            diagnostics.append("route attribution does not match the receipt constructor")
        if not discharger or provenance.get("discharger") != discharger or discharger not in actual_names:
            diagnostics.append("discharger attribution does not match the actual proof root")
        if any(name not in actual_names for name in provenance.get("dependencies", [])):
            diagnostics.append("dependency attribution is absent from the actual proof closure")
        if receipt.get("provenance_error"):
            diagnostics.append(receipt["provenance_error"])
        return ("unattributed" if diagnostics else route), diagnostics
    except (AttributeError, TypeError, ValueError) as error:
        return "unattributed", [f"optional attribution could not be read: {error}"]


class ReceiptTransportError(ValueError):
    """No usable Lean decision arrived; this is never a weaker audit path."""


def _receipt_provider_groups(payload):
    """Keep independent provider environments independent during extraction."""
    from .declarations import PACKAGES
    operation = payload.get("operation")
    records = payload.get("records") or []
    if operation == "receipt":
        roots = [payload.get("record"), payload.get("request_record")]
    elif operation == "extract":
        roots = records
    else:
        names = {mapping.get(key) for mapping in payload.get("mappings") or []
                 for key in ("request_declaration", "receipt_declaration")}
        roots = [record for record in records if record.get("name") in names]
    selected = {}
    for record in roots:
        if not record:
            continue
        module = record.get("module")
        if not isinstance(module, str) or not module:
            raise ReceiptTransportError("receipt root has no provider module")
        relative = Path(*module.split(".")).with_suffix(".lean")
        owners = [name for name, (directory, _) in PACKAGES.items() if (directory / relative).is_file()]
        if len(owners) != 1:
            raise ReceiptTransportError(f"receipt provider {module} has {len(owners)} source owners")
        selected.setdefault(owners[0], set()).add(module)
    return selected


def _invoke_receipt_classifier(payload, packages):
    from .declarations import PACKAGES
    built = subprocess.run(["lake", "build", "declaration-records"], cwd=LEAN,
                           text=True, capture_output=True)
    if built.returncode:
        raise ReceiptTransportError(built.stdout + built.stderr)
    # Lean resolves a module namespace from its first search-path provider,
    # even when that provider lacks a particular object. Concatenating sibling
    # paths therefore cannot safely combine independent build closures.
    providers = []
    for package, modules in sorted(_receipt_provider_groups(payload).items()):
        if package not in PACKAGES:
            raise ReceiptTransportError(f"unknown receipt provider package: {package}")
        directory = PACKAGES[package][0]
        search = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], cwd=directory,
                                text=True, capture_output=True)
        if search.returncode:
            raise ReceiptTransportError(search.stderr.strip() or "missing provider search path")
        paths = [str((directory / path).resolve()) for path in search.stdout.strip().split(os.pathsep) if path]
        providers.append({"modules": sorted(modules), "search_paths": list(dict.fromkeys(paths))})
    # This identifier binds a response to this exact invocation. It is transport
    # metadata, never a substitute for a proof or the fresh kernel extraction.
    payload = {**payload, "providers": providers}
    exchange = {"nonce": uuid.uuid4().hex, "input_digest": data_digest(payload)}
    payload = {**payload, "exchange": exchange}
    command = ["lake", "env", str(LEAN / ".lake/build/bin/declaration-records"), "--receipt-status"]
    result = subprocess.run(command, cwd=LEAN, input=json.dumps(payload) + "\n",
                            text=True, capture_output=True)
    if result.returncode:
        raise ReceiptTransportError(result.stderr.strip() or "Lean classifier exited without an export")
    try:
        export = json.loads(result.stdout)
    except (ValueError, TypeError) as error:
        raise ReceiptTransportError(f"corrupt Lean status export: {error}") from error
    if not isinstance(export, dict) or export.get("format") != "zkc.receipt-status/0" or export.get("authority") != "fresh-kernel-audit/0":
        raise ReceiptTransportError("missing current Lean status export/provenance")
    if export.get("exchange") != exchange:
        raise ReceiptTransportError("Lean status export answers another audit invocation")
    return export


def _audit_payload(declarations, **fields):
    return {"format": "zkc.receipt-audit-input/0", "headers": list(declarations.headers.values()), **fields}


def _validate_audit(audit):
    if (not isinstance(audit, dict) or audit.get("status") not in {"certified", "open", "incomplete"} or
            audit.get("outcome") not in {"established", "unresolved"} or
            any(not isinstance(audit.get(key), list) for key in ("reasons", "assumptions", "discharged", "checks")) or
            any(not isinstance(reason, str) for reason in audit.get("reasons", [])) or
            any(not isinstance(check, dict) or type(check.get("passed")) is not bool or
                check.get("origin") not in {"kernel-extraction", "external-admission", "resolution"} or
                not isinstance(check.get("reason"), str) for check in audit.get("checks", [])) or
            any(not isinstance(row, dict) or
                any(not isinstance(row.get(key), str) for key in ("id", "category", "discharge", "source"))
                for field in ("assumptions", "discharged") for row in audit.get(field, [])) or
            (audit["status"] == "certified" and (audit["reasons"] or not audit["checks"] or
                not all(check["passed"] for check in audit["checks"]))) or
            (audit["status"] == "certified") != (audit["outcome"] == "established")):
        raise ReceiptTransportError("missing or corrupt Lean item status export")
    return audit


def _referenced_records(records, roots):
    """Join only the supplied roots and their emitted dependency identities."""
    names = {record["name"] for record in roots if record}
    for record in roots:
        proof = (((record or {}).get("detail") or {}).get("claim_data") or {}).get("receipt") or {}
        names.update(row.get("name") for row in proof.get("dependencies") or [] if records.get(row.get("name")))
        artifact = (proof.get("subject") or {}).get("artifacts_head")
        if records.get(artifact):
            names.add(artifact)
    selected = {name: records.get(name) for name in names if records.get(name)}
    selected.update({record["name"]: record for record in roots if record})
    return [selected[name] for name in sorted(selected)]


def audit_receipt(record, request_record, request, registry, records, generated_modules=None):
    payload = _audit_payload(records, operation="receipt", record=record, request_record=request_record,
                             request=request, records=_referenced_records(records, [record, request_record]))
    receipt = ((record.get("detail") or {}).get("claim_data") or {}).get("receipt") or {}
    route, attribution = receipt_attribution(receipt)
    receipt = {**receipt, "root_route": route, "attribution_diagnostics": attribution}
    try:
        export = _invoke_receipt_classifier(payload, records.packages())
        audit = _validate_audit(export.get("audit"))
    except (ReceiptTransportError, OSError) as error:
        return receipt, [], [], [f"receipt status transport failure: {error}"]
    return receipt, audit["assumptions"], audit["discharged"], audit["reasons"]


def source_entry(item):
    export = _invoke_receipt_classifier({"format": "zkc.receipt-audit-input/0",
        "operation": "entry", "item": item}, {"main"})
    return export["entry"], export["reasons"]


def _scope_export(source, mappings, records, modules, evidence, checks, reasons,
                  environment, environment_reasons, reused_records, *, trial=False, scope=None, proof_entry=None,
                  consumer_requirements=None, consumer_context=None):
    roots = [records.get(mapping.get(key)) for mapping in mappings
             for key in ("request_declaration", "receipt_declaration")]
    selected_records = _referenced_records(records, roots)
    attached_modules = [record["module"] for record in selected_records
                        if module_attached(record["module"], modules)]
    items = []
    for item in source.get("claims", []):
        node = (item.get("attachment") or {}).get("node")
        candidates = [mapping for mapping in mappings if mapping.get("node") == node]
        mapping = candidates[0] if len(candidates) == 1 else {}
        record = records.get(mapping.get("receipt_declaration")) or {}
        receipt = ((record.get("detail") or {}).get("claim_data") or {}).get("receipt") or {}
        dependencies, failures = semantic_dependencies(receipt.get("dependencies") or [], records, environment)
        items.append({**item, "admitted_request_digest": data_digest(item.get("request") or {}),
                      "semantic_dependencies": dependencies, "dependency_reasons": failures})
    payload = _audit_payload(records, operation="scope", records=selected_records,
        source={**source, "claims": items}, mappings=mappings, evidence=evidence or {}, validation=checks,
        reasons=reasons, environment_reasons=environment_reasons, attached_modules=attached_modules,
        reused_reason=reused_reason(reused_records) if reused_records is not None else None,
        trial=trial, scope=scope, proof_entry=proof_entry, consumer_requirements=consumer_requirements,
        consumer_context=consumer_context,
        validate_scope=scope is not None or proof_entry is not None)
    export = _invoke_receipt_classifier(payload, records.packages())
    if not isinstance(export, dict) or export.get("format") != "zkc.receipt-status/0":
        raise ReceiptTransportError("missing or corrupt Lean scope status export")
    rows = export.get("claims")
    if (not isinstance(rows, list) or len(rows) != len(items) or
            export.get("status") not in {"certified", "open", "incomplete", "no-claim"} or
            export.get("outcome") not in {"established", "unresolved"} or
            not isinstance(export.get("reasons"), list) or
            any(not isinstance(reason, str) for reason in export.get("reasons", [])) or
            (export["status"] == "certified") != (export["outcome"] == "established") or
            export.get("audit_status") not in {"checked", "unaudited"} or
            (export["status"] == "certified" and export["audit_status"] != "checked")):
        raise ReceiptTransportError("missing or corrupt Lean scope status export")
    # Check one export per requested occurrence; digest equality alone cannot
    # distinguish two occurrences requesting the same meaning.
    for item, row in zip(items, rows, strict=True):
        if (not isinstance(row, dict) or row.get("node") != (item.get("attachment") or {}).get("node") or
                row.get("request_digest") != item["admitted_request_digest"] or
                row.get("claim_kind") not in {"canonical", "author", "generic", "reserved", "unresolved"} or
                row.get("semantic_dependencies") != item["semantic_dependencies"]):
            raise ReceiptTransportError("Lean status export has a wrong source/request association")
        _validate_audit(row.get("audit"))
    security_rows = [row for row in rows if row["claim_kind"] not in {"author", "generic"}]
    if ((export["audit_status"] == "unaudited" and
            any(row["audit"]["status"] == "certified" for row in rows)) or
            (export["status"] == "certified" and (not security_rows or export["reasons"] or
            any(row["audit"]["status"] != "certified" for row in security_rows))) or
            (export["status"] == "no-claim" and security_rows)):
        raise ReceiptTransportError("inconsistent Lean scope/item status exports")
    if export.get("consumer_requirements") != consumer_requirements:
        raise ReceiptTransportError("Lean scope audit answered another consumer requirement set")
    requirements = export.get("requirements")
    if consumer_requirements is None:
        if requirements is not None:
            raise ReceiptTransportError("Lean export invented consumer requirements")
    else:
        if (not isinstance(requirements, dict) or requirements.get("input") != consumer_requirements
                or requirements.get("context") != consumer_context
                or requirements.get("status") not in {"certified", "open", "incomplete"}
                or requirements.get("outcome") not in {"established", "unresolved"}
                or (requirements["status"] == "certified") != (requirements["outcome"] == "established")
                or not isinstance(requirements.get("claims"), list)
                or len(requirements["claims"]) != len(consumer_requirements["claims"])):
            raise ReceiptTransportError("Lean export changed the consumer requirement set or context")
        context_matches = consumer_requirements["context"] == consumer_context
        for expected, row in zip(consumer_requirements["claims"], requirements["claims"], strict=True):
            if (not isinstance(row, dict) or row.get("node") != expected["node"]
                    or row.get("request") != expected["request"]
                    or row.get("status") not in {"certified", "open", "incomplete"}
                    or not isinstance(row.get("matching_nodes"), list)
                    or not isinstance(row.get("certified_nodes"), list)
                    or not isinstance(row.get("reasons"), list)
                    or any(not isinstance(reason, str) for reason in row.get("reasons", []))):
                raise ReceiptTransportError("Lean export has a wrong consumer requirement association")
            # Consistency of this transport with its already audited rows. This
            # does not classify proofs or match caller-provided request digests.
            occurrences = [(item, claim) for item, claim in zip(items, rows, strict=True)
                           if claim["node"] == expected["node"]]
            candidates = [claim for item, claim in occurrences if item.get("request") == expected["request"]]
            proved = ([claim for claim in candidates if claim["audit"]["status"] == "certified"]
                      if context_matches and len(occurrences) == 1 else [])
            if (row["matching_nodes"] != [claim["node"] for claim in candidates]
                    or row["certified_nodes"] != [claim["node"] for claim in proved]
                    or (row["status"] == "certified") != bool(proved)):
                raise ReceiptTransportError("inconsistent Lean consumer requirement status export")
        covered = all(row["status"] == "certified" for row in requirements["claims"])
        if (requirements["status"] == "certified") != covered:
            raise ReceiptTransportError("inconsistent Lean consumer coverage export")
        if export["status"] in {"certified", "no-claim"} and not covered:
            raise ReceiptTransportError("Lean aggregate omitted a consumer requirement")
    return export, items


def requested_claim(item, mappings, records, registry, modules, evidence, checks, connected_reasons,
                    environment, environment_reasons, reused_records, *, _export=None):
    if _export is None:
        export, _ = _scope_export({"claims": [item]}, mappings, records, modules, evidence, checks,
            connected_reasons, environment, environment_reasons, reused_records)
        _export = export["claims"][0]
    audit = _export["audit"]
    request = item.get("request") or {}
    digest = data_digest(request)
    node = (item.get("attachment") or {}).get("node")
    candidates = [mapping for mapping in mappings if mapping.get("node") == node]
    mapping = candidates[0] if len(candidates) == 1 else {}
    receipt_record = records.get(mapping.get("receipt_declaration"))
    receipt = (((receipt_record or {}).get("detail") or {}).get("claim_data") or {}).get("receipt") or {}
    route, attribution = receipt_attribution(receipt)
    receipt = {**receipt, "root_route": route, "attribution_diagnostics": attribution}
    assumptions, discharged, reasons = audit["assumptions"], audit["discharged"], audit["reasons"]
    # Render the observation Lean audited. A second filesystem read can report
    # a different body digest while retaining the first observation's status.
    dependencies = _export["semantic_dependencies"]
    entry = item.get("source_entry", (request.get("subject") or {}).get("entry"))
    subject = request.get("subject") or {}
    obligations = [{"identity": digest, "typed_statement_digest": data_digest(receipt.get("proposition")),
                    "context_digest": data_digest(receipt.get("context") or []),
                    "parameter_telescope": receipt.get("context") or [], "expected_responsibility_layer": "P",
                    "root_route": receipt.get("root_route") or "open", "discharger": receipt.get("discharger"),
                    "attachment": item.get("attachment")}]
    for expected_link in (receipt.get("stage_links") or {}).get("obligations", []):
        identifier = expected_link.get("identifier")
        proved = next((row for row in discharged if row["id"] == identifier), None)
        expected_link = next((row for row in (receipt.get("stage_links") or {}).get("obligations", [])
                              if row.get("identifier") == identifier), {})
        obligations.append({"identity": identifier, "goal": expected_link.get("goal"),
                            "goal_identity": expected_link.get("goal_identity"),
                            "typed_statement_digest": data_digest(expected_link.get("goal")),
                            "context_digest": data_digest(expected_link.get("context")),
                            "expected_responsibility_layer": expected_link.get("expected_responsibility_layer"),
                            "root_route": "theorem" if proved else "open",
                            "status": "certified" if proved else "open"})
    stage_identifiers = {link.get("identifier") for link in
                         (receipt.get("stage_links") or {}).get("obligations", [])}
    for link in receipt.get("required_links") or []:
        if link.get("identifier") in stage_identifiers:
            continue
        obligations.append({"identity": link.get("identifier"), "goal": link.get("goal"),
            "typed_statement_digest": data_digest(link.get("goal")),
            "context_digest": data_digest(link.get("context")),
            "expected_responsibility_layer": link.get("expected_responsibility_layer"),
            "root_route": "theorem" if link.get("proved") else "open",
            "status": "certified" if link.get("proved") else "open"})
    resolution = mapping.get("resolution") or {}
    state, claim_kind = audit["status"], _export["claim_kind"]
    obligations[0]["status"] = state
    return {"request": request, "request_digest": digest, "attachment": item.get("attachment"),
            "property": (request.get("property") or {}).get("name"),
            "covered_endpoint": (receipt.get("stage_links") or {}).get("covered_endpoint") or subject.get("stage"),
            "requested_stage": subject.get("stage"), "statement": None,
            "claim_kind": claim_kind,
            "status": state, "outcome": audit["outcome"], "audit_checks": audit["checks"],
            "product": "author_extension" if claim_kind == "author" else
                       (receipt.get("authority") or {}).get("product", "unresolved"), "scope": "ir-relative", "native_closure": "open",
            "validation": checks["outcome"], "resolution": resolution, "attempts": mapping.get("attempts") or [],
            "method_plan": item.get("method"), "receipt": receipt_record and receipt_record["name"],
            "root_route": receipt.get("root_route"), "discharger": receipt.get("discharger"),
            "attribution_diagnostics": receipt.get("attribution_diagnostics") or [],
            "method_version": ((receipt.get("provenance") or {}).get("method")
                               if isinstance(receipt.get("provenance"), dict) else None),
            "exported_capabilities": receipt.get("exported_capabilities") or [],
            "application_coverage": receipt.get("application_coverage"),
            "source_entry": entry, "entry_association": item.get("entry_association"),
            "honest_input": receipt.get("honest_input"),
            "actual_dependency_declarations": receipt.get("proof_dependencies") or [],
            "actual_receipt_dependencies": receipt.get("dependencies") or [], "obligations": obligations,
            "checked_correspondences": [row for row in discharged if row.get("category") == "stage-link"],
            "assumptions_by_category": {category: [row for row in assumptions if row["category"] == category]
                                        for category in sorted({row["category"] for row in assumptions})},
            "semantic_dependencies": dependencies, "assumptions": assumptions, "discharged": discharged,
            "bound": {"property": receipt.get("proposition")}, "reasons": list(dict.fromkeys(reasons)),
            "matching": {"kernel": (["registered resolution", "evaluated meaning", "receipt proof type"]
                                    if receipt.get("indices_checked") is True else []),
                         "frontend": ["source request association", "artifact byte digests", "source site labels"]}}


def scope_reasons(source, scope, proof_entry=None):
    export = _invoke_receipt_classifier({"format": "zkc.receipt-audit-input/0",
        "operation": "scope-reasons", "source": source, "scope": scope, "proof_entry": proof_entry}, {"main"})
    return export["reasons"]


def report_claim_scope(source, mappings, records, registry, modules, evidence, checks, reasons,
                       environment, environment_reasons, reused_records, *, trial=False, scope=None, proof_entry=None,
                       consumer_requirements=None, consumer_context=None):
    """Join/render exactly one Lean classification for every requested item."""
    try:
        export, _ = _scope_export(source, mappings, records, modules, evidence, checks, reasons,
            environment, environment_reasons, reused_records, trial=trial, scope=scope, proof_entry=proof_entry,
            consumer_requirements=consumer_requirements, consumer_context=consumer_context)
    except (ReceiptTransportError, OSError) as error:
        # A failed transport has no security decision. In particular it cannot
        # become `incomplete` by consulting a frontend resolution fallback.
        diagnostic = f"receipt status transport failure: {error}"
        claims = [{"request": item.get("request"), "attachment": item.get("attachment"),
                   "claim_kind": "unresolved", "status": "transport-failure", "outcome": "unresolved",
                   "product": "unresolved", "reasons": [diagnostic]}
                  for item in source.get("claims", [])]
        return {"claims": claims, "security_claims": claims, "author_claims": [], "generic_claims": [],
                "status": "transport-failure", "outcome": "unresolved", "reasons": [diagnostic],
                "audit_status": "transport-failure", "requirements": None,
                "consumer_requirements": consumer_requirements}
    claims = [requested_claim(item, mappings, records, registry, modules, evidence, checks,
        reasons, environment, environment_reasons, reused_records, _export=row)
        for item, row in zip(source.get("claims", []), export["claims"], strict=True)]
    return {"claims": claims,
            "security_claims": [item for item in claims if item["claim_kind"] not in {"author", "generic"}],
            "author_claims": [item for item in claims if item["claim_kind"] == "author"],
            "generic_claims": [item for item in claims if item["claim_kind"] == "generic"],
            "outcome": export["outcome"], "status": export["status"], "reasons": export["reasons"],
            "audit_status": export.get("audit_status", "checked"),
            "requirements": export.get("requirements"),
            "consumer_requirements": export.get("consumer_requirements")}



CONSUMER_REQUIREMENTS_MAX_BYTES = 4 * 1024 * 1024
CONSUMER_REQUIREMENTS_MAX_DEPTH = 64


def read_consumer_requirements(path):
    """Bound untrusted input before the strict JSON and envelope checks."""
    from bridges.pipeline.source_claims import decode

    with Path(path).open("rb") as source:
        data = source.read(CONSUMER_REQUIREMENTS_MAX_BYTES + 1)
    if len(data) > CONSUMER_REQUIREMENTS_MAX_BYTES:
        raise ValueError("consumer requirements exceed the 4 MiB byte limit")
    text = data.decode("utf-8")
    depth = 0
    quoted = escaped = False
    for char in text:
        if quoted:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                quoted = False
        elif char == '"':
            quoted = True
        elif char in "[{":
            depth += 1
            if depth > CONSUMER_REQUIREMENTS_MAX_DEPTH:
                raise ValueError("consumer requirements exceed the nesting limit of 64")
        elif char in "]}":
            depth -= 1
    try:
        return validate_consumer_requirements(decode(text))
    except RecursionError as error:
        raise ValueError("consumer requirements exceed decoder recursion limits") from error


def validate_consumer_requirements(value):
    """Validate transport shape; only Lean assigns consumer coverage status."""
    if (not isinstance(value, dict) or set(value) != {"format", "context", "claims"}
            or value.get("format") != "zkc.consumer-requirements/0"
            or not isinstance(value.get("claims"), list) or not value["claims"]):
        raise ValueError("invalid consumer requirements envelope or empty claim set")
    context = value.get("context")
    if (not isinstance(context, dict) or set(context) != {"subject", "manifest_sha256", "checker"}
            or any(not isinstance(context.get(key), str) or not context[key].strip()
                   for key in ("subject", "manifest_sha256"))
            or not isinstance(context.get("checker"), dict)):
        raise ValueError("invalid consumer requirements context")
    nodes = []
    for row in value["claims"]:
        if (not isinstance(row, dict) or set(row) != {"node", "request"}
                or not isinstance(row.get("node"), dict) or not row["node"] or row["node"] in nodes
                or not isinstance(row.get("request"), dict) or not row["request"]):
            raise ValueError("consumer requirements need distinct occurrences and full request objects")
        nodes.append(row["node"])
    return value


def build(manifest_path, records, ledger=None, evidence_directory=None, reused_records=None, *,
          consumer_requirements=None):
    """Build reports only from source requests and checked emitted receipts."""
    manifest = load_manifest(manifest_path)
    if consumer_requirements is not None:
        validate_consumer_requirements(consumer_requirements)
    evidence = load_evidence(evidence_directory, manifest["name"])
    modules = attached(manifest)
    connected, connected_reasons = connection(manifest, manifest_path, modules, evidence)
    checks = validation(evidence)
    reasons = []
    try:
        entries, endpoints = records.registry()
        registry = Registry(entries, endpoints)
    except ValueError as error:
        registry = Registry([], [])
        reasons.append(str(error))
    environment, environment_reasons = verified_environment(records)
    if evidence is not None and evidence.get("format") != EVIDENCE_FORMAT:
        reasons.append("unsupported pipeline evidence format")
    if evidence is not None and evidence.get("manifest_sha256") != sha256(manifest_path):
        reasons.append("pipeline evidence lacks this exact manifest identity")
    source = (evidence or {}).get("source_claims") or {}
    if source.get("format") != BOUND_CLAIMS_FORMAT:
        reasons.append("no bound source claim export was produced")
    scope = (evidence or {}).get("source_claim_scope")
    common_reasons = reasons + connected_reasons
    selected_reasons = common_reasons
    selected = report_claim_scope(source, (evidence or {}).get("claim_receipts") or [], records, registry,
                                  modules, evidence, checks, selected_reasons, environment,
                                  environment_reasons, reused_records, scope=scope,
                                  proof_entry=(manifest.get("entries") or {}).get("proof"),
                                  consumer_requirements=consumer_requirements,
                                  consumer_context={"subject": manifest["name"],
                                      "manifest_sha256": sha256(manifest_path), "checker": environment})
    trials = []
    for trial in (evidence or {}).get("source_claim_trials") or []:
        entry = trial.get("entry")
        bound = {**source, "entry": entry, "entries": [entry], "claims": trial.get("claims") or []}
        trial_evidence = {**(evidence or {}), "source_claims": bound}
        trial_scope = {"entries": [entry], "selection": "explicit"}
        mappings = trial.get("claim_receipts") or []
        audited = report_claim_scope(bound, mappings, records, registry, modules, trial_evidence, checks,
                                     common_reasons, environment, environment_reasons,
                                     reused_records, trial=True, scope=trial_scope)
        trials.append({"entry": entry, "source_claim_scope": trial_scope,
                       "bound_claims": bound["claims"], "claim_receipts": mappings,
                       **audited})
    try:
        relative = str(Path(manifest_path).resolve().relative_to(ROOT))
    except ValueError:
        relative = str(manifest_path)
    products = {claim["product"] for claim in selected["security_claims"]}
    product = next(iter(products)) if len(products) == 1 else "assurance_report"
    return {"format": FORMAT, "subject": manifest["name"], **selected,
            "product": product, "scope": "ir-relative", "native_closure": "open",
            "source_claim_scope": scope, "source_claim_trials": trials,
            "source_claim_inventory": (evidence or {}).get("source_claim_inventory", []),
            "manifest": {"path": relative, "sha256": sha256(manifest_path),
                "schema": manifest.get("schema"), "entries": manifest.get("entries") or {}},
            "artifacts": {"attached": modules, "connected": connected}, "checker": environment,
            "context": context(manifest, ledger, records, registry),
            "allowed_axioms": list(ALLOWED_AXIOMS)}
