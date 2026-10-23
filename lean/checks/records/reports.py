"""Assurance reports: `zkc.assurance-report/0`, one per compiled subject.

Requested meanings come only from bound source claims. Typed receipt indices,
actual proofs and their dependencies are extracted by Lean. Legacy endpoint
helpers remain for mathematical ledger and negative-control auditing; they do
not select requested claims for the public report builder. `lean/docs/spec/assurance-report.md` specifies the format.
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


def receipt_join(mapping, records, modules, evidence):
    reasons = []
    for key in ("request_declaration", "receipt_declaration"):
        name = mapping.get(key)
        record = records.get(name) if name else None
        if not record:
            reasons.append(f"missing emitted {key}: {name}")
        elif not module_attached(record["module"], modules):
            reasons.append(f"mismatched artifact: {key} {name} is outside this subject's generated modules")
    receipt = records.get(mapping.get("receipt_declaration"))
    if not any(check.get("name") == "claim-receipt" and check.get("outcome") == "accepted" and
               check.get("module") == (receipt or {}).get("module") and
               check.get("request") == mapping.get("request_declaration") and
               check.get("receipt") == mapping.get("receipt_declaration")
               for check in (evidence or {}).get("checks", [])):
        reasons.append("no accepted claim-receipt check built the actual request and receipt declarations")
    return reasons


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


def audit_receipt(record, request_record, request, registry, records, generated_modules=None):
    reasons, assumptions, discharged = [], [], []
    if not records.headers or any(header.get("axiom_provenance") != "resolved-constant-info/0" or
                                  header.get("reference_provenance") != "checked-stored-module/0"
                                  for header in records.headers.values()):
        reasons.append("declaration records lack checked stored-provider/actual-axiom provenance")
    detail = record.get("detail") or {}
    data = detail.get("claim_data") or {}
    receipt = data.get("receipt") or {}
    if detail.get("type_head") not in ({RECEIPT_TYPE} | SECURITY_RECEIPT_TYPES) or not receipt:
        reasons.append(f"proof type mismatch: {record['name']} is not an extracted typed Receipt")
    if data.get("extraction_error"):
        reasons.append(f"receipt extraction failed: {data['extraction_error']}")
    request_detail = (request_record or {}).get("detail") or {}
    actual_request = (request_detail.get("claim_data") or {}).get("wire_request")
    try:
        expected = request_projection(request)
    except (ValueError, KeyError, TypeError) as error:
        expected = None
        reasons.append(f"request cannot be represented: {error}")
    if request_detail.get("type_head") != REQUEST_TYPE or actual_request != expected:
        reasons.append("wrong request: emitted Wire.Request differs from the bound source request")
    if receipt.get("wire_request") != expected:
        reasons.append("wrong request: Receipt indices do not name the actual bound request declaration")
    if receipt.get("indices_checked") is not True or receipt.get("proof_type_matches") is not True:
        reasons.append("proof type mismatch: Resolved/Evaluated/Receipt indices were not checked")
    registered = receipt.get("registered_property")
    expected_identifier = {key: (request.get("property") or {}).get(key) for key in ("name", "version")}
    if registered != expected_identifier:
        reasons.append("wrong registered property: actual Resolved export differs from the request")
    # Canonical keys, complete exports and outer premise authorization have a
    # single owner: Lean. No Python name/category list grants permission.
    authority = receipt.get("authority") or {}
    recognized = authority.get("kind") == "canonical" and authority.get("checked") is True
    security = (receipt.get("admission") or {}).get("security_subject") is True
    if authority.get("kind") == "reserved" or (security and authority.get("checked") is not True):
        reasons.append("unrecognized property/model registry or reserved author extension")
    quantity = (request.get("quantity") or {}).get("kind")
    capabilities = receipt.get("exported_capabilities") or []
    if request.get("capabilities") and not recognized:
        reasons.append("requested capabilities have no recognized checked consumer")
    if capabilities and not (recognized and quantity == "charged"):
        reasons.append("unrecognized or unsupported capability export")
    if recognized:
        if receipt.get("quantity_kind") != quantity:
            reasons.append("wrong quantity: evaluated typed arguments differ from the wire quantity")
        if quantity == "charged" and "capabilities.charged_reduction@0" not in capabilities:
            reasons.append("missing charged reduction capability in the actual evaluated receipt")
        if quantity == "scalar" and "capabilities.charged_reduction@0" in capabilities:
            reasons.append("scalar request cannot export a charged reduction without a charged meaning")
        coverage = receipt.get("application_coverage") or {}
        if coverage.get("checked") is not True:
            reasons.append("application coverage is not checked against the actual designated request binder/model")
        mode = coverage.get("mode")
        if mode not in {"fixed-statement", "honest-inputs", "parameter", "fixed"}:
            reasons.append("unrecognized application coverage mode")
        if mode in {"parameter", "fixed"} and not all(coverage.get(key) is True for key in
                ("context_matches", "reference_matches", "model_value_matches")):
            reasons.append("application coverage context/reference/value comparison failed")
        if mode == "parameter" and (coverage.get("value_is_binder") is not True or
                                     not coverage.get("designated_binder")):
            reasons.append("parameter application does not equal the designated free request binder")
        if mode == "fixed" and (not isinstance(coverage.get("fixed_value"), str) or
                                coverage.get("designated_binder") is not None):
            reasons.append("fixed application scope is not concrete or narrows a designated free request binder")
    for capability in request.get("capabilities") or []:
        key = f"{capability.get('name')}@{capability.get('version')}"
        if key not in capabilities:
            reasons.append(f"missing requested capability: {key}")
    typed_subject = receipt.get("subject") or {}
    if recognized and not typed_subject.get("artifacts_head"):
        reasons.append("missing actual typed security subject artifact identity")
    admission = receipt.get("admission") or {}
    security_subject = (bool(typed_subject) or security or recognized or
                        detail.get("type_head") in SECURITY_RECEIPT_TYPES)
    if security_subject:
        if admission.get("security_subject") is not True or admission.get("associated") is not True:
            reasons.append("missing typed security model admission association")
        if admission.get("subject_checked") is not True:
            reasons.append("actual security Subject.check did not admit this request/target/acceptance")
        if admission.get("model_status") != "admitted":
            reasons.append(f"actual security model resolution is {admission.get('model_status', 'unchecked')}")
        if detail.get("type_head") in SECURITY_RECEIPT_TYPES and admission.get("certificate_checked") is not True:
            reasons.append("typed security admission certificate does not match the actual receipt indices")
    for current, origin in ((record, "receipt"), (request_record, "request")):
        if not current:
            continue
        if origin == "receipt":
            policy = receipt.get("telescope") or {}
            if policy.get("accepted") is not True:
                rejected = [row for row in policy.get("binders", []) if row.get("classification") == "refused"]
                reasons += [f"{row.get('reason')}: {row.get('binder')} binder {row.get('type')} of {current['name']}"
                            for row in rejected] or ["missing Lean telescope authorization"]
            assumptions += [{**row, "discharge": "assumed", "source": f"authorized premise of {current['name']}"}
                            for row in policy.get("conditions", [])]
        else:
            policy = (current.get("detail") or {}).get("claim_data") or {}
            policy = policy.get("telescope") or {}
            if policy.get("accepted") is not True:
                reasons.append("request declaration lacks Lean telescope authorization")
        reasons += declaration(records, current["name"], origin)[1]
    # Optional provenance attributes a method; it cannot add assumptions or
    # restrict which kernel-checked proof establishes the fixed meaning.
    route, attribution = receipt_attribution(receipt)
    closure = receipt.get("dependencies") or []
    # Actual axioms and provider identities remain authoritative. Unsupplied
    # transitive function telescopes are not remaining caller premises.
    for item in closure:
        current = records.get(item.get("name"))
        if current:
            reasons += declaration(records, current["name"], "dependency")[1]
    # Independently reconstructed typed stage goals, never caller-selected
    # labels, determine the interpreted endpoint's required links.
    links = receipt.get("required_links") or []
    identifiers = [link.get("identifier") for link in links]
    if len(identifiers) != len(set(identifiers)):
        reasons.append("ambiguous registered obligation identifiers")
    for link in links:
        if link.get("proved") is not True:
            reasons.append(f"unproved registered obligation: {link.get('identifier')}")
    # Generic author properties have their registered links above, but no
    # compiled security stage. A typed/canonical security receipt must also
    # reconstruct all stage obligations from its actual subject.
    if security_subject:
        stage_facts = receipt.get("stage_links") or {}
        stage_recognized = stage_facts.get("recognized_subject") is True
        if not stage_recognized:
            reasons.append("unrecognized actual typed compiled subject: stage obligations were not reconstructed")
        if stage_recognized and stage_facts.get("stage") != (request.get("subject") or {}).get("stage"):
            reasons.append("wrong interpreted stage: typed subject differs from the request")
        expected_links = stage_facts.get("obligations") or []
        required = tuple(link.get("identifier") for link in expected_links)
        if stage_recognized and (not required or len(set(required)) != len(required)):
            reasons.append("incomplete checked stage obligations: missing or ambiguous Lean authority policy")
        for identifier in required:
            expected = [link for link in expected_links if link.get("identifier") == identifier]
            if not stage_recognized or len(expected) != 1:
                reasons.append(f"missing required interpreted-stage link: {identifier}")
                continue
            matches = expected[0].get("matches") or []
            matching = ([link for link in links if link.get("index") == matches[0].get("index") and
                         link.get("identifier") == identifier] if len(matches) == 1 else [])
            if len(matching) != 1 or matching[0].get("proved") is not True:
                reasons.append(f"missing required interpreted-stage link: {identifier}")
            elif matches[0].get("goal_defeq") is not True or matches[0].get("subject_matches") is not True:
                reasons.append(f"wrong actual subject or goal for interpreted-stage link: {identifier}")
            else:
                discharged.append({"id": identifier, "category": "stage-link", "schema": expected[0].get("goal_head"),
                    "statement": expected[0].get("goal"), "instantiated": matching[0].get("goal"),
                    "discharge": "proved", "source": "kernel comparison with actual Subject.stageLinks",
                    "goal_identity": expected[0].get("goal_identity"), "context": expected[0].get("context")})
    assumptions.append({"id": "source.correspondence", "category": "trusted-link",
                        "schema": None, "statement": "Source-to-IR correspondence remains unproved",
                        "instantiated": None, "discharge": "assumed", "source": "IR-relative milestone"})
    return {**receipt, "root_route": route, "attribution_diagnostics": attribution}, assumptions, discharged, reasons


def source_entry(item):
    """Resolve author-facing scope through the checked frontend association.

    The association is attribution, not kernel correspondence. Without it only
    an exactly equal source/request Entry is supported.
    """
    protocol = ((item.get("request") or {}).get("subject") or {}).get("entry")
    entry = item.get("source_entry", protocol)
    reasons = []
    if not isinstance(protocol, str) or not protocol or not isinstance(entry, str) or not entry:
        return None, ["invalid source/request Entry"]
    association = item.get("entry_association")
    if association is None:
        if entry != protocol:
            reasons.append("source alias lacks a checked interface Entry association")
    elif (not isinstance(association, dict) or
          set(association) != {"source_entry", "protocol", "interface_digest", "attribution"} or
          association.get("source_entry") != entry or association.get("protocol") != protocol or
          association.get("attribution") != "trusted-frontend-checked-interface" or
          not isinstance(association.get("interface_digest"), str) or
          re.fullmatch(r"sha256:[0-9a-f]{64}", association["interface_digest"]) is None):
        reasons.append("source/request Entry differs from its checked interface association")
    return entry, reasons


def requested_claim(item, mappings, records, registry, modules, evidence, checks, connected_reasons,
                    environment, environment_reasons, reused_records):
    request = item.get("request") or {}
    reasons = list(connected_reasons) + list(environment_reasons)
    digest = data_digest(request)
    node = (item.get("attachment") or {}).get("node")
    if item.get("request_digest") != digest:
        reasons.append("wrong request digest: bound source request bytes changed")
    candidates = [mapping for mapping in mappings if mapping.get("node") == node]
    if len(candidates) != 1:
        reasons.append("missing or ambiguous request/receipt source-node association")
    mapping = candidates[0] if len(candidates) == 1 else {}
    if mapping and mapping.get("request_digest") != digest:
        reasons.append("wrong request digest: receipt association is stale")
    if reused_records is not None:
        reasons.append(reused_reason(reused_records))
    subject = request.get("subject") or {}
    artifacts = (evidence or {}).get("artifacts") or {}
    # Pipeline artifact keys are stable byte roles, not claim semantics.
    unit_key = "interactive_export" if subject.get("stage") == "interactive" else "original_export"
    if subject.get("unit") != artifacts.get(unit_key):
        reasons.append("mismatched artifact: request unit is not the admitted original export")
    raw_receipt = (((records.get(mapping.get("receipt_declaration")) or {}).get("detail") or {}).get("claim_data") or {})
    role_policy = (((raw_receipt.get("receipt") or {}).get("stage_links") or {}).get("artifact_roles")) or []
    expected_roles = {row.get("role") for row in role_policy}
    supplied = subject.get("artifacts") or []
    if not role_policy or len(supplied) != len(expected_roles) or {row.get("role") for row in supplied} != expected_roles:
        reasons.append("mismatched artifact: request differs from the checked Lean authority artifact roles")
    for artifact in supplied:
        selected_roles = [row for row in role_policy if row.get("role") == artifact.get("role")]
        if len(selected_roles) != 1 or artifact.get("digest") != artifacts.get(selected_roles[0].get("pipeline_artifact")):
            reasons.append(f"mismatched artifact: request {artifact.get('role')} differs from pipeline bytes")
    bound_source = (evidence or {}).get("source_claims") or {}
    bound_entries = bound_source.get("entries", [bound_source.get("entry")])
    entry, entry_reasons = source_entry(item)
    reasons += entry_reasons
    if not isinstance(bound_entries, list) or entry not in bound_entries:
        reasons.append("wrong subject: source request Entry differs from the admitted exports")
    if checks["outcome"] != "accepted":
        reasons.append("pipeline validation has not accepted this subject")
    receipt, assumptions, discharged = {}, [], []
    request_record = records.get(mapping.get("request_declaration"))
    receipt_record = records.get(mapping.get("receipt_declaration"))
    if receipt_record:
        reasons += receipt_join(mapping, records, modules, evidence)
        receipt, assumptions, discharged, audit_reasons = audit_receipt(
            receipt_record, records.get(mapping.get("request_declaration")), request, registry, records, modules)
        reasons += audit_reasons
        typed_subject = receipt.get("subject") or {}
        if typed_subject:
            for key, artifact_role in (("original_source", "source"),
                                       ("participant_source", "source"),
                                       ("participant_candidate", "constructed_candidate")):
                if typed_subject.get(key) != artifacts.get(artifact_role):
                    reasons.append(f"mismatched artifact: actual typed subject {key} differs from pipeline")
            if "producer_source" in typed_subject:
                for key, artifact_role in (("producer_source", "source"),
                                           ("producer_candidate", "constructed_candidate")):
                    if typed_subject.get(key) != artifacts.get(artifact_role):
                        reasons.append(f"mismatched artifact: actual typed subject {key} differs from pipeline")
            target_protocol = (request.get("target") or {}).get("protocol")
            if typed_subject.get("original_entry") != target_protocol:
                reasons.append("wrong target protocol: request differs from actual admitted snapshot")
            artifact_record = records.get(typed_subject.get("artifacts_head"))
            if not artifact_record or not module_attached(artifact_record["module"], modules):
                reasons.append("mismatched artifact: actual typed subject artifacts are outside the regenerated modules")
    else:
        reasons.append("no emitted typed receipt proves this request")
    dependencies, dependency_reasons = semantic_dependencies(receipt.get("dependencies") or [], records, environment)
    if receipt:
        reasons += dependency_reasons
    expected_dependency_digest = mapping.get("semantic_dependency_digest")
    if expected_dependency_digest is not None and expected_dependency_digest != dependencies["digest"]:
        reasons.append("stale semantic dependency digest: referenced definition bodies or environment changed")
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
    definitions = resolution.get("definitions")
    missing = (resolution.get("status") == "incomplete" and
               resolution.get("kind") in (None, "registered-undefined") and
               isinstance(definitions, list) and bool(definitions) and
               all(isinstance(item, str) and item.strip() for item in definitions))
    if missing and receipt:
        reasons.append("inconsistent resolution: a typed receipt accompanies missing definitions")
    # Incompleteness is a diagnostic, never positive evidence. A receipt and a
    # frontend missing-definition claim are inconsistent and cannot certify.
    state = "incomplete" if missing and not receipt else "open" if reasons else "certified"
    claim_kind = ((receipt.get("authority") or {}).get("kind") or
                  (((request_record or {}).get("detail") or {}).get("claim_data") or {}).get("claim_kind", "unresolved"))
    obligations[0]["status"] = state
    return {"request": request, "request_digest": digest, "attachment": item.get("attachment"),
            "property": (request.get("property") or {}).get("name"),
            "covered_endpoint": (receipt.get("stage_links") or {}).get("covered_endpoint") or subject.get("stage"),
            "requested_stage": subject.get("stage"), "statement": None,
            "claim_kind": claim_kind,
            "status": state, "outcome": "established" if state == "certified" else "unresolved",
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
            "honest_input_policy": receipt.get("honest_input_policy"),
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
    """Validate whole-Entry selection without selecting individual properties."""
    if not isinstance(scope, dict):
        return ["missing source claim Entry scope"]
    entries = scope.get("entries")
    if (not isinstance(entries, list) or not entries or
            any(not isinstance(entry, str) or not entry for entry in entries) or
            len(entries) != len(set(entries))):
        return ["invalid source claim Entry scope"]
    reasons = []
    if scope.get("selection") not in ("proof-entry", "explicit"):
        reasons.append("unknown source claim Entry selection")
    if entries != source.get("entries", [source.get("entry")]):
        reasons.append("source claim Entry scope differs from bound Entries")
    if scope.get("selection") == "proof-entry" and entries != [proof_entry]:
        reasons.append("default source claim scope differs from the manifest proof Entry")
    resolved = [source_entry(item) for item in source.get("claims", [])]
    for _, entry_reasons in resolved:
        reasons += entry_reasons
    if any(entry not in entries for entry, _ in resolved):
        reasons.append("source request Entry is outside the selected scope")
    if scope.get("selection") == "explicit":
        populated = {entry for entry, _ in resolved}
        for entry in entries:
            if entry not in populated:
                reasons.append(f"requested Entry has no matching source claims: {entry}")
    return reasons


def report_claim_scope(source, mappings, records, registry, modules, evidence, checks, reasons,
                       environment, environment_reasons, reused_records):
    """Use the same receipt audit for selected Entries and visible other trials."""
    reasons = list(reasons)
    claims = [requested_claim(item, mappings, records, registry, modules, evidence, checks,
                              reasons, environment, environment_reasons, reused_records)
              for item in source.get("claims", [])]
    nodes = [canonical((item.get("attachment") or {}).get("node")) for item in source.get("claims", [])]
    if len(nodes) != len(set(nodes)):
        reasons.append("duplicate bound source claim node")
    known_nodes = set(nodes)
    if any(canonical(mapping.get("node")) not in known_nodes for mapping in mappings):
        reasons.append("receipt association names a source node absent from this scope")
    author_claims = [item for item in claims if item["claim_kind"] == "author"]
    generic_claims = [item for item in claims if item["claim_kind"] == "generic"]
    security_claims = [item for item in claims if item["claim_kind"] not in {"author", "generic"}]
    outcome = ("established" if security_claims and not reasons and
               all(item["status"] == "certified" for item in security_claims) else "unresolved")
    state = ("no-claim" if not security_claims and source.get("format") == BOUND_CLAIMS_FORMAT else
             "certified" if outcome == "established" else
             "incomplete" if security_claims and all(item["status"] == "incomplete" for item in security_claims) else "open")
    return {"claims": claims, "security_claims": security_claims, "author_claims": author_claims,
            "generic_claims": generic_claims,
            "outcome": outcome, "status": state, "reasons": reasons}


def build(manifest_path, records, ledger=None, evidence_directory=None, reused_records=None):
    """Build reports only from source requests and checked emitted receipts."""
    manifest = load_manifest(manifest_path)
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
    selected_reasons = common_reasons + scope_reasons(source, scope, (manifest.get("entries") or {}).get("proof"))
    selected = report_claim_scope(source, (evidence or {}).get("claim_receipts") or [], records, registry,
                                  modules, evidence, checks, selected_reasons, environment,
                                  environment_reasons, reused_records)
    trials = []
    trial_entries = set()
    selected_entries = scope.get("entries", []) if isinstance(scope, dict) else []
    for trial in (evidence or {}).get("source_claim_trials") or []:
        entry = trial.get("entry")
        bound = {**source, "entry": entry, "entries": [entry], "claims": trial.get("claims") or []}
        trial_evidence = {**(evidence or {}), "source_claims": bound}
        trial_scope = {"entries": [entry], "selection": "explicit"}
        trial_reasons = scope_reasons(bound, trial_scope)
        if entry in trial_entries or entry in selected_entries:
            trial_reasons.append("duplicate or selected Entry in source claim trials")
        trial_entries.add(entry)
        mappings = trial.get("claim_receipts") or []
        available = all(records.get(mapping.get("request_declaration")) and
                        (not mapping.get("receipt_declaration") or records.get(mapping["receipt_declaration"]))
                        for mapping in mappings) and len(mappings) == len(bound["claims"])
        audited = report_claim_scope(bound, mappings, records, registry, modules, trial_evidence, checks,
                                     common_reasons + trial_reasons, environment, environment_reasons,
                                     reused_records)
        if not available:
            audited["status"], audited["outcome"] = "open", "unresolved"
            audited["reasons"].append("trial declaration records unavailable; trial is unaudited")
            for claim in audited["claims"]:
                claim["status"], claim["outcome"] = "open", "unresolved"
                claim["reasons"].append("trial declaration records unavailable; trial is unaudited")
        trials.append({"entry": entry, "source_claim_scope": trial_scope,
                       "bound_claims": bound["claims"], "claim_receipts": mappings,
                       "audit_status": "checked" if available else "unaudited", **audited})
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
