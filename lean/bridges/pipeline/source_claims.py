"""Bind native claim exports to the exact artifacts sent to Lean.

This module does not resolve registered meanings or certify claims. It records
byte identities and proposals for the typed resolver; the kernel must still
check the retained clause, selector, sites, model and proof. Request hashes are
cache/audit keys, never a substitute for a receipt's checked proof type.
"""

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common.lean_render import Refused, require  # noqa: E402


def digest(data):
    return "sha256:" + hashlib.sha256(data).hexdigest()


def canonical(value):
    """Canonical audit encoding, independent of JSON object order and spacing."""
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True,
                      allow_nan=False).encode("ascii")


def decode(text):
    """Never let JSON duplicate keys or non-finite numbers hide a changed claim."""
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, f"duplicate source-claim field {key}")
            result[key] = value
        return result

    def invalid(value):
        raise Refused(f"non-finite source-claim number {value}")

    try:
        return json.loads(text, object_pairs_hook=unique, parse_constant=invalid)
    except (ValueError, TypeError) as error:
        raise Refused(f"malformed source-claim JSON: {error}") from error


def qualify_site(parent, site):
    """Mirror Structured.qualifyProtocolSite; compare against actual policy below."""
    return site if parent is None else f"apply_{len(parent.encode('utf-8'))}_{parent}_{site}"


def resolve_sites(original, policy, bindings):
    """Resolve complete native paths through the original protocol call tree.

    Repeats preserve one static occurrence. Calls extend the full occurrence;
    duplicate paths and non-query leaves fail closed. This is frontend
    attribution, additionally checked by typed Site membership in Lean.
    """
    definitions = {item[1]: item for item in original[7] if item[0] == "function"}
    found = {}

    def block(value, path, parent, active):
        require(value[0] == "block", "site attribution needs a structured block")
        for operation, _operands, _results, regions, site in value[1]:
            if operation[0] == "draw":
                found.setdefault(tuple([*path, site]), []).append(qualify_site(parent, site))
            if operation[0] == "protocol_apply":
                callee = operation[1]
                require(callee in definitions and callee not in active, "missing or recursive site call")
                block(definitions[callee][9], [*path, site], qualify_site(parent, site), {*active, callee})
            for region in regions:
                block(region[2], path, parent, active)

    entry = original[3]
    require(entry in definitions, "site attribution lacks original Entry")
    block(definitions[entry][9], [], None, {entry})
    draws = policy[8]
    result = []
    labels, occurrences = set(), set()
    for binding in bindings:
        require(isinstance(binding, dict) and set(binding) == {"site", "native_path", "source"},
                "unexpected source site binding fields")
        label, path = binding["site"], binding["native_path"]
        require(isinstance(label, str) and isinstance(path, list) and path
                and all(isinstance(part, str) and part for part in path), "malformed native site path")
        matches = found.get(tuple(path), [])
        require(len(matches) == 1, f"site {label}: native path does not select one query occurrence")
        selected = [pair for pair in draws if pair[0] == matches[0]]
        require(len(selected) == 1, f"site {label}: query is not one constructed challenge occurrence")
        native, delivery = selected[0]
        require(label not in labels and native not in occurrences, "duplicate source construction occurrence")
        labels.add(label)
        occurrences.add(native)
        result.append(dict(site=label, native_path=path, native=native, delivery=delivery,
                           source=deepcopy(binding["source"]), attribution="trusted-frontend-checked-policy"))
    return result


def bind_export(export, *, entry, source, interface_text, original_text,
                participant_text=None, program=None):
    """Return bound wire requests; every result still requires typed resolution.

    Only semantic stage artifacts enter SubjectRef. The native interface and
    source attachment are checked separately: renaming a claim label can change
    a source capture without changing the admitted protocol or request.
    """
    require(isinstance(export, dict), "source claims must be an object")
    require(set(export) == {"format", "entry", "registry_resolution", "admission", "claims", "proposals", "seams"},
            "unexpected source-claim export fields")
    require(export["format"] == "zkc.source-claims/0", "unsupported source-claim format")
    require(export["registry_resolution"] == "deferred-to-lean", "native claims cannot certify a meaning")
    require(export["entry"] == entry, "source claims name another Entry")
    admission = export["admission"]
    require(isinstance(admission, dict), "source claims omit admission")
    require(set(admission) == {"format", "original_sha256", "interface_sha256", "protocol_symbol",
                               "capture", "installation"},
            "unexpected source-claim admission fields")
    for field in ("capture", "installation"):
        require(isinstance(admission[field], str), f"source-claim {field} must be a string")
    require(admission.get("original_sha256") == digest(source), "source claims bind another original")
    # The CLI appends one record terminator; exportSourceClaims hashes the
    # interface payload, before that terminator. Preserve all other bytes.
    require(admission.get("interface_sha256") == digest(interface_text.removesuffix("\n").encode()),
            "source claims bind another native interface")
    interface = decode(interface_text)
    require(isinstance(interface, dict) and interface.get("format") == "zkc.language-interface/0",
            "source claims lack a native entry interface")
    require(interface.get("entry") == entry, "native interface names another Entry")
    require(interface.get("original") == admission["original_sha256"].removeprefix("sha256:"),
            "native interface binds another original")
    original = decode(original_text)
    require(isinstance(original, list) and len(original) >= 4, "malformed admitted snapshot export")
    require(admission.get("format") == original[0] == "zkc.structured-source/0",
            "source claims bind another snapshot format")
    require(original[2] == admission["original_sha256"], "admitted snapshot binds another original")
    require(original[3] == admission.get("protocol_symbol"), "source claims bind another protocol")
    require(interface.get("protocol") == original[3],
            "native interface maps Entry to another protocol")
    for field in ("proposals", "seams"):
        require(isinstance(export[field], list), f"component {field} must be an array")
    require(isinstance(export["claims"], list), "source claims must be an array")
    results = []
    attachments = set()
    for item in export["claims"]:
        require(isinstance(item, dict) and set(item) == {"request", "attachment", "method", "site_bindings"},
                "unexpected source-claim record fields")
        request = deepcopy(item["request"])
        require(isinstance(request, dict), "source claim request must be an object")
        subject = request.get("subject")
        require(isinstance(subject, dict) and set(subject) == {"entry", "stage"},
                "unexpected wire subject fields")
        require(subject["entry"] == entry, "claim request names another Entry")
        stage = subject["stage"]
        require(stage in {"interactive", "compiled-ideal", "executable-bytes"}, "unknown claim stage")
        target = request.get("target")
        require(isinstance(target, dict) and target.get("protocol") == original[3],
                "claim target names another protocol")
        artifacts = []
        if stage != "interactive":
            require(participant_text is not None, "compiled request lacks its constructed participant")
            artifacts.append({"role": "constructed-participant", "digest": digest(participant_text.encode())})
        if stage == "executable-bytes":
            require(program is not None, "byte request lacks its executable program")
            artifacts.append({"role": "verifier-program", "digest": digest(program)})
        # A source proof alias names a configured deployment. The admitted IR
        # names its protocol by a symbol. Keep the alias for author-facing scope,
        # and resolve the semantic subject through the exact checked interface.
        request["subject"] = {"unit": digest(original_text.encode()), "entry": original[3],
                              "stage": stage, "artifacts": artifacts}
        attachment = deepcopy(item["attachment"])
        require(isinstance(attachment, dict), "claim attachment must be an object")
        key = canonical(attachment.get("node"))
        require(key not in attachments, "duplicate claim source node")
        attachments.add(key)
        results.append({"request": request, "request_digest": digest(canonical(request)),
                        "source_entry": entry,
                        "entry_association": {"source_entry": entry, "protocol": original[3],
                            "interface_digest": admission["interface_sha256"],
                            "attribution": "trusted-frontend-checked-interface"},
                        "attachment": attachment, "method": deepcopy(item["method"]),
                        "site_bindings": deepcopy(item["site_bindings"]),
                        "resolution": "pending-lean", "source_scope": "ir-relative"})
    return {"format": "zkc.bound-source-claims/0", "entry": entry,
            "native_export_digest": digest(canonical(export)), "claims": results,
            "proposals": deepcopy(export["proposals"]), "seams": deepcopy(export["seams"]),
            "checked_links": ["native-original", "native-interface", "source-entry-association",
                              "snapshot-source", "stage-artifacts"],
            "required_links": ["typed-request-resolution", "source.correspondence",
                *(["typed-component-association"]
                  if export["proposals"] or export["seams"] else [])],
            # Component laws belong to this proof method. A direct proof of the
            # fixed request meaning need not use the component method at all.
            "method_obligations": ([{"method": "component-composition",
                "required": ["component-law-obligations"]}]
                if export["proposals"] or export["seams"] else [])}
