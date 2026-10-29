"""Generate artifact facts and source-bound typed Lean request clients.

Manifest configuration controls physical output/imports only. Property meanings
are computed by Lean registries; proof methods cannot change a request.
"""

from pathlib import Path
import sys
import textwrap

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common.lean_render import Refused, require, text  # noqa: E402
from bridges.pipeline import claim_render, source_claims  # noqa: E402


def module_name(subject, leaf):
    """Companion module next to the generated Claims module; namespace may differ."""
    module = subject.module_name("claims")
    require(module is not None, f"{subject.name}: no generated claims module")
    return module.rsplit(".", 1)[0] + "." + leaf


def paragraphs(*parts):
    """Documentation paragraphs, each wrapped at 80 columns."""
    return "\n\n".join(textwrap.fill(part, width=80) for part in parts)


def ty_term(ty):
    """The Lean `Ty` of a structured type tag."""
    tag = ty[0]
    if tag == "bool":
        return ".boolean"
    if tag == "index":
        return ".index"
    if tag in ("field", "vector", "group"):
        return f".{tag} {text(ty[1])}"
    raise Refused(f"unsupported published input type {ty}")


def statement_pattern(count):
    """The pattern of a statement of `count` published values, and their names."""
    variables = [f"value{index}" for index in range(count)]
    pattern = ".nil"
    for variable in reversed(variables):
        pattern = f".cons {variable} ({pattern})" if pattern != ".nil" else f".cons {variable} .nil"
    return pattern, variables


HEADER = """module

{imports}

@[expose] public section

/-! {doc} -/

"""


def artifacts_module(subject, entry, glue_namespace, executable_namespace, artifacts):
    """The subject's artifacts, compiled facts and lowering evidence."""
    namespace = subject.get("lean", "namespace")
    glue_module = subject.module_name("glue")
    imports = ["ZkcSecurity.Claims.Subject", "ZkcTools.ConstructionBindings.Admission",
               glue_module, subject.get("construction", "connection")]
    if executable_namespace:
        imports.append(subject.module_name("program"))
    entry_name = subject.get("entries", "proof")
    publics = ", ".join(ty_term(ty) for ty in entry.types)
    program = f"some {subject.module_name('program')}.validator" if executable_namespace else "none"
    doc = paragraphs(
        f"Generated artifacts of the subject `{subject.name}` and their checked facts. "
        "Regenerate with `lean/bridges/subject.py --write`.",
        f"The artifacts are the original export and the constructed validator of the compiled "
        f"`{entry_name}` Entry, the types of the inputs its policy publishes"
        + (" and the executable validator of the deployed program" if executable_namespace else "")
        + ". Every fact below is a generated per-Entry fact the kernel checked.")
    source = HEADER.format(imports="\n".join(f"public import {name}" for name in imports), doc=doc)
    source += f"""namespace {namespace}
open Zkc.Source Zkc.Source.Structured ZkcSecurity.Endpoint

set_option smartUnfolding false

/-- The artifacts of the compiled `{entry_name}` Entry. -/
def artifacts : Artifacts where
  original := {glue_namespace}.snapshot
  participant := {glue_namespace}.participant
  publics := [{publics}]
  program := {program}

set_option smartUnfolding true in
/-- The admitted original, the composed check and the checked selection. -/
def compiled : Compiled artifacts where
  imported := {glue_namespace}.imported
  compiled := {glue_namespace}.compiled
  selection := {glue_namespace}.selection
  selected := {glue_namespace}.selected
  checked := {glue_namespace}.selection_checked
  publics := by decide +kernel
  occurrences := by decide +kernel
  sourceConnection := some ⟨{glue_namespace}.sourceConnected⟩
"""
    pattern, variables = statement_pattern(len(entry.types))
    source += f"""
variable {{F G : Type}} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- Actual all-reply source transport, separate from static admission. -/
theorem sourceConnection : compiled.SourceConnection (F := F) (G := G) where
  equation challenge statement handle initial proof := by
    match statement with
    | {pattern} => exact {glue_namespace}.compiled_transform challenge {' '.join(variables)} handle initial proof
"""
    source += f'''
/-- Fresh physical attribution, checked against pipeline bytes by reporting.
Digest attribution is distinct from the kernel checked compiled facts above. -/
def sourceReference (stage : Zkc.Claims.Stage) : Zkc.Claims.SubjectRef :=
  ⟨{text(source_claims.digest(artifacts['original_text'].encode()))}, {text(artifacts['original'][3])}, stage,
    match stage with
    | .interactive => []
    | .compiledIdeal => [⟨"constructed-participant", {text(source_claims.digest(artifacts['export_text'].encode()))}⟩]
    | .executableBytes => [⟨"constructed-participant", {text(source_claims.digest(artifacts['export_text'].encode()))}⟩'''
    if artifacts.get("program") is not None:
        source += f', ⟨"verifier-program", {text(source_claims.digest(artifacts["program"]))}⟩'
    source += "]⟩\n"
    if artifacts.get("interactive") is not None:
        interactive = artifacts["interactive"]
        source += f'''
/-- Independently bound bytes for the separately admitted interactive protocol subject. -/
def interactiveReference : Zkc.Claims.SubjectRef :=
  ⟨{text(source_claims.digest(interactive['export_text'].encode()))},
    {text(interactive["snapshot"][3])}, .interactive, []⟩
'''
    sites = {}
    for claim in artifacts["source_claims"]["claims"]:
        for site in claim.get("resolved_sites", []):
            require(site["site"] not in sites or sites[site["site"]] == site,
                    "inconsistent source site attribution")
            sites[site["site"]] = site
    site_terms = []
    for site in sites.values():
        site_terms.append(f'''{{ label := {text(site['site'])}, native := {text(site['native'])},
      delivery := {text(site['delivery'])}, selected := by decide +kernel,
      request := compiled.context.request.getD (.draw ""), requestSelected := by decide +kernel }}''')
    source += "\n/-- Actual full construction occurrences selected by native source paths. -/\n"
    source += "def sourceSites : List (ZkcSecurity.Claims.Site compiled.context) :=\n  [" + ",\n   ".join(site_terms) + "]\n"
    source += f"\nend {namespace}\n"
    return source


def lowering_module(subject, entry, executable_namespace):
    """Byte transport is separate from the fixed artifact and source metadata."""
    namespace = subject.get("lean", "namespace")
    imports = [subject.module_name("artifacts"), executable_namespace]
    source = HEADER.format(imports="\n".join(f"public import {name}" for name in imports),
                           doc="Generated byte-lowering evidence. Regenerate with "
                               "`lean/bridges/subject.py --write`. Static admission and "
                               "actual byte-to-Domain transport are separate checked obligations.")
    pattern, variables = statement_pattern(len(entry.types))
    source += f"""namespace {namespace}
open ZkcSecurity.Endpoint

variable {{F G : Type}} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The exact admitted program and its actual byte-to-Domain transport. -/
def lowering : LoweringEvidence artifacts compiled F G where
  validator := {executable_namespace}.validator
  program := rfl
  lowered := {executable_namespace}.lowered
  accepted := {executable_namespace}.accepted
  prepared := {executable_namespace}.prepared
  sorted := {executable_namespace}.helpersSorted
  admits statement := by
    match statement with
    | {pattern} => exact {executable_namespace}.admitted {' '.join(variables)}
  pruning challenge codec budget binding statement initial bytes := by
    match statement with
    | {pattern} => exact {executable_namespace}.domain_prunes challenge codec budget binding {' '.join(variables)} initial bytes

end {namespace}
"""
    return source


def request_commands(namespace, bound, library="Registration.library"):
    """Serialize fixed requests and invoke Lean's checked receipt constructor.

    The registration can be generated by Lean or supplied by an author. This
    renderer has no property, theorem-specialization or arithmetic logic.
    """
    source = f"namespace {namespace}\nopen Zkc.Claims ZkcSecurity.Tools.ClaimConstruction\n\n"
    source += "set_option maxRecDepth 8192\nset_option maxHeartbeats 2000000\n\n"
    for index, claim in enumerate(bound["claims"]):
        prefix = f"request{index}"
        source += f"/-- Exact source request; attachment and method are separate. -/\ndef {prefix}Data : Wire.Request :=\n"
        source += claim_render.request(claim["request"]) + "\n\n"
        method = "none" if claim["method"] is None else "some " + claim_render.application(claim["method"])
        source += f"def {prefix}Method : Option Wire.Application := {method}\n\n"
        source += f"claim_request {prefix}Data using {library} method {prefix}Method\n\n"
    source += f"end {namespace}\n"
    return source


def claims_module(subject, bound):
    """Only data and generic Lean construction calls; never print a Prop."""
    namespace = subject.get("lean", "namespace")
    require(namespace, f"{subject.name}: source receipts need lean.namespace")
    imports = ["ZkcSecurity.Tools.ClaimConstruction", *subject.get("lean", "imports", [])]
    source = HEADER.format(imports="\n".join(f"public import {name}" for name in dict.fromkeys(imports))
                           + "\n" + "\n".join(f"public meta import {name}" for name in subject.get("lean", "imports", [])),
                           doc="Generated source requests and typed receipts. Regenerate with "
                               "`lean/bridges/subject.py --write`. Typed library exports fix the "
                               "subject and registry; source requests select the property and method.")
    return source + request_commands(namespace, bound, subject.get("lean", "library", "Registration.library"))
