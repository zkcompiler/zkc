"""Render a subject's generated modules in the security integration.

For a manifest with a `[claims]` namespace, two modules are generated there:

- the artifacts module: the subject's `Artifacts` (the original export, the
  constructed validator, the published input types read from the export, and
  the executable validator when the subject has one), its `Compiled` facts and,
  for an executable subject, its `LoweringEvidence`, every field one of the
  generated per-Entry facts the kernel checked;
- the claims module: the evidence of the claim, built by the subject's family
  constructor, and the claim itself, the registered endpoint applied to that
  evidence and stated at the subject's artifacts, its contract and its regime,
  so that the kernel checks that the evidence has the type the manifest claims.

The family constructor, the contract and the model equations are hand-written
in the subject's `Evidence` and `Contract` modules; nothing here is trusted:
every value becomes a statement the kernel checks when the modules are built.
"""

from pathlib import Path
import sys
import textwrap

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common.lean_render import Refused, require, text  # noqa: E402

SECURITY = Path("lean/integrations/arklib")

# The registered endpoint of each claim: its theorem's short name, the property
# definition it proves and the contract declaration the property is stated at.
ENDPOINTS = {
    ("ideal-meaning", "soundness", "fixed"): ("fixed_soundness", "FixedSoundness"),
    ("ideal-meaning", "soundness", "adaptive"): ("adaptive_soundness", "AdaptiveSoundness"),
    ("executable-bytes", "soundness", "fixed"): ("fixed_soundness_bytes", "FixedSoundnessBytes"),
    ("executable-bytes", "soundness", "adaptive"): ("adaptive_soundness_bytes", "AdaptiveSoundnessBytes"),
    ("ideal-meaning", "knowledge-soundness", "fixed"): ("knowledge_soundness", "KnowledgeSoundness"),
    ("executable-bytes", "knowledge-soundness", "fixed"): ("knowledge_soundness_bytes", "KnowledgeSoundnessBytes"),
}
CONTRACTS = {"soundness": "falseStatement", "knowledge-soundness": "holds"}
REGIMES = {"exact-uniform challenges": "Regime.exact F"}
SEMANTICS = {"ideal-meaning": ".idealMeaning", "executable-bytes": ".executableBytes"}
# The section variables of a claims module: the instances the endpoints of each
# property take, and no others, so that no claim carries an unused premise.
VARIABLES = {
    "soundness": "variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]\n"
                 "  [AddCommGroup G] [Module F G] [DecidableEq G]",
    "knowledge-soundness": "variable {F G : Type} [Field F] [Fintype F] [DecidableEq F] [Inhabited F] "
                           "[SampleableType F]\n  [AddCommGroup G] [Module F G] [DecidableEq G] [SampleableType G]",
}


def names(manifest):
    """The declarations a subject's claim consists of, all derived from its claims
    namespace, so the generated application and the report name the same
    declarations."""
    claims = manifest.get("claims") or {}
    namespace = claims.get("namespace")
    if namespace is None:
        return {}
    properties = claims.get("properties") or []
    prop = properties[0] if len(properties) == 1 else None
    endpoint = ENDPOINTS.get((claims.get("endpoint"), prop, claims.get("statement")))
    return {"namespace": namespace,
            "artifacts": f"{namespace}.artifacts",
            "contract": f"{namespace}.Contract.{CONTRACTS.get(prop, 'falseStatement')}",
            "instance": f"{namespace}.evidence",
            "application": f"{namespace}.{endpoint[0]}" if endpoint else None}


def module_path(namespace, leaf):
    return SECURITY.joinpath(*namespace.split("."), f"{leaf}.lean")


def module_name(namespace, leaf):
    return f"{namespace}.{leaf}"


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


def artifacts_module(subject, entry, glue_namespace, executable_namespace):
    """The subject's artifacts, compiled facts and lowering evidence."""
    namespace = subject.get("claims", "namespace")
    glue_module = subject.module_name("glue")
    imports = ["ZkcSecurity.Endpoint.Evidence", glue_module]
    if executable_namespace:
        imports.append(executable_namespace)
    entry_name = subject.get("entries", "proof")
    publics = ", ".join(ty_term(ty) for ty in entry.types)
    program = f"some {executable_namespace}.validator" if executable_namespace else "none"
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
"""
    if executable_namespace:
        pattern, variables = statement_pattern(len(entry.types))
        source += f"""
variable {{F G : Type}} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The executable validator, accepted by the lowering rule. -/
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
"""
    source += f"\nend {namespace}\n"
    return source


def application_text(subject, prop, endpoint, statement, evidence_name, regime, claimed):
    """One application: the evidence the family constructor builds at an endpoint
    and a statement form, and the registered endpoint applied to it."""
    theorem, property_name = ENDPOINTS[(endpoint, prop, statement)]
    construction = subject.get("family", "construction")
    executable = endpoint == "executable-bytes"
    lowering = "lowering" if executable else "PUnit.unit"
    stated = ["(art := artifacts)"]
    adaptive = statement == "adaptive"
    if prop == "soundness":
        stated += ["(claim := Contract.falseStatement)", f"(regime := {regime})"]
        binding = "⟨application⟩" if adaptive else "PUnit.unit"
        value = f"{construction} (F := F) (G := G) {SEMANTICS[endpoint]} .{statement} {binding} {lowering}"
        description = (f"ordinary soundness of {'program bytes' if executable else 'the ideal meaning'} for "
                       f"{statement} statements")
    else:
        stated += ["(holds := Contract.holds)"]
        value = f"{construction} (F := F) (G := G) {SEMANTICS[endpoint]} {lowering}"
        description = f"knowledge soundness of {'program bytes' if executable else 'the ideal meaning'} for fixed statements"
    parameter = " (application : String)" if adaptive else ""
    argument = " application" if adaptive else ""
    evidence_doc = textwrap.fill(f"The evidence of {description}{' in an application context' if adaptive else ''}.",
                                 width=76)
    lead = "The claim" if claimed else "Also covered"
    claim_doc = textwrap.fill(f"{lead}: {description}, at the subject's artifacts and contract.", width=76)
    return description, f"""/-- {evidence_doc} -/
noncomputable def {evidence_name}{parameter} :=
  {value}

/-- {claim_doc} -/
theorem {theorem}{parameter} :
    {property_name} {' '.join(stated)}
      ({evidence_name} (F := F) (G := G){argument}) :=
  ZkcSecurity.Endpoint.{theorem} ({evidence_name}{argument})
"""


def evidence_name(endpoint, statement, prop):
    """The name of the evidence of an endpoint and statement form other than the
    manifest's claim."""
    form = "fixed" if prop == "soundness" and statement == "fixed" else (
        "adaptive" if prop == "soundness" else "")
    semantics = "Bytes" if endpoint == "executable-bytes" else "Ideal"
    name = f"{form}{semantics}Evidence"
    return name[0].lower() + name[1:]


def claims_module(subject):
    """The evidence of the claim and the claim: the registered endpoint applied to
    the evidence, at the subject's artifacts, contract and regime. The family
    constructor's evidence at every other endpoint and statement form the
    subject covers is applied too: the ideal meaning, program bytes when the
    subject has an executable program, and both statement forms for ordinary
    soundness."""
    claims = subject.table("claims")
    namespace = claims["namespace"]
    properties = claims.get("properties") or []
    require(len(properties) == 1, f"{subject.name}: a claims namespace needs exactly one property")
    prop = properties[0]
    endpoint, statement = claims.get("endpoint"), claims.get("statement")
    key = (endpoint, prop, statement)
    require(key in ENDPOINTS, f"{subject.name}: no registered endpoint for {key}")
    require(subject.get("family", "construction"), f"{subject.name}: the manifest names no family construction")
    require(prop == "soundness" or statement == "fixed",
            f"{subject.name}: knowledge soundness is registered for fixed statements only")
    regime = None
    if prop == "soundness":
        regime = REGIMES.get(claims.get("regime"))
        require(regime is not None, f"{subject.name}: unsupported regime {claims.get('regime')!r}")
    adaptive = statement == "adaptive"
    description, claimed = application_text(subject, prop, endpoint, statement, "evidence", regime, True)
    endpoints = ["ideal-meaning"] + (["executable-bytes"] if subject.get("profiles", "executable") else [])
    forms = ["fixed", "adaptive"] if prop == "soundness" else ["fixed"]
    covered = [application_text(subject, prop, other, form, evidence_name(other, form, prop), regime, False)[1]
               for other in endpoints for form in forms if (other, form) != (endpoint, statement)]
    contract = "Contract.falseStatement" if prop == "soundness" else "Contract.holds"
    doc = paragraphs(
        f"Generated claims of the subject `{subject.name}`. Regenerate with `lean/bridges/subject.py --write`.",
        f"The manifest claims {description}. The claim is the registered endpoint applied to the subject's "
        "evidence" + (" in every bound application context" if adaptive else "")
        + f", stated at the subject's artifacts, its contract (`{contract}`)"
        + (" and its regime" if prop == "soundness" else "")
        + ": the kernel checks that the evidence has that type.",
        "The family constructor's evidence at every other endpoint and statement form the subject covers is "
        "applied below the claim, at the same artifacts"
        + (", contract and regime." if prop == "soundness" else " and contract."))
    imports = ["ZkcSecurity.Endpoint.Soundness" if prop == "soundness" else "ZkcSecurity.Endpoint.Knowledge",
               subject.module_name("claims").rsplit(".", 1)[0] + ".Evidence"]
    source = HEADER.format(imports="\n".join(f"public import {name}" for name in imports), doc=doc)
    source += f"""namespace {namespace}
open ZkcSecurity.Endpoint

set_option linter.unusedSectionVars false

{VARIABLES[prop]}

{claimed}"""
    if covered:
        source += "\n/-! ## Other covered endpoints and statement forms -/\n\n" + "\n".join(covered)
    source += f"\nend {namespace}\n"
    return source
