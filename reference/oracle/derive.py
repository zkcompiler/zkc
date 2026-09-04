"""The structural and typing half of a derivation.

A judgment has five parts.  Four of them — the subject it is about, the notion
it is indexed by, the resources it quantifies over, and the qualitative
obligations it inherited — are determined by the sealed protocol, the selected
bindings, and the plan.  The fifth, the bound, is arithmetic.

This module produces the four.  It resolves the site against the artifact and
constructs the conclusion subject the kernel would, matches each premise
against the subject relation its port declares, checks the index and result
schema agree, and accumulates hypotheses in the exact order an application
inherits them. It stops where the bound begins: a second implementation of the
same arithmetic could share a common-mode misreading with the first, so numeric
bounds are cross-checked by re-derivation from the cited source instead of by a
second evaluator.

The two implementations agree on the artifact — that is what the encoding
parity suites establish — so a judgment about it is a statement both can make.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction
from typing import Any, NamedTuple

from . import model
from .canonical import Refusal, canon_json
from .signature import (
    QUANTIFICATIONS,
    Binding,
    ExactRef,
    Rule,
    SecurityIndex,
    Signature,
)

# Sorts the sealed protocol supplies.  A request that asserts one is asking a
# question about a different artifact.
PROTOCOL_SORTS = frozenset(
    {"reduction_contract", "path_transition", "round_adjacency", "subject"})


# --------------------------------------------------------------------------
# The sealed view: what a judgment may read about the protocol.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ClaimRef:
    claim_index: int
    descriptor_digest: str

    def document(self) -> dict[str, Any]:
        return {"claim_index": self.claim_index,
                "descriptor_digest": self.descriptor_digest}


@dataclass(frozen=True)
class SealedReduction:
    transformer_position: int
    contract_ref: ExactRef
    ordered_inputs: tuple[ClaimRef, ...]
    ordered_outputs: tuple[ClaimRef, ...]


@dataclass(frozen=True)
class SealedView:
    artifact_id: str
    claims: tuple[ClaimRef, ...]
    reductions: dict[int, SealedReduction]
    #: Each transformer's body extent and centrality, projected rather than
    #: judged.  No judgment here reads it; the rule class that will is the one
    #: composing two claims in parallel, which does not ship yet.
    bodies: tuple[TransformerBody, ...] = ()


class TransformerBody(NamedTuple):
    """One transformer's body extent and whether it commutes."""

    instance: str
    begin: int
    end: int
    central: bool


def transformer_bodies(
        protocol: dict[str, Any],
        vocabulary: model.ProtocolVocabulary) -> list[TransformerBody]:
    """Each transformer's body extent and centrality (kernel.md section 4).

    The body is what a transformer writes and what it reads: the messages its
    contract's rounds declare, together with the challenges those rounds
    sample.  A message is an absorb and a challenge is a squeeze, and a
    central transformer is one with neither, so counting messages alone would
    track write-write interference and miss read-write interference -- which
    is what BIND depends on.

    Sorted by (begin, end, instance).  The instance is part of the key because
    the other implementation sorts an unstable sort by the same triple, and
    without it two transformers with equal bodies would be ordered differently
    between the two.
    """

    extents: dict[str, list[Any]] = {}

    def observe(instance: str, position: int, central: bool) -> None:
        extent = extents.get(instance)
        if extent is None:
            extents[instance] = [position, position, central]
            return
        extent[0] = min(extent[0], position)
        extent[1] = max(extent[1], position)
        if not central:
            extent[2] = False

    for position, event in enumerate(protocol["events"]):
        # A role is filled by whatever carries the material, so the body
        # extent covers both seats: two protocols differing only in which
        # seat fills a role would otherwise get different extents. A public
        # binding always absorbs.
        if isinstance(event, model.Slot) and event.membership is not None:
            observe(event.membership[0], position, not event.absorbed)
        elif isinstance(event, model.Bind) and event.membership is not None:
            observe(event.membership[0], position, False)

    positions = {event.label: index
                 for index, event in enumerate(protocol["events"])}
    for reduce in protocol.get("reduces", ()):
        contract = vocabulary.reductions.get(reduce.contract)
        if not contract:
            continue
        dep_slots = contract.get("dep_slots") or []
        # Sampling a challenge is what makes a transformer non-central.  No
        # admitted contract can avoid one -- a reduction contract needs a
        # non-empty round list -- so this is unconditional in practice, and is
        # written as the kernel's predicate rather than as the constant it
        # currently evaluates to.
        #
        # The challenges are the ones the contract's *rounds* use, resolved
        # role to dependency slot to operand, which is how the other leg
        # reaches them. Reading every challenge-shaped dependency instead
        # would agree only while no contract declares one a round does not
        # use, and the two implementations would then be running different
        # rules over the same artifact.
        for round_entry in contract.get("rounds") or []:
            role = (round_entry.get("challenge_use") or {}).get("role")
            slots = [index for index, slot in enumerate(dep_slots)
                     if slot.get("role") == role]
            if len(slots) != 1 or slots[0] >= len(reduce.deps):
                raise Refusal(
                    f"reduction {reduce.label!r} has no single dependency "
                    f"operand for challenge role {role!r}"
                )
            index = positions.get(reduce.deps[slots[0]])
            if index is None or not isinstance(
                    protocol["events"][index], model.Chal):
                raise Refusal(
                    f"reduction {reduce.label!r} round dependency is not a "
                    "fresh challenge event"
                )
            observe(reduce.label, index, False)

    return sorted(
        (TransformerBody(name, extent[0], extent[1], extent[2])
         for name, extent in extents.items()),
        key=lambda body: (body.begin, body.end, body.instance),
    )


def group_transformer_bodies(
        bodies: list[TransformerBody]) -> list[list[TransformerBody]]:
    """Group bodies by transitive overlap.

    A group whose members are all but one central decomposes per-transformer;
    any other interleaved group does not.  This answers a question and refuses
    nothing: the answer is the precondition of composing two claims in
    parallel and of nothing else.  Accumulating a round-by-round bound over a
    transcript is a union bound over rounds, which interleaving does not
    threaten, because every challenge stays fresh given the prefix the duplex
    absorbed.
    """

    if not bodies:
        return []
    groups: list[list[TransformerBody]] = []
    start = 0
    end = bodies[0].end
    for index in range(1, len(bodies)):
        # Containment is overlap, and the group runs to the furthest end any
        # member reaches: a shorter body inside it must not pull the end back.
        if bodies[index].begin <= end:
            end = max(end, bodies[index].end)
            continue
        groups.append(list(bodies[start:index]))
        start = index
        end = bodies[index].end
    groups.append(list(bodies[start:]))
    return groups


def sealed_view(protocol: dict[str, Any],
                vocabulary: model.ProtocolVocabulary) -> SealedView:
    """Project the theorem-independent structure a judgment may read.

    The artifact carries no citation, so nothing here names a theorem: a
    claim, the transformer that produced it, and the exact contract that
    transformer was checked against.  Which semantics applies to that
    structure is the selected binding's business.
    """
    model.validate_protocol(protocol, vocabulary)
    # A site names a CANONICAL position, not an authored one: sources are
    # ordered by profile and canonical anchors, and reduces topologically.
    # Reading the authored order here would agree with the carrier only when
    # the two happen to coincide, which is why the same normalization that
    # computes identity computes these positions.
    sources, reduces, claim_pos, transformer_pos = (
        model._normalized_transformers(protocol))

    descriptor_of: dict[str, str] = {
        entry.label: model.claim_descriptor_digest(entry.profile, entry.anchors)
        for entry in sources}
    for reduce in reduces:
        for (label, profile), anchors in zip(reduce.produced, reduce.anchors):
            descriptor_of[label] = model.claim_descriptor_digest(profile,
                                                                 anchors)

    ref_of: dict[str, ClaimRef] = {}
    by_position: dict[int, ClaimRef] = {}
    for label, position in claim_pos.items():
        ref = ClaimRef(position, descriptor_of[label])
        ref_of[label] = ref
        by_position[position] = ref
    if sorted(by_position) != list(range(len(claim_pos))):
        raise Refusal("canonical claim positions are not contiguous")
    claims = [by_position[position] for position in range(len(claim_pos))]

    reductions: dict[int, SealedReduction] = {}
    for reduce in reduces:
        revision = vocabulary.reduction_digests.get(reduce.contract)
        if revision is None:
            raise Refusal(f"reduction '{reduce.label}' names an unloaded "
                          f"contract '{reduce.contract}'")
        position = transformer_pos[reduce.label]
        reductions[position] = SealedReduction(
            position, ExactRef(reduce.contract, revision),
            tuple(ref_of[label] for label in reduce.consumed),
            tuple(ref_of[label] for label, _ in reduce.produced))

    return SealedView(
        model.compute_id(protocol, vocabulary), tuple(claims), reductions,
        tuple(transformer_bodies(protocol, vocabulary)),
    )


# --------------------------------------------------------------------------
# Subjects and sites.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class ProtocolClaim:
    artifact_id: str
    claim: ClaimRef

    def document(self) -> dict[str, Any]:
        return {"artifact_id": self.artifact_id, "claim": self.claim.document(),
                "kind": "protocol_claim"}


@dataclass(frozen=True)
class ConsumedClaimVector:
    artifact_id: str
    consumer: ClaimRef
    ordered_sources: tuple[ClaimRef, ...]

    def document(self) -> dict[str, Any]:
        return {"artifact_id": self.artifact_id,
                "consumer": self.consumer.document(),
                "kind": "consumed_claim_vector",
                "ordered_sources": [claim.document()
                                    for claim in self.ordered_sources]}


@dataclass(frozen=True)
class AssumedJudgment:
    """A judgment a request asserts rather than derives.

    Only three parts are readable from a request — the subject, the index, and
    the result — because everything else about a judgment is produced by
    evaluation, and accepting more here would let a request assert a
    conclusion.  The result is validated and then not represented: this module
    produces the skeleton, and the skeleton carries no bound, so the result is
    dropped from every judgment including the ones nested inside a hypothesis.
    """

    subject: Any  # ProtocolClaim | ConsumedClaimVector
    index: SecurityIndex

    def document(self) -> dict[str, Any]:
        return {"hypotheses": [], "index": self.index.document(),
                "resource_variables": [], "subject": self.subject.document()}


@dataclass(frozen=True)
class AssumedJudgmentHolds:
    """The marker an assumption leaves on its own conclusion.

    Only evaluation synthesizes it, which is why a request cannot supply one:
    the judgment reader admits no hypotheses at all.  It travels with every
    conclusion that inherited the assumption, so a reader of the witness can
    see which parts of the derivation were asserted.
    """

    judgment: AssumedJudgment

    def document(self) -> dict[str, Any]:
        return {"judgment": self.judgment.document(),
                "kind": "assumed_judgment"}


@dataclass(frozen=True)
class Site:
    kind: str  # reduction | path
    artifact_id: str
    claim: ClaimRef | None = None            # path
    owner_claim: ClaimRef | None = None      # reduction
    transformer_position: int = 0
    output_index: int = 0

    def document(self) -> dict[str, Any]:
        if self.kind == "path":
            if self.claim is None:
                raise Refusal("a path occurrence names no claim")
            return {"artifact_id": self.artifact_id,
                    "claim": self.claim.document(), "kind": "path"}
        if self.owner_claim is None:
            raise Refusal("a reduction occurrence names no owner claim")
        return {"artifact_id": self.artifact_id,
                "kind": "reduction",
                "output_index": self.output_index,
                "owner_claim": self.owner_claim.document(),
                "transformer_position": self.transformer_position}


def subject_of(view: SealedView, site: Site) -> ProtocolClaim:
    """The conclusion subject is constructed here, never supplied.

    A binding's subject schema validates what this produces; it cannot
    replace it, which is why a direct application always concludes about an
    exact protocol claim.
    """
    if site.artifact_id != view.artifact_id:
        raise Refusal("the site names a different artifact")
    if site.kind == "path":
        return ProtocolClaim(view.artifact_id, _exact(view, site.claim))
    reduction = view.reductions.get(site.transformer_position)
    if reduction is None:
        raise Refusal(f"no reduction occupies transformer position "
                      f"{site.transformer_position}")
    if _exact(view, site.owner_claim) not in reduction.ordered_outputs:
        raise Refusal("the site's owner claim is not produced by that "
                      "reduction")
    if site.output_index >= len(reduction.ordered_outputs):
        raise Refusal("the site names an output the reduction does not have")
    return ProtocolClaim(view.artifact_id,
                         reduction.ordered_outputs[site.output_index])


def _exact(view: SealedView, claim: ClaimRef | None) -> ClaimRef:
    if claim is None:
        raise Refusal("a site names no claim")
    for candidate in view.claims:
        if candidate == claim:
            return candidate
    raise Refusal(f"claim {claim.claim_index} with digest "
                  f"{claim.descriptor_digest} is not in this artifact")


# --------------------------------------------------------------------------
# The request.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Apply:
    site: Site
    binding: str
    premises: dict[str, Any]


@dataclass(frozen=True)
class Assume:
    """A premise the request asserts instead of deriving.

    A leaf, always: an assumption has no children, and the conclusion it offers
    is the judgment it asserts plus a marker recording that it was asserted.
    The marker is what keeps the assumption visible in the witness rather than
    silently indistinguishable from a derived premise
    (`docs/spec/soundness.md`).
    """

    asserted: "AssumedJudgment"


@dataclass(frozen=True)
class Request:
    selected_bindings: tuple[str, ...]
    resolved_parameters: dict[str, dict[str, tuple[str, Any]]]
    target_subject: ProtocolClaim
    target_index: SecurityIndex
    target_resources: tuple[tuple[str, str], ...]
    plan: Any  # Apply at the root; an Assume there is refused when derived


def _closed(node: Any, where: str, keys: tuple[str, ...]) -> dict[str, Any]:
    if not isinstance(node, dict):
        raise Refusal(f"{where} is not an object")
    for key in sorted(node):
        if key not in keys:
            raise Refusal(f"{where} carries an unknown field {key!r}")
    for key in keys:
        if key not in node:
            raise Refusal(f"{where} is missing {key!r}")
    return node


def _claim(node: Any, where: str) -> ClaimRef:
    entry = _closed(node, where, ("claim_index", "descriptor_digest"))
    return ClaimRef(entry["claim_index"], entry["descriptor_digest"])


def _site(node: Any, where: str) -> Site:
    if not isinstance(node, dict) or node.get("kind") not in ("path",
                                                              "reduction"):
        raise Refusal(f"{where} names no admitted occurrence")
    if node["kind"] == "path":
        entry = _closed(node, where, ("kind", "artifact_id", "claim"))
        return Site("path", entry["artifact_id"],
                    claim=_claim(entry["claim"], f"{where} claim"))
    entry = _closed(node, where, ("kind", "artifact_id", "owner_claim",
                                  "transformer_position", "output_index"))
    return Site("reduction", entry["artifact_id"],
                owner_claim=_claim(entry["owner_claim"], f"{where} owner"),
                transformer_position=entry["transformer_position"],
                output_index=entry["output_index"])


def _resolved_value(node: Any, where: str) -> tuple[str, Any]:
    entry = _closed(node, where, ("sort", "value"))
    sort = entry["sort"]
    if sort in PROTOCOL_SORTS:
        raise Refusal(f"{where} supplies a {sort}, which the sealed protocol "
                      "supplies and a request may not")
    if sort in ("integer", "rational"):
        return (sort, Fraction(entry["value"]))
    return (sort, entry["value"])


def _subject(node: Any, where: str):
    if not isinstance(node, dict):
        raise Refusal(f"{where} is not an object")
    kind = node.get("kind")
    if kind == "protocol_claim":
        entry = _closed(node, where, ("kind", "artifact_id", "claim"))
        return ProtocolClaim(entry["artifact_id"],
                             _claim(entry["claim"], f"{where} claim"))
    if kind == "consumed_claim_vector":
        entry = _closed(node, where,
                        ("kind", "artifact_id", "consumer", "ordered_sources"))
        sources = entry["ordered_sources"]
        if not isinstance(sources, list):
            raise Refusal(f"{where} ordered sources is not an array")
        return ConsumedClaimVector(
            entry["artifact_id"],
            _claim(entry["consumer"], f"{where} consumer"),
            tuple(_claim(item, f"{where} source {index}")
                  for index, item in enumerate(sources)))
    raise Refusal(f"{where} names no admitted subject kind")


def _assumed_result(node: Any, where: str) -> None:
    """Validate the result an assumption asserts, and represent none of it.

    An assumed judgment carries an extraction result; every other shape is
    produced by evaluation, so asserting one would let a request state a
    conclusion it did not reach.  The coordinates are checked for shape and
    discarded, because this module stops where the bound begins and the
    skeleton drops results from every judgment.
    """
    if not isinstance(node, dict):
        raise Refusal(f"{where} result is not an object")
    kind = node.get("kind")
    if kind != "extraction":
        raise Refusal(f"{where} supplies a {kind!r} result; an assumed "
                      "judgment carries an extraction result, and every other "
                      "shape is produced by evaluation")
    entry = _closed(node, f"{where} result", ("kind", "coordinates"))
    coordinates = entry["coordinates"]
    if not isinstance(coordinates, list):
        raise Refusal(f"{where} result coordinates is not an array")
    for index, item in enumerate(coordinates):
        place = f"{where} result coordinate {index}"
        if not isinstance(item, dict):
            raise Refusal(f"{place} is not an object")
        for key in sorted(item):
            if key not in ("label", "arity", "challenge_space"):
                raise Refusal(f"{place} carries an unknown field {key!r}")
        for key in ("label", "arity"):
            if key not in item:
                raise Refusal(f"{place} is missing {key!r}")
        if not isinstance(item["label"], str):
            raise Refusal(f"{place} label is not a string")
        for key in ("arity", "challenge_space"):
            if key in item and not isinstance(item[key], dict):
                raise Refusal(f"{place} {key} is not a quantity")


def _judgment(node: Any, where: str) -> AssumedJudgment:
    entry = _closed(node, where, ("subject", "index", "result"))
    index = _closed(entry["index"], f"{where} index",
                    ("notion", "track", "variant", "model", "quantification"))
    # Required, not defaulted: the canonical form is total, and an
    # assumed judgment states the actual index it holds under, so a
    # variable has no place here.
    if index["quantification"] not in QUANTIFICATIONS:
        raise Refusal(f"{where} index carries an unknown quantification")
    _assumed_result(entry["result"], where)
    return AssumedJudgment(
        _subject(entry["subject"], f"{where} subject"),
        SecurityIndex(index["notion"], index["track"], index["variant"],
                      index["model"], index["quantification"]))


def _plan(node: Any, where: str, signature: Signature):
    if not isinstance(node, dict):
        raise Refusal(f"{where} is not an object")
    kind = node.get("kind")
    if kind == "assume":
        entry = _closed(node, where, ("kind", "judgment"))
        # No hypotheses field is readable, so a request cannot supply the
        # marker that evaluation synthesizes; the carrier refuses one
        # explicitly and here the closed field set makes it unspellable.
        return Assume(_judgment(entry["judgment"], f"{where} judgment"))
    if kind != "apply":
        raise Refusal(f"{where} names no admitted plan node kind")
    entry = _closed(node, where, ("kind", "site", "binding", "premises"))
    binding = entry["binding"]
    if not any(item.id == binding for item in signature.bindings):
        raise Refusal(f"{where} names binding '{binding}', which this "
                      "signature does not declare")
    premises = entry["premises"]
    if not isinstance(premises, dict):
        raise Refusal(f"{where} premises is not an object")
    return Apply(_site(entry["site"], f"{where} site"), binding,
                 {port: _plan(premises[port], f"{where}.{port}", signature)
                  for port in sorted(premises)})


def read_request(document: Any, signature: Signature) -> Request:
    root = _closed(document, "request", ("registry", "derivation"))
    if root["registry"] != "zkc.derivation_request":
        raise Refusal("this is not a derivation request")
    body = _closed(root["derivation"], "derivation",
                   ("selected_bindings", "resolved_parameters", "target",
                    "plan"))
    selected = tuple(body["selected_bindings"])
    declared = {item.id for item in signature.bindings}
    for name in selected:
        if name not in declared:
            raise Refusal(f"the request selects binding '{name}', which this "
                          "signature does not declare")
    parameters: dict[str, dict[str, tuple[str, Any]]] = {}
    for name, values in body["resolved_parameters"].items():
        if name not in declared:
            raise Refusal(f"the request resolves parameters for binding "
                          f"'{name}', which this signature does not declare")
        parameters[name] = {
            key: _resolved_value(value, f"resolved parameter '{key}'")
            for key, value in values.items()}
    target = _closed(body["target"], "target",
                     ("subject", "index", "resource_variables"))
    subject = _closed(target["subject"], "target subject",
                      ("kind", "artifact_id", "claim"))
    if subject["kind"] != "protocol_claim":
        raise Refusal("a target subject is an exact protocol claim")
    index = _closed(target["index"], "target index",
                    ("notion", "track", "variant", "model", "quantification"))
    if index["quantification"] not in QUANTIFICATIONS:
        raise Refusal("target index carries an unknown quantification")
    resources = tuple(
        (item["name"], item["sort"])
        for item in (_closed(entry, "target resource", ("name", "sort"))
                     for entry in target["resource_variables"]))
    return Request(
        selected, parameters,
        ProtocolClaim(subject["artifact_id"],
                      _claim(subject["claim"], "target claim")),
        SecurityIndex(index["notion"], index["track"], index["variant"],
                      index["model"], index["quantification"]),
        resources, _plan(body["plan"], "plan", signature))


# --------------------------------------------------------------------------
# The structural half of APPLY and DERIVE.
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Hypothesis:
    ref: ExactRef
    arguments: tuple[dict[str, Any], ...]

    def document(self) -> dict[str, Any]:
        return {"arguments": [dict(argument) for argument in self.arguments],
                "kind": "proposition", "ref": self.ref.document()}


@dataclass(frozen=True)
class Conclusion:
    subject: Any  # ProtocolClaim | ConsumedClaimVector
    index: SecurityIndex
    resources: tuple[tuple[str, str], ...]
    hypotheses: tuple[Any, ...]  # Hypothesis | AssumedJudgmentHolds

    def document(self) -> dict[str, Any]:
        return {
            "hypotheses": [item.document() for item in self.hypotheses],
            "index": self.index.document(),
            "resource_variables": [{"name": name, "sort": sort}
                                   for name, sort in self.resources],
            "subject": self.subject.document(),
        }


@dataclass(frozen=True)
class AppliedNode:
    site: Site
    binding: ExactRef
    premises: dict[str, Any]
    conclusion: Conclusion

    def document(self) -> dict[str, Any]:
        return {
            "binding": self.binding.document(),
            "conclusion": self.conclusion.document(),
            "kind": "applied",
            "premises": {port: node.document()
                         for port, node in self.premises.items()},
            "site": self.site.document(),
        }


@dataclass(frozen=True)
class AssumedNode:
    """An evaluated assumption: no site, no binding, and no premises.

    Its conclusion is the asserted judgment carrying the marker, which is the
    only difference between an assumption and a premise nobody supplied.
    """

    conclusion: Conclusion

    def document(self) -> dict[str, Any]:
        return {"conclusion": self.conclusion.document(), "kind": "assumed"}


def required_parameters(signature: Signature, binding: Binding
                        ) -> dict[str, str]:
    """The external values a binding demands, and the sort each is read at.

    A resolved parameter is never described as an artifact fact, so the caller
    supplies it; what the caller may not do is supply one nothing reads, or
    supply it at a sort other than the one it is read at.
    """
    rule = signature.rule(binding.rule)
    required: dict[str, str] = {}

    def take(value) -> None:
        if getattr(value, "kind", None) == "resolved_parameter":
            existing = required.setdefault(value.reference, value.sort)
            if existing != value.sort:
                raise Refusal(f"binding '{binding.id}' reads parameter "
                              f"'{value.reference}' at two sorts")

    for _, value in list(binding.parameter_bindings) + list(binding.fact_bindings):
        take(value)
    for _, values in (list(binding.condition_argument_bindings)
                      + list(binding.hypothesis_argument_bindings)):
        for value in values:
            take(value)
    for _, relation in binding.premise_relations:
        for value in relation.external_arguments:
            take(value)
    _collect_game_parameters(rule.body, take)
    return required


def _collect_game_parameters(node: Any, take) -> None:
    if hasattr(node, "game"):
        for argument in node.game.instance_arguments:
            take(argument)
        return
    for attribute in ("operands", "entries", "cases"):
        for child in getattr(node, attribute, ()) or ():
            _collect_game_parameters(child, take)
    for attribute in ("quantity", "scale", "arity", "challenge_space", "bound"):
        child = getattr(node, attribute, None)
        if child is not None:
            _collect_game_parameters(child, take)
    if hasattr(node, "fields"):
        for _, value in node.fields:
            _collect_game_parameters(value, take)


def derive(signature: Signature, view: SealedView,
           request: Request) -> dict[str, Any]:
    """The skeleton: the plan's shape and the structural part of every
    conclusion.  There is no theorem search, no provider resolution, and no
    fallback — the plan is explicit and this evaluates exactly it."""
    # The selected context is checked before anything is derived: a parameter
    # supplied at the wrong sort is a caller error whether or not the value
    # happens to reach a position this reference would otherwise resolve.
    for name in request.selected_bindings:
        binding = next(item for item in signature.bindings if item.id == name)
        required = required_parameters(signature, binding)
        supplied = request.resolved_parameters.get(name, {})
        if set(supplied) != set(required):
            missing = sorted(set(required) - set(supplied))
            extra = sorted(set(supplied) - set(required))
            detail = (f"does not resolve {missing[0]!r}" if missing
                      else f"resolves {extra[0]!r}, which nothing reads")
            raise Refusal(f"the request {detail} for binding '{name}'")
        for parameter, (sort, _) in supplied.items():
            if sort != required[parameter]:
                raise Refusal(f"the request resolves '{parameter}' at {sort} "
                              f"and binding '{name}' reads it at "
                              f"{required[parameter]}")

    # A root assumption would assert the whole answer, so the target's own
    # judgment is the one thing that must be reached rather than supplied.
    if isinstance(request.plan, Assume):
        raise Refusal("a protocol derivation root must be an application, not "
                      "an assumption")

    root = _node(signature, view, request, request.plan)
    if root.conclusion.subject != request.target_subject:
        raise Refusal("the root concludes about a different subject than the "
                      "target names")
    if root.conclusion.index != request.target_index:
        raise Refusal("the root concludes at a different index than the "
                      "target names")
    if root.conclusion.resources != request.target_resources:
        raise Refusal("the root quantifies over different resources than the "
                      "target declares")
    return {
        "artifact_id": view.artifact_id,
        "root": root.document(),
        "target": {
            "index": request.target_index.document(),
            "resource_variables": [{"name": name, "sort": sort}
                                   for name, sort in request.target_resources],
            "subject": request.target_subject.document(),
        },
    }


def _node(signature: Signature, view: SealedView, request: Request, plan):
    """Evaluate one plan node.  An assumption is a leaf; an application recurs."""
    if isinstance(plan, Assume):
        return _assume(plan)
    return _apply(signature, view, request, plan)


def _assume(plan: Assume) -> AssumedNode:
    asserted = plan.asserted
    return AssumedNode(Conclusion(asserted.subject, asserted.index, (),
                                  (AssumedJudgmentHolds(asserted),)))


def carry_quantification(rule: Rule,
                         supplied: dict[str, "SecurityIndex"]):
    """Match each premise index and return the instantiated conclusion.

    One binding across all ports: a second premise naming the same
    variable is a constraint on what the first bound, and the conclusion
    restates the bound value. Stated once, apart from `_apply`, so the
    adaptive direction can be exercised against a widened schema without
    a full derivation — no shipped index is non-static, which would
    otherwise leave this path running only on the value it produces
    anyway.
    """
    bound_quantification: str | None = None
    for port in rule.premises:
        supplied_index = supplied[port.name]
        expected = port.expected_index
        if expected.quantification.startswith("$"):
            value = supplied_index.quantification
            if bound_quantification is None:
                bound_quantification = value
            elif bound_quantification != value:
                raise Refusal(f"premise '{port.name}' of rule '{rule.id}' "
                              "binds the quantification variable to a value "
                              "another premise disagrees with")
            expected = replace(expected, quantification=value)
        if supplied_index != expected:
            raise Refusal(f"premise '{port.name}' of rule '{rule.id}' expects "
                          f"{port.expected_index.notion} and the child "
                          f"concludes {supplied_index.notion}")
    conclusion_index = rule.conclusion_index
    if conclusion_index.quantification.startswith("$"):
        if bound_quantification is None:
            raise Refusal(f"rule '{rule.id}' concludes an index variable no "
                          "premise bound")
        conclusion_index = replace(conclusion_index,
                                   quantification=bound_quantification)
    return conclusion_index


def _apply(signature: Signature, view: SealedView, request: Request,
           plan: Apply) -> AppliedNode:
    binding = next(item for item in signature.bindings
                   if item.id == plan.binding)
    if plan.binding not in request.selected_bindings:
        raise Refusal(f"the plan applies binding '{plan.binding}', which the "
                      "selected context does not offer")
    rule = signature.rule(binding.rule)
    subject = subject_of(view, plan.site)

    # The occurrence has to be the one the binding anchors to, or the rule is
    # being applied to structure it was never connected to.
    if plan.site.kind == "reduction":
        if binding.anchor_kind != "reduction_contract":
            raise Refusal(f"binding '{binding.id}' anchors to a path and the "
                          "site is a reduction")
        reduction = view.reductions[plan.site.transformer_position]
        if reduction.contract_ref != binding.anchor_ref:
            raise Refusal(f"binding '{binding.id}' names contract "
                          f"'{binding.anchor_ref.id}' and the occurrence was "
                          f"checked against '{reduction.contract_ref.id}'")
    elif binding.anchor_kind != "path_transition":
        raise Refusal(f"binding '{binding.id}' anchors to a reduction and the "
                      "site is a path")

    _coverage(view, plan.site, binding)

    if set(plan.premises) != {port.name for port in rule.premises}:
        raise Refusal(f"the plan supplies premises {sorted(plan.premises)} and "
                      f"rule '{rule.id}' declares "
                      f"{sorted(port.name for port in rule.premises)}")

    premises: dict[str, Any] = {}
    for port in sorted(plan.premises):
        premises[port] = _node(signature, view, request, plan.premises[port])

    relations = dict(binding.premise_relations)
    conclusion_index = carry_quantification(
        rule, {port.name: premises[port.name].conclusion.index
               for port in rule.premises})
    for port in rule.premises:
        child = premises[port.name]
        expected = _expected_subject(view, plan.site, subject,
                                     relations[port.name], port.name)
        if child.conclusion.subject != expected:
            raise Refusal(f"premise '{port.name}' is about "
                          f"{canon_json(child.conclusion.subject.document())} "
                          f"and its relation selects "
                          f"{canon_json(expected.document())}")

    hypotheses: list[Any] = []
    # Declaration order, not plan order: the plan decides which child is
    # evaluated first, the rule decides which obligations come first.
    for port in rule.premises:
        for hypothesis in premises[port.name].conclusion.hypotheses:
            if hypothesis not in hypotheses:
                hypotheses.append(hypothesis)
    for template in rule.external_hypotheses:
        instance = _instantiate(signature, view, request, binding, rule,
                                plan.site, subject, template)
        if instance not in hypotheses:
            hypotheses.append(instance)

    return AppliedNode(
        plan.site, ExactRef(binding.id, binding.revision()), premises,
        Conclusion(subject, conclusion_index,
                   tuple((item.name, item.sort) for item in rule.resources),
                   tuple(hypotheses)))


def _coverage(view: SealedView, site: Site, binding: Binding) -> None:
    """The derivation must follow the claim graph.

    Every consumed claim some transformer produced must be selected by one of
    the binding's consumed-claim premise relations, and every selected input
    position must name a consumed claim.  Containment, not equality: a
    premise about an artifact source stays the artifact's own hypothesis.
    The producer map is a fold over the sealed view, and the judgment is
    vacuous at a path occurrence, which consumes nothing.
    """
    if site.kind != "reduction":
        return
    reduction = view.reductions[site.transformer_position]
    selected: set[int] = set()
    for relation in dict(binding.premise_relations).values():
        if relation.kind == "consumed_claim":
            selected.update(relation.input_indices)
        elif relation.kind == "consumed_claim_vector":
            if relation.selector == "all_reduction_inputs":
                selected.update(range(len(reduction.ordered_inputs)))
            else:
                selected.update(relation.input_indices)
    produced = {output.claim_index
                for other in view.reductions.values()
                for output in other.ordered_outputs}
    uncovered = sorted(
        claim.claim_index
        for position, claim in enumerate(reduction.ordered_inputs)
        if position not in selected and claim.claim_index in produced)
    beyond = sorted(position for position in selected
                    if position >= len(reduction.ordered_inputs))
    if uncovered or beyond:
        raise Refusal(
            "the binding's premise relations do not follow the claim graph: "
            f"uncovered produced claims {uncovered}, "
            f"selections beyond the consumed list {beyond}")


def _expected_subject(view: SealedView, site: Site, subject: ProtocolClaim,
                      relation, port: str):
    if relation.kind == "same_subject":
        return subject
    if site.kind != "reduction":
        raise Refusal(f"premise '{port}' consumes reduction inputs at a path "
                      "occurrence")
    reduction = view.reductions[site.transformer_position]
    if relation.kind == "consumed_claim":
        index = relation.input_indices[0]
        if index >= len(reduction.ordered_inputs):
            raise Refusal(f"premise '{port}' selects operand {index} and the "
                          f"reduction consumes {len(reduction.ordered_inputs)}")
        return ProtocolClaim(view.artifact_id, reduction.ordered_inputs[index])
    if relation.kind != "consumed_claim_vector":
        raise Refusal(f"premise '{port}' asserts an external subject, which "
                      "this reference does not derive")
    if relation.selector == "all_reduction_inputs":
        sources = reduction.ordered_inputs
        if not sources:
            raise Refusal(f"premise '{port}' selects a whole vector and the "
                          "reduction consumes nothing")
    else:
        for index in relation.input_indices:
            if index >= len(reduction.ordered_inputs):
                raise Refusal(f"premise '{port}' selects operand {index}, "
                              "which is out of range")
        sources = tuple(reduction.ordered_inputs[index]
                        for index in relation.input_indices)
    return ConsumedClaimVector(view.artifact_id, subject.claim, sources)


def _instantiate(signature: Signature, view: SealedView, request: Request,
                 binding: Binding, rule: Rule, site: Site,
                 subject: ProtocolClaim, template) -> Hypothesis:
    arguments = dict(binding.hypothesis_argument_bindings)[template.slot]
    proposition = next((ref for identifier, ref, _
                        in signature.schemas.propositions
                        if identifier == template.ref), None)
    if proposition is None:
        raise Refusal(f"rule '{rule.id}' names an undeclared proposition")
    return Hypothesis(proposition,
                      tuple(_resolve(view, request, binding, site, subject,
                                     value)
                            for value in arguments))


def _resolve(view: SealedView, request: Request, binding: Binding, site: Site,
             subject: ProtocolClaim, value) -> dict[str, Any]:
    """A hypothesis argument, in the form the judgment document carries it."""
    if value.kind == "conclusion_subject":
        return {"sort": "subject", "value": subject.document()}
    if value.kind == "resolved_parameter":
        supplied = request.resolved_parameters.get(binding.id, {})
        if value.reference not in supplied:
            raise Refusal(f"binding '{binding.id}' reads parameter "
                          f"'{value.reference}', which the request does not "
                          "resolve")
        sort, resolved = supplied[value.reference]
        if sort != value.sort:
            raise Refusal(f"parameter '{value.reference}' is resolved at "
                          f"{sort} and read at {value.sort}")
        return {"sort": sort, "value": _scalar(resolved)}
    if value.kind == "literal":
        return {"sort": value.sort, "value": _scalar(value.literal)}
    if value.kind == "sealed_artifact_projection":
        projection = value.artifact_projection
        if projection.kind != "conclusion_reduction_contract":
            raise Refusal("this reference resolves only the conclusion "
                          "contract into a hypothesis argument")
        if site.kind != "reduction":
            raise Refusal("a contract projection at a path occurrence")
        return {"sort": "reduction_contract",
                "value": view.reductions[
                    site.transformer_position].contract_ref.document()}
    raise Refusal(f"a hypothesis argument of kind '{value.kind}' is not "
                  "structurally resolvable")


def _scalar(value: Any) -> Any:
    if isinstance(value, Fraction):
        return (str(value.numerator) if value.denominator == 1
                else f"{value.numerator}/{value.denominator}")
    if hasattr(value, "document"):
        return value.document()
    return value
