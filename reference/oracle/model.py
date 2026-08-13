"""Independent PIR model, reduction/terminal judgments, and encoders.

The authored object is deliberately close to the kernel rather than MLIR.
Labels are handles only; canonical form replaces every reference with an
event, claim, or transformer position.

Protocol dictionaries contain:

``policy``
    One of the closed seal policies.
``kappa``
    The construction profile selection.
``sources``
    :class:`Source` rows carrying an exact claim-profile id and anchors.
``events``
    ``bind`` / ``slot`` / ``chal`` / ``check`` rows in spine order.
``reduces``
    Generic :class:`Reduce` rows. Reduction contracts own both transcript shape
    and the exact local implication.
``material_bindings``
    Injective local-value to semantic-reference edges.
``sinks``
    Rule/check-map discharges or explicit routes.
``routes``
    Optional prover construction instances and ordered witness handle classes.

No earlier encoding, claim-kind, check-kind, or split-contract interpretation is
present here. The only semantic registry is ProtocolVocabulary v4.
"""

from __future__ import annotations

import hashlib
import heapq
import json
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, NamedTuple


ROOT = Path(__file__).resolve().parents[2]
REGISTRY = ROOT / "registry"


def canon_json(value: Any) -> str:
    """The single canonical JSON spelling used by every digest."""

    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=True
    )


def tagged_digest(tag: str, value: Any, *, reference: bool = True) -> str:
    digest = hashlib.sha256(tag.encode("ascii") + canon_json(value).encode("ascii"))
    encoded = digest.hexdigest()
    return "sha256:" + encoded if reference else encoded


def material_construct(tag: str, typed_arguments: list[list[Any]]) -> str:
    """Evaluate the sole MaterialExpr reference constructor."""

    if not isinstance(tag, str) or not tag or not all(
        0x20 <= ord(char) <= 0x7E for char in tag
    ):
        raise Refusal("material constructor tag is not printable ASCII")
    valid_sorts = {"ref", "refs", "claim", "claims", "atom"}
    if any(
        not isinstance(argument, list)
        or len(argument) != 2
        or argument[0] not in valid_sorts
        for argument in typed_arguments
    ):
        raise Refusal("material constructor has malformed typed arguments")
    return tagged_digest(
        "zkc/material-expr\n",
        ["construct", tag, typed_arguments],
    )


def is_sha256_ref(value: Any) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 71
        and value.startswith("sha256:")
        and all(char in "0123456789abcdef" for char in value[7:])
    )


MAX_ATTR_DEPTH = 64


def check_domain(value: Any, depth: int = 0) -> None:
    """Admit exactly the identity-bearing MLIR attribute domain."""

    if depth > MAX_ATTR_DEPTH:
        raise ValueError("E228: canonical attribute nesting exceeds 64")
    if value is None:
        return
    if type(value) is bool:
        raise ValueError("E228: booleans are outside the canonical domain")
    if type(value) is int:
        if not -(1 << 63) <= value < 1 << 63:
            raise ValueError("E228: integer is outside signed 64-bit range")
        return
    if isinstance(value, str):
        if not all(0x20 <= ord(char) <= 0x7E for char in value):
            raise ValueError("E228: strings must be printable ASCII")
        return
    if isinstance(value, (list, tuple)):
        for member in value:
            check_domain(member, depth + 1)
        return
    if isinstance(value, dict):
        for key, member in value.items():
            if not isinstance(key, str):
                raise ValueError("E228: canonical dictionary keys are strings")
            check_domain(key, depth + 1)
            check_domain(member, depth + 1)
        return
    raise ValueError(f"E228: unsupported canonical value {type(value).__name__}")


def check_atom_domain(value: Any, depth: int = 0) -> None:
    """Admit the non-null kernel attribute subset used by registry atoms."""

    if depth > MAX_ATTR_DEPTH:
        raise Refusal("canonical atom nesting exceeds 64")
    if value is None or type(value) is bool:
        raise Refusal("null and booleans are outside the canonical atom domain")
    if type(value) is int:
        if not -(1 << 63) <= value < 1 << 63:
            raise Refusal("canonical atom integer is outside signed 64-bit range")
        return
    if isinstance(value, str):
        if not all(0x20 <= ord(char) <= 0x7E for char in value):
            raise Refusal("canonical atom string is not printable ASCII")
        return
    if isinstance(value, (list, tuple)):
        for member in value:
            check_atom_domain(member, depth + 1)
        return
    if isinstance(value, dict):
        for key, member in value.items():
            if not isinstance(key, str) or not key:
                raise Refusal("canonical atom object keys must be nonempty strings")
            check_atom_domain(key, depth + 1)
            check_atom_domain(member, depth + 1)
        return
    raise Refusal(f"unsupported canonical atom {type(value).__name__}")


class Refusal(ValueError):
    """A failed static judgment."""


def _unique_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    """Refuse a duplicate decoded object key at any depth."""

    seen: dict[str, Any] = {}
    for key, value in pairs:
        if key in seen:
            raise Refusal(f"duplicate JSON object key {key!r}")
        seen[key] = value
    return seen


def _reject_non_integer_number(literal: str) -> Any:
    raise Refusal(
        "a numeric value leaves the encoding domain: exact values are "
        "decimal integers or decimal strings"
    )


def load_json(text: str) -> Any:
    """Parse one authority input under the canonical JSON domain.

    Duplicate decoded keys have no last-wins reading. Floating-point syntax
    and Python's non-standard NaN/Infinity constants have no representation in
    the integer-only encoding domain.
    """

    try:
        return json.loads(
            text,
            object_pairs_hook=_unique_keys,
            parse_float=_reject_non_integer_number,
            parse_constant=_reject_non_integer_number,
        )
    except json.JSONDecodeError as error:
        raise Refusal(f"invalid JSON: {error.msg}") from None


def _message_count_is_dynamic(multiplicity: dict[str, Any]) -> bool:
    return multiplicity == {"same_as": "consumed_claims"}


def _resolve_message_count(
    multiplicity: dict[str, Any], consumed_claims: int
) -> int:
    if _message_count_is_dynamic(multiplicity):
        return consumed_claims
    return multiplicity["exact"]


def _closed(body: dict[str, Any], fields: set[str], where: str) -> None:
    unknown = set(body) - fields
    missing = fields - set(body)
    if unknown or missing:
        raise Refusal(
            f"{where} has missing={sorted(missing)} unknown={sorted(unknown)}"
        )


class ProtocolVocabulary:
    """Normalized, cross-admitted semantic vocabulary.

    The loader is intentionally independent of the carrier.  It normalizes
    the semantic sections plus the closed opaque-predicate preimage section
    and derives the same transitive content digests from the public JSON
    format.
    """

    def __init__(self, document: dict[str, Any]):
        _closed(
            document,
            {
                "registry",
                "claim_profiles",
                "predicate_specs",
                "check_contracts",
                "hole_contracts",
                "reduction_contracts",
                "terminal_rules",
            },
            "protocol vocabulary",
        )
        if document["registry"] != "zkc.protocol_vocabulary":
            raise Refusal("unsupported ProtocolVocabulary envelope")

        self.profiles = {
            name: self._profile(name, body)
            for name, body in document["claim_profiles"].items()
        }
        self.predicate_specs = {
            digest: self._predicate_spec(digest, body)
            for digest, body in document["predicate_specs"].items()
        }
        self.contracts = {
            name: self._contract(name, body)
            for name, body in document["check_contracts"].items()
        }
        cited_specs = {
            body["predicate"]["content_digest"]
            for body in self.contracts.values()
            if body["mode"] == "opaque"
        }
        if cited_specs != set(self.predicate_specs):
            raise Refusal(
                "predicate_specs must be exactly the closure cited by opaque checks"
            )
        self.hole_contracts = {
            name: self._hole_contract(name, body)
            for name, body in document["hole_contracts"].items()
        }
        self.reductions = {
            name: self._reduction(name, body)
            for name, body in document["reduction_contracts"].items()
        }
        self.rules = {
            name: self._rule(name, body)
            for name, body in document["terminal_rules"].items()
        }

        self.profile_digests = {
            name: tagged_digest("zkc/claim-profile\n", body)
            for name, body in self.profiles.items()
        }
        self.hole_contract_digests = {
            name: tagged_digest("zkc/hole-contract\n", body)
            for name, body in self.hole_contracts.items()
        }
        self.contract_digests = {
            name: tagged_digest("zkc/check-contract\n", body)
            for name, body in self.contracts.items()
        }
        self.reduction_digests = {}
        for name, body in self.reductions.items():
            profile_ids = {
                member if isinstance(member, str) else member["profile"]
                for member in body["consumes"]
            } | {output["profile"] for output in body["outputs"]}
            try:
                profile_digests = {
                    profile: self.profile_digests[profile]
                    for profile in sorted(profile_ids)
                }
                check_digests = {
                    role: self.contract_digests[slot["contract"]]
                    for role, slot in sorted(body["checks"].items())
                }
            except KeyError as error:
                raise Refusal(
                    f"reduction contract {name!r} has unresolved citation "
                    f"{error.args[0]!r}"
                ) from None
            self.reduction_digests[name] = tagged_digest(
                "zkc/reduction-contract\n",
                {
                    "check_contract_digests": check_digests,
                    "content": body,
                    "profile_digests": profile_digests,
                },
            )

        self.rule_digests = {}
        for name, body in self.rules.items():
            try:
                preimage = {
                    "claim_profile_digest": self.profile_digests[
                        body["claim_profile"]
                    ],
                    "check_contract_digests": {
                        role: self.contract_digests[contract]
                        for role, contract in sorted(body["checks"].items())
                    },
                    "content": body,
                }
                if "producer" in body:
                    preimage["producer_contract_digest"] = self.reduction_digests[
                        body["producer"]["contract"]
                    ]
            except KeyError as error:
                raise Refusal(
                    f"terminal rule {name!r} has unresolved citation "
                    f"{error.args[0]!r}"
                ) from None
            self.rule_digests[name] = tagged_digest(
                "zkc/terminal-rule\n", preimage
            )

        self.document = {
            "check_contracts": self.contracts,
            "claim_profiles": self.profiles,
            "hole_contracts": self.hole_contracts,
            "predicate_specs": self.predicate_specs,
            "reduction_contracts": self.reductions,
            "registry": "zkc.protocol_vocabulary",
            "terminal_rules": self.rules,
        }

    @classmethod
    def load(cls, path: Path | str) -> "ProtocolVocabulary":
        return cls(load_json(Path(path).read_text(encoding="utf-8")))

    @staticmethod
    def _strings(value: Any, where: str, *, sort: bool = False) -> list[str]:
        if not isinstance(value, list) or not all(
            isinstance(member, str) and member for member in value
        ):
            raise Refusal(f"{where} must be a string array")
        if not all(
            all(0x20 <= ord(char) <= 0x7E for char in member)
            for member in value
        ):
            raise Refusal(f"{where} entries must be printable ASCII")
        if len(set(value)) != len(value):
            raise Refusal(f"{where} contains duplicates")
        return sorted(value) if sort else list(value)

    def _profile(self, name: str, body: Any) -> dict[str, Any]:
        if not isinstance(body, dict):
            raise Refusal(f"claim profile {name!r} must be an object")
        _closed(body, {"kind", "anchors"}, f"claim profile {name!r}")
        if (
            not isinstance(body["kind"], str)
            or not body["kind"]
            or not all(0x20 <= ord(char) <= 0x7E for char in body["kind"])
        ):
            raise Refusal(f"claim profile {name!r} has no kind")
        return {
            "anchors": self._strings(
                body["anchors"], f"{name} anchors", sort=True
            ),
            "kind": body["kind"],
        }

    def _check_abi(
        self,
        parameters_value: Any,
        semantic_value: Any,
        operands_value: Any,
        where: str,
    ) -> dict[str, Any]:
        parameters = self._strings(
            parameters_value, f"{where} parameters", sort=True
        )
        semantic = self._strings(
            semantic_value, f"{where} semantic parameters", sort=True
        )
        occupied = set(parameters) | set(semantic)
        if len(occupied) != len(parameters) + len(semantic):
            raise Refusal(f"{where} has duplicate roles")
        if not isinstance(operands_value, list):
            raise Refusal(f"{where} operands must be an array")
        operands = []
        captures: set[str] = set()
        for index, operand in enumerate(operands_value):
            operand_where = f"{where} operand {index}"
            if not isinstance(operand, dict):
                raise Refusal(f"{operand_where} must be an object")
            _closed(
                operand,
                {"role", "class", "multiplicity"},
                operand_where,
            )
            role = operand["role"]
            value_class = operand["class"]
            if (
                not isinstance(role, str)
                or not role
                or role in occupied
                or not isinstance(value_class, str)
                or not value_class
                or value_class == "chal"
            ):
                raise Refusal(f"{operand_where} has invalid role or class")
            occupied.add(role)
            multiplicity = operand["multiplicity"]
            if not isinstance(multiplicity, dict):
                raise Refusal(f"{operand_where} has malformed multiplicity")
            if set(multiplicity) == {"exact"}:
                amount = multiplicity["exact"]
                if type(amount) is not int or not 1 <= amount <= 1 << 20:
                    raise Refusal(
                        f"{operand_where} has invalid exact multiplicity"
                    )
                normalized = {"exact": amount}
            elif set(multiplicity) == {"capture", "min"}:
                capture, minimum = multiplicity["capture"], multiplicity["min"]
                if (
                    not isinstance(capture, str)
                    or not capture
                    or capture in captures
                    or captures
                    or type(minimum) is not int
                    or not 1 <= minimum <= 1 << 20
                ):
                    raise Refusal(f"{operand_where} has invalid count capture")
                captures.add(capture)
                normalized = {"capture": capture, "min": minimum}
            elif set(multiplicity) == {"same_as"}:
                capture = multiplicity["same_as"]
                if capture not in captures:
                    raise Refusal(
                        f"{operand_where} references an unbound capture"
                    )
                normalized = {"same_as": capture}
            else:
                raise Refusal(f"{operand_where} has unknown multiplicity")
            operands.append(
                {
                    "class": value_class,
                    "multiplicity": normalized,
                    "role": role,
                }
            )
        return {
            "operands": operands,
            "parameters": parameters,
            "semantic_parameters": semantic,
        }

    def _predicate_spec(self, digest: str, body: Any) -> dict[str, Any]:
        where = f"predicate spec {digest!r}"
        if not is_sha256_ref(digest) or not isinstance(body, dict):
            raise Refusal(f"{where} has malformed key or body")
        expected = {"format", "title", "entrypoints"}
        if "references" in body:
            expected.add("references")
        _closed(body, expected, where)
        if (
            body["format"] != "zkc-check-predicate-spec"
            or not isinstance(body["title"], str)
            or not body["title"]
            or not all(0x20 <= ord(char) <= 0x7E for char in body["title"])
        ):
            raise Refusal(f"{where} has wrong format or title")
        entrypoints_value = body["entrypoints"]
        if not isinstance(entrypoints_value, dict) or not entrypoints_value:
            raise Refusal(f"{where} has no entrypoints")
        entrypoints: dict[str, Any] = {}
        for name, entrypoint in entrypoints_value.items():
            entry_where = f"{where} entrypoint {name!r}"
            if (
                not isinstance(name, str)
                or not name
                or not all(0x20 <= ord(char) <= 0x7E for char in name)
                or not isinstance(entrypoint, dict)
            ):
                raise Refusal(f"{entry_where} is malformed")
            _closed(
                entrypoint,
                {
                    "acceptance",
                    "parameters",
                    "semantic_parameters",
                    "operands",
                },
                entry_where,
            )
            acceptance = self._strings(
                entrypoint["acceptance"], f"{entry_where} acceptance"
            )
            if not acceptance:
                raise Refusal(f"{entry_where} has no acceptance clauses")
            entrypoints[name] = {
                "acceptance": acceptance,
                **self._check_abi(
                    entrypoint["parameters"],
                    entrypoint["semantic_parameters"],
                    entrypoint["operands"],
                    entry_where,
                ),
            }
        normalized = {
            "entrypoints": entrypoints,
            "format": "zkc-check-predicate-spec",
            "title": body["title"],
        }
        if "references" in body:
            references = self._strings(
                body["references"], f"{where} references"
            )
            if not references:
                raise Refusal(f"{where} references must be absent or non-empty")
            normalized["references"] = references
        derived = tagged_digest("zkc/check-predicate-spec\n", normalized)
        if derived != digest:
            raise Refusal(
                f"{where} key does not match canonical content digest {derived}"
            )
        return normalized

    def _contract(self, name: str, body: Any) -> dict[str, Any]:
        if not isinstance(body, dict):
            raise Refusal(f"check contract {name!r} must be an object")
        _closed(
            body,
            {
                "mode",
                "predicate",
                "parameters",
                "semantic_parameters",
                "operands",
            },
            f"check contract {name!r}",
        )
        if body["mode"] not in {"opaque", "transparent"}:
            raise Refusal(f"check contract {name!r} has unknown mode")
        predicate = body["predicate"]
        if not isinstance(predicate, dict):
            raise Refusal(f"check contract {name!r} predicate must be an object")
        if body["mode"] == "transparent":
            _closed(
                predicate,
                {"format"},
                f"check contract {name!r} predicate",
            )
            if predicate["format"] != "zkc-transparent-expression":
                raise Refusal(
                    f"check contract {name!r} has wrong transparent predicate format"
                )
            normalized_predicate = {"format": "zkc-transparent-expression"}
        else:
            _closed(
                predicate,
                {"format", "content_digest", "entrypoint"},
                f"check contract {name!r} predicate",
            )
            entrypoint = predicate["entrypoint"]
            if (
                predicate["format"] != "zkc-opaque-predicate-spec"
                or not is_sha256_ref(predicate["content_digest"])
                or not isinstance(entrypoint, str)
                or not entrypoint
                or not all(0x20 <= ord(char) <= 0x7E for char in entrypoint)
            ):
                raise Refusal(
                    f"check contract {name!r} has malformed opaque predicate descriptor"
                )
            normalized_predicate = {
                "content_digest": predicate["content_digest"],
                "entrypoint": entrypoint,
                "format": "zkc-opaque-predicate-spec",
            }
        abi = self._check_abi(
            body["parameters"],
            body["semantic_parameters"],
            body["operands"],
            f"check contract {name!r}",
        )
        if body["mode"] == "opaque":
            spec = self.predicate_specs.get(normalized_predicate["content_digest"])
            entrypoint = (
                spec["entrypoints"].get(normalized_predicate["entrypoint"])
                if spec is not None
                else None
            )
            if entrypoint is None:
                raise Refusal(
                    f"check contract {name!r} has unresolved predicate spec or entrypoint"
                )
            expected_abi = {
                key: entrypoint[key]
                for key in ("operands", "parameters", "semantic_parameters")
            }
            if abi != expected_abi:
                raise Refusal(
                    f"check contract {name!r} ABI differs from predicate entrypoint"
                )
        return {
            "mode": body["mode"],
            **abi,
            "predicate": normalized_predicate,
        }

    def _hole_segments(self, value: Any, where: str) -> list[dict[str, Any]]:
        if not isinstance(value, list):
            raise Refusal(f"{where}s must be an array")
        segments: list[dict[str, Any]] = []
        roles: set[str] = set()
        for index, segment in enumerate(value):
            ctx = f"{where} segment #{index}"
            if not isinstance(segment, dict):
                raise Refusal(f"{ctx} must be an object")
            sort = segment.get("sort")
            if sort == "value":
                _closed(segment, {"sort", "role", "class", "count"}, ctx)
                count = segment["count"]
                if (
                    not isinstance(count, str)
                    or not count.isdigit()
                    or (len(count) > 1 and count[0] == "0")
                    or not 1 <= int(count) <= 1 << 20
                ):
                    raise Refusal(
                        f"{ctx} count must be a canonical decimal from 1 "
                        "through 2^20"
                    )
                normalized = {
                    "class": segment["class"],
                    "count": count,
                    "role": segment["role"],
                    "sort": "value",
                }
            elif sort == "handle":
                _closed(segment, {"sort", "role", "class"}, ctx)
                normalized = {
                    "class": segment["class"],
                    "role": segment["role"],
                    "sort": "handle",
                }
            elif sort == "sponge":
                _closed(segment, {"sort", "role"}, ctx)
                normalized = {"role": segment["role"], "sort": "sponge"}
            else:
                raise Refusal(
                    f'{ctx} sort must be "value", "handle", or "sponge"'
                )
            role = normalized["role"]
            if (
                not isinstance(role, str)
                or not role
                or not all(0x20 <= ord(char) <= 0x7E for char in role)
            ):
                raise Refusal(f"{ctx} role must be non-empty printable ASCII")
            if role in roles:
                raise Refusal(f"{ctx} role duplicates an earlier segment")
            roles.add(role)
            type_class = normalized.get("class")
            if sort != "sponge" and (
                not isinstance(type_class, str)
                or not type_class
                or not all(0x20 <= ord(char) <= 0x7E for char in type_class)
            ):
                raise Refusal(f"{ctx} class must be non-empty printable ASCII")
            segments.append(normalized)
        return segments

    def _hole_contract(self, name: str, body: Any) -> dict[str, Any]:
        if not isinstance(body, dict):
            raise Refusal(f"hole contract {name!r} must be an object")
        _closed(
            body,
            {"kind", "operands", "results", "parameters",
             "semantic_parameters"},
            f"hole contract {name!r}",
        )
        kind = body["kind"]
        if kind not in {
            "commit", "extend", "evaluate", "fold", "open", "pow_search",
        }:
            raise Refusal(f"hole contract {name!r} has unknown kind")
        operands = self._hole_segments(
            body["operands"], f"hole contract {name!r} operand"
        )
        results = self._hole_segments(
            body["results"], f"hole contract {name!r} result"
        )
        if not results:
            raise Refusal(f"hole contract {name!r} declares at least one result")
        sponge_ins = sum(1 for s in operands if s["sort"] == "sponge")
        sponge_outs = sum(1 for s in results if s["sort"] == "sponge")
        if kind == "pow_search":
            if sponge_ins != 1 or sponge_outs != 1:
                raise Refusal(
                    f"hole contract {name!r} pow_search declares exactly one "
                    "sponge operand and one sponge result"
                )
        elif sponge_ins or sponge_outs:
            raise Refusal(
                f"hole contract {name!r}: only a pow_search hole declares "
                "sponge segments"
            )
        parameters = self._strings(
            body["parameters"], f"hole contract {name!r} parameters",
            sort=True,
        )
        semantic = self._strings(
            body["semantic_parameters"],
            f"hole contract {name!r} semantic parameters",
            sort=True,
        )
        if len(set(parameters)) != len(parameters) or len(
            set(semantic)
        ) != len(semantic):
            raise Refusal(f"hole contract {name!r} has duplicate parameters")
        if set(parameters) & set(semantic):
            raise Refusal(
                f"hole contract {name!r} parameter and semantic-parameter "
                "names must be disjoint"
            )
        return {
            "kind": kind,
            "operands": operands,
            "parameters": parameters,
            "results": results,
            "semantic_parameters": semantic,
        }

    def _normalize_material_expr(
        self,
        contract_name: str,
        node: Any,
        context: dict[str, Any],
        depth: int = 0,
        counter: list[int] | None = None,
    ) -> tuple[dict[str, Any], str]:
        """Admit one closed, statically sorted MaterialExpr node."""

        where = f"reduction contract {contract_name!r} material expression"
        if counter is None:
            counter = [0]
        counter[0] += 1
        if counter[0] > 1 << 20:
            raise Refusal(f"{where} has too many nodes")
        if (
            depth >= MAX_ATTR_DEPTH
            or not isinstance(node, dict)
            or "kind" not in node
        ):
            raise Refusal(f"{where} is malformed or too deep")
        kind = node["kind"]
        if not isinstance(kind, str):
            raise Refusal(f"{where} has a non-string kind")

        def exact(fields: set[str]) -> None:
            _closed(node, {"kind", *fields}, f"{where} {kind!r}")

        def name(field: str) -> str:
            value = node[field]
            if not isinstance(value, str) or not value:
                raise Refusal(f"{where} {kind!r} has invalid {field}")
            return value

        def input_profile(index: Any) -> str:
            if type(index) is not int or index < 0:
                raise Refusal(f"{where} {kind!r} has invalid input index")
            patterns = context["consumes"]
            if len(patterns) == 1 and isinstance(patterns[0], dict):
                if index >= patterns[0]["min"]:
                    raise Refusal(
                        f"{where} fixed input index is outside variadic minimum"
                    )
                return patterns[0]["profile"]
            if index >= len(patterns):
                raise Refusal(f"{where} input index is out of range")
            return patterns[index]

        def require_anchor(profile: str, anchor: str) -> None:
            admitted = self.profiles.get(profile)
            if admitted is None or anchor not in admitted["anchors"]:
                raise Refusal(
                    f"{where} cites unknown anchor {anchor!r} on {profile!r}"
                )

        if kind == "literal_ref":
            exact({"value"})
            value = node["value"]
            if not is_sha256_ref(value):
                raise Refusal(f"{where} literal_ref is not a MaterialRef")
            return {"kind": kind, "value": value}, "ref"
        if kind == "input_anchor":
            exact({"input", "anchor"})
            anchor = name("anchor")
            require_anchor(input_profile(node["input"]), anchor)
            return {
                "anchor": anchor,
                "input": node["input"],
                "kind": kind,
            }, "ref"
        if kind in {"dependency", "message"}:
            fields = (
                {"role"} if kind == "dependency" else {"role", "occurrence"}
            )
            exact(fields)
            role = name("role")
            table = context["deps"] if kind == "dependency" else context["messages"]
            if role not in table:
                raise Refusal(f"{where} cites unknown {kind} role {role!r}")
            result = {"kind": kind, "role": role}
            if kind == "message":
                multiplicity = table[role]
                if _message_count_is_dynamic(multiplicity):
                    raise Refusal(
                        f"{where} cannot select one occurrence from a dynamic "
                        "message role"
                    )
                index = node["occurrence"]
                if (
                    type(index) is not int
                    or not 0 <= index < multiplicity["exact"]
                ):
                    raise Refusal(f"{where} has invalid message occurrence")
                result["occurrence"] = index
            return result, "ref"
        if kind == "parameter_ref":
            exact({"name"})
            parameter = name("name")
            if context["parameters"].get(parameter) != "material_ref":
                raise Refusal(f"{where} parameter_ref has incompatible sort")
            return {"kind": kind, "name": parameter}, "ref"
        if kind == "construct":
            exact({"tag", "args"})
            tag = name("tag")
            if not all(0x20 <= ord(char) <= 0x7E for char in tag):
                raise Refusal(f"{where} construct tag is not printable ASCII")
            if not isinstance(node["args"], list):
                raise Refusal(f"{where} construct args must be an array")
            args = []
            for argument in node["args"]:
                normalized, sort = self._normalize_material_expr(
                    contract_name, argument, context, depth + 1, counter
                )
                args.append({"expr": normalized, "sort": sort})
            return {
                "args": [entry["expr"] for entry in args],
                "kind": kind,
                "tag": tag,
            }, "ref"
        if kind == "input_anchors":
            exact({"anchor", "order"})
            anchor = name("anchor")
            order = node["order"]
            if order not in {"operand", "canonical_unique"}:
                raise Refusal(f"{where} has unknown order mode")
            profiles = {
                member if isinstance(member, str) else member["profile"]
                for member in context["consumes"]
            }
            for profile in profiles:
                require_anchor(profile, anchor)
            return {"anchor": anchor, "kind": kind, "order": order}, "refs"
        if kind == "messages":
            exact({"role"})
            role = name("role")
            if role not in context["messages"]:
                raise Refusal(f"{where} cites unknown message role {role!r}")
            return {"kind": kind, "role": role}, "refs"
        if kind == "parameter_refs":
            exact({"name"})
            parameter = name("name")
            if context["parameters"].get(parameter) != "material_ref_vector":
                raise Refusal(f"{where} parameter_refs has incompatible sort")
            return {"kind": kind, "name": parameter}, "refs"
        if kind == "list":
            exact({"items"})
            if not isinstance(node["items"], list):
                raise Refusal(f"{where} list items must be an array")
            items = []
            for item in node["items"]:
                normalized, sort = self._normalize_material_expr(
                    contract_name, item, context, depth + 1, counter
                )
                if sort != "ref":
                    raise Refusal(f"{where} list accepts only RefExpr items")
                items.append(normalized)
            return {"items": items, "kind": kind}, "refs"
        if kind == "input_descriptor":
            exact({"input"})
            input_profile(node["input"])
            return {"input": node["input"], "kind": kind}, "claim"
        if kind == "input_descriptors":
            exact({"order"})
            order = node["order"]
            if order not in {"operand", "canonical_unique"}:
                raise Refusal(f"{where} has unknown order mode")
            return {"kind": kind, "order": order}, "claims"
        if kind == "parameter_atom":
            exact({"name"})
            parameter = name("name")
            if context["parameters"].get(parameter) != "atom":
                raise Refusal(f"{where} parameter_atom has incompatible sort")
            return {"kind": kind, "name": parameter}, "atom"
        if kind == "literal":
            exact({"value"})
            check_atom_domain(node["value"])
            return {"kind": kind, "value": node["value"]}, "atom"
        raise Refusal(f"{where} has unknown constructor {kind!r}")

    def _reduction(self, name: str, body: Any) -> dict[str, Any]:
        if not isinstance(body, dict):
            raise Refusal(f"reduction contract {name!r} must be an object")
        _closed(
            body,
            {
                "consumes",
                "dep_slots",
                "rounds",
                "parameters",
                "checks",
                "constraints",
                "outputs",
            },
            f"reduction contract {name!r}",
        )

        consumes = []
        if not isinstance(body["consumes"], list):
            raise Refusal(f"reduction contract {name!r} consumes is not an array")
        for member in body["consumes"]:
            if isinstance(member, str) and member:
                consumes.append(member)
            elif isinstance(member, dict) and set(member) == {"profile", "min"}:
                if (
                    not isinstance(member["profile"], str)
                    or not member["profile"]
                    or type(member["min"]) is not int
                    or not 1 <= member["min"] <= 1 << 20
                ):
                    raise Refusal(f"reduction contract {name!r} has bad consume pattern")
                consumes.append({"min": member["min"], "profile": member["profile"]})
            else:
                raise Refusal(f"reduction contract {name!r} has bad consume pattern")
        if not consumes or (
            any(isinstance(member, dict) for member in consumes) and len(consumes) != 1
        ):
            raise Refusal(f"reduction contract {name!r} has invalid consume arity")
        for member in consumes:
            profile = member if isinstance(member, str) else member["profile"]
            if profile not in self.profiles:
                raise Refusal(f"reduction contract {name!r} cites unknown profile")

        dep_slots = []
        dep_roles: set[str] = set()
        if not isinstance(body["dep_slots"], list):
            raise Refusal(f"reduction contract {name!r} dep_slots is not an array")
        for index, slot in enumerate(body["dep_slots"]):
            where = f"reduction contract {name!r} dep slot {index}"
            if not isinstance(slot, dict):
                raise Refusal(f"{where} is not an object")
            if set(slot) != {"role", "source", "class"}:
                raise Refusal(f"{where} has wrong fields")
            if (
                not isinstance(slot["role"], str)
                or not slot["role"]
                or slot["role"] in dep_roles
                or slot["source"]
                not in {
                    "any",
                    "public_bind",
                    "prover_slot",
                    "challenge_capability",
                }
                or not isinstance(slot["class"], str)
                or not slot["class"]
                or slot["class"] == "chal"
            ):
                raise Refusal(f"{where} is invalid")
            dep_roles.add(slot["role"])
            normalized_slot = {
                "class": slot["class"],
                "role": slot["role"],
                "source": slot["source"],
            }
            dep_slots.append(normalized_slot)

        rounds = []
        round_challenge_uses: set[str] = set()
        message_counts: dict[str, dict[str, Any]] = {}
        has_variadic_consume = len(consumes) == 1 and isinstance(
            consumes[0], dict
        )
        if not isinstance(body["rounds"], list):
            raise Refusal(f"reduction contract {name!r} rounds is not an array")
        if not body["rounds"]:
            raise Refusal(f"reduction contract {name!r} has no rounds")
        for index, round_ in enumerate(body["rounds"]):
            where = f"reduction contract {name!r} round {index}"
            if not isinstance(round_, dict) or set(round_) not in (
                {"challenge_use", "messages"},
                {"challenge_use", "messages", "kind"},
            ):
                raise Refusal(f"{where} has wrong fields")
            challenge_use = round_["challenge_use"]
            if (
                not isinstance(challenge_use, dict)
                or set(challenge_use) - {"role", "count"}
                or "role" not in challenge_use
            ):
                raise Refusal(f"{where} has invalid challenge_use")
            challenge_role = challenge_use["role"]
            dep = next(
                (slot for slot in dep_slots if slot["role"] == challenge_role),
                None,
            )
            if (
                dep is None
                or not isinstance(challenge_role, str)
                or not challenge_role
                or challenge_role in round_challenge_uses
            ):
                raise Refusal(f"{where} has invalid challenge-use role")
            round_challenge_uses.add(challenge_role)
            normalized_challenge_use = {"role": challenge_role}
            if "count" in challenge_use:
                count = challenge_use["count"]
                if type(count) is not int or not 2 <= count <= 1 << 20:
                    raise Refusal(f"{where} has invalid challenge-use count")
                normalized_challenge_use["count"] = count
            messages = []
            if not isinstance(round_["messages"], list):
                raise Refusal(f"{where} messages is not an array")
            for message in round_["messages"]:
                if (
                    not isinstance(message, dict)
                    or set(message) != {"role", "count"}
                    or not isinstance(message["role"], str)
                    or not message["role"]
                    or message["role"] in dep_roles
                    or message["role"] in message_counts
                ):
                    raise Refusal(f"{where} has invalid message role")
                multiplicity = message["count"]
                if not isinstance(multiplicity, dict):
                    raise Refusal(f"{where} message count is not a tagged object")
                if set(multiplicity) == {"exact"}:
                    exact = multiplicity["exact"]
                    if type(exact) is not int or not 1 <= exact <= 1 << 20:
                        raise Refusal(f"{where} has invalid exact message count")
                    normalized_count = {"exact": exact}
                elif set(multiplicity) == {"same_as"}:
                    if multiplicity["same_as"] != "consumed_claims":
                        raise Refusal(f"{where} has unknown dynamic message count")
                    if not has_variadic_consume:
                        raise Refusal(
                            f"{where} uses consumed_claims without exactly one "
                            "variadic consume pattern"
                        )
                    normalized_count = {"same_as": "consumed_claims"}
                else:
                    raise Refusal(f"{where} has malformed tagged message count")
                message_counts[message["role"]] = normalized_count
                messages.append(
                    {"count": normalized_count, "role": message["role"]}
                )
            normalized_round = {
                "challenge_use": normalized_challenge_use,
                "messages": messages,
            }
            if "kind" in round_:
                if (
                    not isinstance(round_["kind"], str)
                    or not round_["kind"]
                    or not all(
                        0x20 <= ord(char) <= 0x7E for char in round_["kind"]
                    )
                ):
                    raise Refusal(f"{where} has invalid kind")
                normalized_round["kind"] = round_["kind"]
            rounds.append(normalized_round)
        if not isinstance(body["parameters"], dict):
            raise Refusal(f"reduction contract {name!r} parameters is not an object")
        parameters = {}
        for parameter, sort in sorted(body["parameters"].items()):
            if (
                not isinstance(parameter, str)
                or not parameter
                or not all(0x20 <= ord(char) <= 0x7E for char in parameter)
                or sort not in {"atom", "material_ref", "material_ref_vector"}
            ):
                raise Refusal(f"reduction contract {name!r} has invalid parameter")
            parameters[parameter] = sort

        context = {
            "consumes": consumes,
            "deps": {slot["role"]: slot for slot in dep_slots},
            "messages": message_counts,
            "parameters": parameters,
        }
        checks = {}
        if not isinstance(body["checks"], dict):
            raise Refusal(f"reduction contract {name!r} checks is not an object")
        for role, slot in sorted(body["checks"].items()):
            where = f"reduction contract {name!r} check {role!r}"
            if (
                not isinstance(role, str)
                or not role
                or not all(0x20 <= ord(char) <= 0x7E for char in role)
                or not isinstance(slot, dict)
            ):
                raise Refusal(f"{where} is invalid")
            required = {"contract", "parameters", "attachments"}
            allowed = required | {"transparent_predicate"}
            if set(slot) - allowed or not required <= set(slot):
                raise Refusal(f"{where} has wrong fields")
            check_id = slot["contract"]
            check_contract = self.contracts.get(check_id)
            if check_contract is None:
                raise Refusal(f"{where} cites unknown CheckContract")
            if not isinstance(slot["parameters"], dict) or sorted(slot["parameters"]) != check_contract["parameters"]:
                raise Refusal(f"{where} does not pin exact check parameters")
            check_atom_domain(slot["parameters"])
            transparent = check_contract["mode"] == "transparent"
            if transparent != ("transparent_predicate" in slot):
                raise Refusal(f"{where} has wrong transparent-predicate mode")
            normalized_slot = {
                "attachments": [],
                "contract": check_id,
                "parameters": dict(slot["parameters"]),
            }
            if transparent:
                predicate = slot["transparent_predicate"]
                check_domain(predicate)
                if not isinstance(predicate, list) or not predicate:
                    raise Refusal(f"{where} has malformed transparent predicate")
                normalized_slot["transparent_predicate"] = predicate
            if not isinstance(slot["attachments"], list):
                raise Refusal(f"{where} attachments is not an array")
            targets: set[tuple[str, str]] = set()
            semantic_coverage: set[str] = set()
            operand_roles = {entry["role"] for entry in check_contract["operands"]}
            semantic_roles = set(check_contract["semantic_parameters"])
            for attachment in slot["attachments"]:
                if not isinstance(attachment, dict):
                    raise Refusal(f"{where} attachment is not an object")
                _closed(attachment, {"kind", "source", "target_role"}, where)
                attachment_kind = attachment["kind"]
                target = attachment["target_role"]
                if attachment_kind not in {
                    "semantic_parameter",
                    "material_ref_equality",
                    "value_identity",
                    "material_ref_vector_equality",
                    "common_material_ref_equality",
                } or not isinstance(target, str) or not target:
                    raise Refusal(f"{where} has invalid attachment")
                source, source_sort = self._normalize_material_expr(
                    name, attachment["source"], context
                )
                expected_sort = (
                    "refs"
                    if attachment_kind in {
                        "material_ref_vector_equality",
                        "common_material_ref_equality",
                    }
                    else "ref"
                )
                if source_sort != expected_sort:
                    raise Refusal(f"{where} attachment source has wrong sort")
                if attachment_kind == "semantic_parameter":
                    if target not in semantic_roles:
                        raise Refusal(f"{where} targets unknown semantic parameter")
                    semantic_coverage.add(target)
                elif target not in operand_roles:
                    raise Refusal(f"{where} targets unknown operand role")
                elif attachment_kind in {
                    "material_ref_equality",
                    "value_identity",
                    "common_material_ref_equality",
                }:
                    operand = next(
                        entry
                        for entry in check_contract["operands"]
                        if entry["role"] == target
                    )
                    if operand["multiplicity"] != {"exact": 1}:
                        raise Refusal(f"{where} requires an exactly-one target")
                if attachment_kind == "value_identity" and source["kind"] not in {"dependency", "message"}:
                    raise Refusal(f"{where} value identity needs a local-value selector")
                target_key = (
                    "semantic" if attachment_kind == "semantic_parameter" else "operand",
                    target,
                )
                if target_key in targets:
                    raise Refusal(f"{where} attaches one target twice")
                targets.add(target_key)
                normalized_slot["attachments"].append(
                    {"kind": attachment_kind, "source": source, "target_role": target}
                )
            normalized_slot["attachments"].sort(key=canon_json)
            if semantic_coverage != semantic_roles:
                raise Refusal(f"{where} does not cover every semantic parameter")
            checks[role] = normalized_slot

        constraints = []
        if not isinstance(body["constraints"], list):
            raise Refusal(f"reduction contract {name!r} constraints is not an array")
        seen_constraints: set[str] = set()
        for constraint in body["constraints"]:
            if not isinstance(constraint, dict):
                raise Refusal(f"reduction contract {name!r} constraint is not an object")
            _closed(constraint, {"kind", "left", "right"}, f"reduction contract {name!r} constraint")
            if constraint["kind"] != "equal":
                raise Refusal(f"reduction contract {name!r} has unknown constraint")
            node_count = [0]
            left, left_sort = self._normalize_material_expr(
                name, constraint["left"], context, counter=node_count
            )
            right, right_sort = self._normalize_material_expr(
                name, constraint["right"], context, counter=node_count
            )
            if left_sort != right_sort or left == right:
                raise Refusal(f"reduction contract {name!r} has ill-sorted or tautological constraint")
            if canon_json(right) < canon_json(left):
                left, right = right, left
            normalized = {"kind": "equal", "left": left, "right": right}
            spelling = canon_json(normalized)
            if spelling in seen_constraints:
                raise Refusal(f"reduction contract {name!r} repeats a constraint")
            seen_constraints.add(spelling)
            constraints.append(normalized)
        constraints.sort(key=canon_json)

        outputs = []
        if not isinstance(body["outputs"], list) or not body["outputs"]:
            raise Refusal(f"reduction contract {name!r} outputs is empty")
        # Exactly one, and the reason is on the judgment side: a derivation
        # site names one output position, so several outputs would offer one
        # site per output with every conclusion carrying the whole reduction's
        # error, and nothing constrains that direction.
        if len(body["outputs"]) != 1:
            raise Refusal(
                f"reduction contract {name!r} produces "
                f"{len(body['outputs'])} claims; a reduction contract produces "
                "exactly one, because a derivation site names one output "
                "position")
        for index, output in enumerate(body["outputs"]):
            where = f"reduction contract {name!r} output {index}"
            if not isinstance(output, dict):
                raise Refusal(f"{where} is not an object")
            _closed(output, {"profile", "anchors"}, where)
            profile = output["profile"]
            admitted = self.profiles.get(profile)
            if admitted is None or not isinstance(output["anchors"], dict):
                raise Refusal(f"{where} has unknown profile or malformed anchors")
            # The faithfulness gate: a produced claim descriptor must say what
            # it is about, or one anchorless constant composes with every
            # consumer at the link boundary.  Source profiles stay free to be
            # anchorless; an entry claim's anchors are declared by its author.
            if not admitted["anchors"]:
                raise Refusal(
                    f"{where} produces anchorless profile {profile!r}; a "
                    "produced claim descriptor must say what it is about")
            if sorted(output["anchors"]) != admitted["anchors"]:
                raise Refusal(f"{where} does not construct every exact anchor")
            anchors = {}
            for anchor, expression in sorted(output["anchors"].items()):
                normalized, sort = self._normalize_material_expr(name, expression, context)
                if sort != "ref":
                    raise Refusal(f"{where} anchor constructor is not RefExpr")
                anchors[anchor] = normalized
            outputs.append({"anchors": anchors, "profile": profile})

        return {
            "checks": checks,
            "constraints": constraints,
            "consumes": consumes,
            "dep_slots": dep_slots,
            "outputs": outputs,
            "parameters": parameters,
            "rounds": rounds,
        }

    def _rule(self, name: str, body: Any) -> dict[str, Any]:
        if not isinstance(body, dict):
            raise Refusal(f"terminal rule {name!r} must be an object")
        allowed = {
            "claim_profile",
            "producer",
            "checks",
            "transparent_predicates",
            "attachments",
        }
        if set(body) - allowed or not (allowed - {"producer"}) <= set(body):
            raise Refusal(f"terminal rule {name!r} has wrong fields")
        attachments = sorted(
            (dict(attachment) for attachment in body["attachments"]),
            key=canon_json,
        )
        result = {
            "attachments": attachments,
            "checks": dict(body["checks"]),
            "claim_profile": body["claim_profile"],
            "transparent_predicates": dict(body["transparent_predicates"]),
        }
        if body["claim_profile"] not in self.profiles:
            raise Refusal(f"terminal rule {name!r} cites unknown claim profile")
        if not isinstance(body["checks"], dict) or not all(
            isinstance(role, str)
            and role
            and isinstance(contract, str)
            and contract in self.contracts
            for role, contract in body["checks"].items()
        ):
            raise Refusal(f"terminal rule {name!r} has invalid check map")
        if not isinstance(body["transparent_predicates"], dict):
            raise Refusal(f"terminal rule {name!r} has invalid predicate map")
        producer_contract = None
        if "producer" in body:
            if not isinstance(body["producer"], dict) or set(body["producer"]) != {
                "contract",
                "output",
            }:
                raise Refusal(f"terminal rule {name!r} has malformed producer pin")
            result["producer"] = {
                "output": body["producer"]["output"],
                "contract": body["producer"]["contract"],
            }
            producer_contract = self.reductions.get(body["producer"]["contract"])
            output = body["producer"]["output"]
            if (
                producer_contract is None
                or type(output) is not int
                or not 0 <= output < len(producer_contract["outputs"])
                or producer_contract["outputs"][output]["profile"]
                != body["claim_profile"]
            ):
                raise Refusal(f"terminal rule {name!r} has invalid producer pin")
        for attachment in attachments:
            source = (
                attachment.get("source")
                if isinstance(attachment, dict)
                else None
            )
            if (
                not isinstance(source, dict)
                or source.get("kind") != "producer_message"
            ):
                continue
            if producer_contract is None:
                raise Refusal(
                    f"terminal rule {name!r} selects a producer message without "
                    "a producer pin"
                )
            role = source.get("role")
            index = source.get("index")
            multiplicity = next(
                (
                    message["count"]
                    for round_ in producer_contract["rounds"]
                    for message in round_["messages"]
                    if message["role"] == role
                ),
                None,
            )
            if multiplicity is None:
                raise Refusal(
                    f"terminal rule {name!r} selects an unknown producer message"
                )
            if _message_count_is_dynamic(multiplicity):
                raise Refusal(
                    f"terminal rule {name!r} cannot select one producer message "
                    "from a dynamic message role"
                )
            if type(index) is not int or not 0 <= index < multiplicity["exact"]:
                raise Refusal(
                    f"terminal rule {name!r} selects an unknown producer message"
                )
        return result

    def digest_for(self, section: str, name: str) -> str:
        tables = {
            "claim_profiles": self.profile_digests,
            "check_contracts": self.contract_digests,
            "hole_contracts": self.hole_contract_digests,
            "reduction_contracts": self.reduction_digests,
            "terminal_rules": self.rule_digests,
        }
        try:
            return tables[section][name]
        except KeyError:
            raise Refusal(f"unresolved {section} citation {name!r}") from None


VOCABULARY = ProtocolVocabulary.load(REGISTRY / "protocol-vocabulary.json")


def _load_registry(name: str) -> dict[str, Any]:
    return load_json((REGISTRY / name).read_text(encoding="utf-8"))


_CONSTRUCTION_DOCUMENT = _load_registry("construction-profiles.json")


def construction_profiles_document() -> dict[str, Any]:
    """Normalize the current construction-profile registry envelope."""

    _closed(
        _CONSTRUCTION_DOCUMENT,
        {"registry", "sponges", "codecs"},
        "construction profile registry",
    )
    if _CONSTRUCTION_DOCUMENT["registry"] != "zkc.construction_profiles":
        raise Refusal("unsupported construction-profile envelope")
    sponges = _CONSTRUCTION_DOCUMENT["sponges"]
    codecs = _CONSTRUCTION_DOCUMENT["codecs"]
    if not isinstance(sponges, dict) or not isinstance(codecs, dict):
        raise Refusal("construction-profile sections must be objects")
    for name, body in sponges.items():
        if not isinstance(name, str) or not isinstance(body, dict):
            raise Refusal("sponge profiles need string names and object bodies")
        _closed(body, {"alphabet_order", "capacity", "rate"}, f"sponge {name!r}")
        alphabet = body.get("alphabet_order")
        if (
            not isinstance(alphabet, str)
            or not alphabet.isascii()
            or not alphabet.isdecimal()
            or alphabet.startswith("0")
            or int(alphabet) < 2
        ):
            raise Refusal(f"sponge {name!r} has no exact alphabet order")
        for dimension in ("capacity", "rate"):
            value = body.get(dimension)
            if type(value) is not int or not 1 <= value <= 4096:
                raise Refusal(f"sponge {name!r} has invalid {dimension}")
    for name, body in codecs.items():
        if not isinstance(name, str) or not isinstance(body, dict):
            raise Refusal("codec profiles need string names and object bodies")
        unknown = set(body) - {"squeeze"}
        if unknown:
            raise Refusal(f"codec {name!r} has unknown={sorted(unknown)}")
        if "squeeze" not in body:
            continue
        squeeze = body["squeeze"]
        if not isinstance(squeeze, dict):
            raise Refusal(f"codec {name!r} squeeze is not an object")
        _closed(squeeze, {"kind", "symbols"}, f"codec {name!r} squeeze")
        if squeeze.get("kind") not in {"mod_reduce", "tuple_bijection"}:
            raise Refusal(f"codec {name!r} has unknown squeeze kind")
        symbols = squeeze.get("symbols")
        if type(symbols) is not int or not 1 <= symbols <= 4096:
            raise Refusal(f"codec {name!r} has invalid squeeze symbols")
    return {
        "codecs": {name: dict(body) for name, body in codecs.items()},
        "sponges": {name: dict(body) for name, body in sponges.items()},
    }


def construction_codec_bias(
    sponge_name: str, codec_name: str, challenge_space: str
) -> dict[str, str]:
    """Independently derive one construction-profile squeeze bias.

    tuple_bijection is deliberately stricter than modulo sampling: an exact
    alphabet-coordinate tuple is a uniform draw only for the target it
    bijects with.  A different target is unsupported, never silently reduced.
    """

    construction_profiles_document()
    try:
        sponge = _CONSTRUCTION_DOCUMENT["sponges"][sponge_name]
        squeeze = _CONSTRUCTION_DOCUMENT["codecs"][codec_name]["squeeze"]
    except KeyError as error:
        raise Refusal("unresolved sponge or squeezing codec profile") from error
    if (
        not isinstance(challenge_space, str)
        or not challenge_space.isascii()
        or not challenge_space.isdecimal()
    ):
        raise Refusal("challenge space is not a decimal natural")
    q = int(challenge_space)
    if q < 2:
        raise Refusal("challenge space must contain at least two elements")
    domain = int(sponge["alphabet_order"]) ** squeeze["symbols"]
    if squeeze["kind"] == "tuple_bijection":
        if q != domain:
            raise Refusal(
                "tuple_bijection requires challenge space exactly equal to "
                f"alphabet_order^symbols (expected {domain}, got {q})"
            )
        bias = Fraction(0)
    else:
        if q > domain:
            raise Refusal("challenge space exceeds the codec squeeze domain")
        residue = domain % q
        bias = Fraction(residue * (q - residue), domain * q)
    return {
        "bias_denominator": str(bias.denominator),
        "bias_numerator": str(bias.numerator),
        "domain": str(domain),
        "kind": squeeze["kind"],
    }


def _advantage_ids(term: Any) -> list[str]:
    if not isinstance(term, dict):
        return []
    result: list[str] = []
    adv = term.get("adv")
    if isinstance(adv, dict) and isinstance(adv.get("assumption"), str):
        result.append(adv["assumption"])
    for value in term.values():
        if isinstance(value, dict):
            result.extend(_advantage_ids(value))
        elif isinstance(value, list):
            for member in value:
                result.extend(_advantage_ids(member))
    return result


_RESERVED_LATTICE_NODES = {
    "special_soundness": ("ss", "soundness"),
    "computational_special_soundness": ("computational_ss", "knowledge"),
    "rbr_soundness": ("rbr", "soundness"),
    "rbr_knowledge": ("rbr", "knowledge"),
    "sr_soundness": ("sr", "soundness"),
    "sr_knowledge": ("sr", "knowledge"),
    "fs_soundness": ("fs", "soundness"),
    "fs_knowledge": ("fs", "knowledge"),
}


def _reserved_near_spelling(node: Any) -> bool:
    return (
        isinstance(node, str)
        and node not in _RESERVED_LATTICE_NODES
        and node.startswith(
            (
                "rbr_",
                "sr_",
                "fs_",
                "special_soundness",
                "computational_special_soundness",
            )
        )
    )


def _term_children(term: Any, constructor: str) -> list[Any] | None:
    if not isinstance(term, dict) or set(term) != {constructor}:
        return None
    children = term[constructor]
    return children if isinstance(children, list) else None


def _is_rat(term: Any, numerator: str, denominator: str) -> bool:
    return term == {"rat": [numerator, denominator]}


def _is_prem(term: Any, component: str, *, indexed: bool) -> bool:
    if not isinstance(term, dict) or set(term) != {"prem"}:
        return False
    selector = term["prem"]
    if not isinstance(selector, dict) or selector.get("premise") != 0:
        return False
    if selector.get("component") != component:
        return False
    index = selector.get("index")
    return isinstance(index, str) and bool(index) if indexed else "index" not in selector


def _premise_read_count(term: Any) -> int:
    if not isinstance(term, dict):
        return 0
    count = 1 if set(term) == {"prem"} else 0
    for value in term.values():
        if isinstance(value, dict):
            count += _premise_read_count(value)
        elif isinstance(value, list):
            count += sum(_premise_read_count(member) for member in value)
    return count


def _contains_constructor(term: Any, constructor: str) -> bool:
    if not isinstance(term, dict):
        return False
    if set(term) == {constructor}:
        return True
    return any(
        _contains_constructor(member, constructor)
        for value in term.values()
        for member in (value if isinstance(value, list) else [value])
        if isinstance(member, dict)
    )


def _exact_duplex_loss() -> dict[str, Any]:
    """The one SR-to-FS theorem formula admitted by the v0 vocabulary."""

    return {
        "add": [
            {"prem": {"premise": 0, "component": "composed"}},
            {
                "div": [
                    {
                        "mul": [
                            {"rat": ["25", "1"]},
                            {"pow": [{"sym": "t"}, {"rat": ["2", "1"]}]},
                        ]
                    },
                    {
                        "pow": [
                            {"param": "alphabet_order"},
                            {"param": "capacity"},
                        ]
                    },
                ]
            },
            {"mul": [{"sym": "t"}, {"param": "codec_bias_max"}]},
            {"param": "codec_bias_sum"},
        ]
    }


def construction_digest(name: str) -> str:
    if name.startswith("sponge:"):
        bare = name.removeprefix("sponge:")
        try:
            body = _CONSTRUCTION_DOCUMENT["sponges"][bare]
        except KeyError:
            raise Refusal(f"unknown sponge profile {bare!r}") from None
        return tagged_digest("zkc/profile-sponge\n", body)
    if name.startswith("codec:"):
        bare = name.removeprefix("codec:")
        try:
            body = _CONSTRUCTION_DOCUMENT["codecs"][bare]
        except KeyError:
            raise Refusal(f"unknown codec profile {bare!r}") from None
        return tagged_digest("zkc/profile-codec\n", body)
    raise Refusal(f"unknown construction citation namespace {name!r}")


class Source(NamedTuple):
    label: str
    profile: str
    anchors: dict[str, str]


class Bind(NamedTuple):
    tag: str
    label: str
    payload_class: str
    stage: str
    value: str | None


class Slot(NamedTuple):
    tag: str
    label: str
    payload_class: str
    absorbed: bool
    membership: tuple[str, str, int] | None
    binding: str | None = None


class Chal(NamedTuple):
    tag: str
    label: str
    payload_class: str
    domain: str
    space: str
    deps: list[str]
    mode: list[str] | None = None


class Check(NamedTuple):
    tag: str
    label: str
    contract: str
    inputs: list[str]
    params: dict[str, Any]
    semantic_args: dict[str, Any]
    expr: list[Any] | None


class Reduce(NamedTuple):
    label: str
    contract: str
    consumed: list[str]
    deps: list[str]
    produced: list[tuple[str, str]]
    params: dict[str, Any]
    anchors: list[dict[str, str]]
    checks: dict[str, str]


class MaterialBinding(NamedTuple):
    value: str
    semantic_ref: str


class Discharge(NamedTuple):
    tag: str
    claim: str
    rule: str
    checks: dict[str, str]


class Route(NamedTuple):
    tag: str
    claim: str
    route: str


def source(label: str, profile: str, anchors: dict[str, str]) -> Source:
    return Source(label, profile, dict(anchors))


def bind(label: str, payload_class: str, stage: str, value: str | None = None) -> Bind:
    return Bind("bind", label, payload_class, stage, value)


def slot(
    label: str,
    payload_class: str,
    absorbed: bool,
    membership: tuple[str, str, int] | tuple[str, str] | None = None,
    binding: str | None = None,
) -> Slot:
    if membership is not None and len(membership) == 2:
        membership = (membership[0], membership[1], 0)
    return Slot("slot", label, payload_class, absorbed, membership, binding)


def chal(
    label: str,
    payload_class: str,
    domain: str,
    space: str,
    deps: tuple[str, ...] | list[str] = (),
    mode: list[str] | None = None,
) -> Chal:
    return Chal("chal", label, payload_class, domain, space, list(deps), mode)


def check(
    label: str,
    contract: str,
    inputs: tuple[str, ...] | list[str] = (),
    *,
    params: dict[str, Any] | None = None,
    semantic_args: dict[str, Any] | None = None,
    expr: list[Any] | None = None,
) -> Check:
    return Check(
        "check",
        label,
        contract,
        list(inputs),
        dict(params or {}),
        dict(semantic_args or {}),
        expr,
    )


def reduce_row(
    label: str,
    contract: str,
    consumed: list[str],
    deps: list[str],
    produced: list[tuple[str, str]],
    *,
    checks: dict[str, str] | None = None,
    params: dict[str, Any] | None = None,
    anchors: list[dict[str, str]] | None = None,
) -> Reduce:
    return Reduce(
        label,
        contract,
        list(consumed),
        list(deps),
        list(produced),
        dict(params or {}),
        [dict(anchor) for anchor in (anchors or [{} for _ in produced])],
        dict(checks or {}),
    )


def material(value: str, semantic_ref: str) -> MaterialBinding:
    return MaterialBinding(value, semantic_ref)


def discharge(claim: str, rule: str, checks: dict[str, str]) -> Discharge:
    return Discharge("discharge", claim, rule, dict(checks))


def route(kind: str, claim: str, target: str) -> Route:
    if kind not in {"export", "assume", "residual"}:
        raise ValueError(f"unknown route kind {kind!r}")
    return Route(kind, claim, target)


PERMITTED_SINKS = {
    "closed_proof": {"discharge"},
    "residual_artifact": {"discharge", "residual"},
    "host_exporting_artifact": {"discharge", "export"},
    "assumption_allowed_artifact": {"discharge", "assume"},
    "analysis_only_artifact": {"discharge", "export", "assume", "residual"},
}


@dataclass
class ClaimView:
    label: str
    profile: str
    anchors: dict[str, str]
    producer: Reduce | None
    output: int

    @property
    def descriptor(self) -> list[Any]:
        return [self.profile, self.anchors]

    @property
    def descriptor_bytes(self) -> bytes:
        return canon_json(self.descriptor).encode("ascii")


@dataclass
class CheckView:
    event: Check
    contract: dict[str, Any]
    roles: dict[str, list[str]]
    positions: list[tuple[str, int]]
    normalized_expr: Any


def claim_descriptor_digest(profile: str, anchors: dict[str, str]) -> str:
    return tagged_digest("zkc/claim\n", [profile, anchors])


def claim_vector_digest(descriptors: list[list[Any]]) -> str:
    ordered = sorted(descriptors, key=lambda item: canon_json(item).encode("ascii"))
    if any(left == right for left, right in zip(ordered, ordered[1:])):
        raise Refusal("producer input descriptors are not unique")
    return tagged_digest("zkc/claim-vector\n", ordered)


def _solve_layout(
    contract: dict[str, Any], inputs: list[str], value_classes: dict[str, str]
) -> list[tuple[dict[str, list[str]], list[tuple[str, int]]]]:
    answers = []

    def visit(
        segment_index: int,
        input_index: int,
        captures: dict[str, int],
        roles: dict[str, list[str]],
        positions: list[tuple[str, int]],
    ) -> None:
        if len(answers) > 1:
            return
        if segment_index == len(contract["operands"]):
            if input_index == len(inputs):
                answers.append((roles, positions))
            return
        segment = contract["operands"][segment_index]
        multiplicity = segment["multiplicity"]
        if "exact" in multiplicity:
            candidates = [multiplicity["exact"]]
        elif "same_as" in multiplicity:
            if multiplicity["same_as"] not in captures:
                return
            candidates = [captures[multiplicity["same_as"]]]
        else:
            name = multiplicity["capture"]
            if name in captures:
                candidates = [captures[name]]
            else:
                candidates = range(multiplicity["min"], len(inputs) - input_index + 1)
        for count in candidates:
            chosen = inputs[input_index : input_index + count]
            if len(chosen) != count or any(
                segment["class"] != "*"
                and value_classes.get(value) != segment["class"]
                for value in chosen
            ):
                continue
            next_captures = dict(captures)
            if "capture" in multiplicity:
                next_captures[multiplicity["capture"]] = count
            next_roles = {role: list(values) for role, values in roles.items()}
            next_roles.setdefault(segment["role"], []).extend(chosen)
            next_positions = positions + [
                (segment["role"], index) for index in range(count)
            ]
            visit(
                segment_index + 1,
                input_index + count,
                next_captures,
                next_roles,
                next_positions,
            )

    visit(0, 0, {}, {}, [])
    return answers


def _normalize_expr(node: Any, view: CheckView, depth: int = 0) -> Any:
    if depth > MAX_ATTR_DEPTH or not isinstance(node, list) or not node:
        raise Refusal("malformed transparent expression")
    if not isinstance(node[0], str):
        raise Refusal("transparent expression head is not a string")
    if node[0] == "in":
        if len(node) != 2 or type(node[1]) is not int or not 0 <= node[1] < len(
            view.positions
        ):
            raise Refusal("malformed transparent input leaf")
        role, occurrence = view.positions[node[1]]
        result = ["role", role]
        if len(view.roles[role]) != 1:
            result.append(occurrence)
        return result
    return [
        node[0],
        *[
            _normalize_expr(child, view, depth + 1)
            if isinstance(child, list)
            else child
            for child in node[1:]
        ],
    ]


def terminal_closure(
    protocol: dict[str, Any],
    vocabulary: ProtocolVocabulary,
    *,
    _return_used: bool = False,
) -> list[dict[str, Any]] | tuple[list[dict[str, Any]], set[str]]:
    """Judge typed terminal closure without consulting the C++ carrier."""

    events: list[Any] = protocol["events"]
    reduces: list[Reduce] = protocol.get("reduces", [])
    value_classes = {
        event.label: event.payload_class
        for event in events
        if isinstance(event, (Bind, Slot))
    }
    value_classes.update(
        (event.label, event.payload_class)
        for event in events
        if isinstance(event, Chal)
    )
    checks = {event.label: event for event in events if isinstance(event, Check)}

    claims: dict[str, ClaimView] = {}

    def add_claim(
        label: str,
        profile: str,
        anchors: dict[str, str],
        producer: Reduce | None,
        output: int,
    ) -> None:
        admitted = vocabulary.profiles.get(profile)
        if admitted is None:
            raise Refusal(f"claim profile {profile!r} is not admitted")
        if sorted(anchors) != sorted(admitted["anchors"]):
            raise Refusal(f"claim {label!r} disagrees with profile {profile!r}")
        if not all(isinstance(value, str) for value in anchors.values()):
            raise Refusal(f"claim {label!r} anchors must be strings")
        claims[label] = ClaimView(label, profile, dict(anchors), producer, output)

    for entry in protocol["sources"]:
        add_claim(entry.label, entry.profile, entry.anchors, None, 0)
    for reduce in reduces:
        if len(reduce.anchors) != len(reduce.produced):
            raise Refusal(f"reduce {reduce.label!r} has wrong output-anchor arity")
        for index, ((label, profile), anchors) in enumerate(
            zip(reduce.produced, reduce.anchors)
        ):
            add_claim(label, profile, anchors, reduce, index)

    check_views: dict[str, CheckView] = {}
    for event in checks.values():
        contract = vocabulary.contracts.get(event.contract)
        if contract is None:
            raise Refusal(f"check contract {event.contract!r} is not admitted")
        if sorted(event.params) != contract["parameters"]:
            raise Refusal(f"check {event.label!r} has wrong parameter names")
        if sorted(event.semantic_args) != contract["semantic_parameters"]:
            raise Refusal(f"check {event.label!r} has wrong semantic arguments")
        transparent = contract["mode"] == "transparent"
        if transparent != (event.expr is not None):
            raise Refusal(f"check {event.label!r} has wrong transparency mode")
        layouts = _solve_layout(contract, event.inputs, value_classes)
        if len(layouts) != 1:
            raise Refusal(
                f"check {event.label!r} has {len(layouts)} operand layouts"
            )
        roles, positions = layouts[0]
        view = CheckView(event, contract, roles, positions, None)
        if event.expr is not None:
            view.normalized_expr = _normalize_expr(event.expr, view)
        check_views[event.label] = view

    binding_by_value: dict[str, str] = {}
    value_by_reference: dict[str, str] = {}
    for binding in protocol.get("material_bindings", []):
        if binding.value not in value_classes:
            raise Refusal(f"material binding names unknown value {binding.value!r}")
        if not is_sha256_ref(binding.semantic_ref):
            raise Refusal("material binding target is not a sha256 reference")
        if binding.value in binding_by_value:
            raise Refusal(f"value {binding.value!r} has two material bindings")
        if binding.semantic_ref in value_by_reference:
            raise Refusal("semantic material reference has two local producers")
        binding_by_value[binding.value] = binding.semantic_ref
        value_by_reference[binding.semantic_ref] = binding.value

    messages: dict[str, dict[str, dict[int, str]]] = {}
    for event in events:
        if isinstance(event, Slot) and event.membership:
            instance, role, index = event.membership
            messages.setdefault(instance, {}).setdefault(role, {})[index] = event.label

    def ordered_inputs(view: ClaimView) -> list[ClaimView]:
        if view.producer is None:
            raise Refusal("terminal attachment requires a reduction producer")
        result = [claims[label] for label in view.producer.consumed]
        result.sort(key=lambda claim: claim.descriptor_bytes)
        if any(
            left.descriptor_bytes == right.descriptor_bytes
            for left, right in zip(result, result[1:])
        ):
            raise Refusal("producer input descriptors are not unique")
        return result

    def producer_dep(view: ClaimView, role: str) -> str:
        if view.producer is None:
            raise Refusal("terminal attachment requires a producer")
        reduction_contract = vocabulary.reductions.get(view.producer.contract)
        if reduction_contract is None:
            raise Refusal("terminal producer contract is not admitted")
        for index, dep_slot in enumerate(reduction_contract["dep_slots"]):
            if dep_slot["role"] == role and index < len(view.producer.deps):
                return view.producer.deps[index]
        raise Refusal(f"producer has no dependency role {role!r}")

    def producer_message(view: ClaimView, role: str, index: int) -> str:
        if view.producer is None:
            raise Refusal("terminal attachment requires a producer")
        try:
            return messages[view.producer.label][role][index]
        except KeyError:
            raise Refusal(f"producer has no message {role}[{index}]") from None

    used_bindings: set[str] = set()

    def binding(value: str) -> str:
        try:
            reference = binding_by_value[value]
        except KeyError:
            raise Refusal(f"check operand {value!r} has no material binding") from None
        used_bindings.add(value)
        return reference

    selected_globally: set[str] = set()
    records = []
    for sink in protocol["sinks"]:
        if not isinstance(sink, Discharge):
            continue
        rule = vocabulary.rules.get(sink.rule)
        if rule is None:
            raise Refusal(f"terminal rule {sink.rule!r} is not admitted")
        try:
            claim = claims[sink.claim]
        except KeyError:
            raise Refusal(f"discharge names unknown claim {sink.claim!r}") from None
        if claim.profile != rule["claim_profile"]:
            raise Refusal("terminal rule does not match claim profile")
        producer_pin = rule.get("producer")
        if producer_pin is not None and (
            claim.producer is None
            or claim.producer.contract != producer_pin["contract"]
            or claim.output != producer_pin["output"]
        ):
            raise Refusal("terminal rule producer pin does not match")
        if sorted(sink.checks) != sorted(rule["checks"]):
            raise Refusal("terminal check roles do not exactly match the rule")

        selected: dict[str, CheckView] = {}
        for role, expected_contract in sorted(rule["checks"].items()):
            label = sink.checks[role]
            view = check_views.get(label)
            if view is None or view.event.contract != expected_contract:
                raise Refusal(
                    f"terminal role {role!r} does not select {expected_contract!r}"
                )
            if label in selected_globally:
                raise Refusal(f"check {label!r} closes more than one discharge")
            selected_globally.add(label)
            selected[role] = view
        for role, predicate in rule["transparent_predicates"].items():
            if selected[role].normalized_expr != predicate:
                raise Refusal(f"transparent predicate for {role!r} does not match")

        def source_anchor(source: dict[str, Any]) -> str:
            if source["kind"] == "claim_anchor":
                return claim.anchors.get(source["anchor"], "")
            if source["kind"] == "producer_input_anchor":
                if claim.producer is None or not 0 <= source["input"] < len(
                    claim.producer.consumed
                ):
                    raise Refusal("producer input anchor index is out of range")
                return claims[claim.producer.consumed[source["input"]]].anchors.get(
                    source["anchor"], ""
                )
            raise Refusal("attachment source is not a scalar anchor")

        def source_anchor_vector(source: dict[str, Any]) -> list[str]:
            if source["kind"] != "producer_inputs_anchor":
                raise Refusal("attachment source is not an anchor vector")
            return [
                input_claim.anchors.get(source["anchor"], "")
                for input_claim in ordered_inputs(claim)
            ]

        def operands(check_role: str, operand_role: str) -> list[str]:
            try:
                return selected[check_role].roles[operand_role]
            except KeyError:
                raise Refusal(
                    f"selected check has no operand role {operand_role!r}"
                ) from None

        for attachment in rule["attachments"]:
            kind = attachment["kind"]
            source_spec = attachment["source"]
            if kind == "descriptor_digest":
                descriptors = [entry.descriptor for entry in ordered_inputs(claim)]
                if claim.anchors.get(attachment["anchor"]) != claim_vector_digest(
                    descriptors
                ):
                    raise Refusal("producer descriptor-vector digest does not match")
                continue
            check_role = attachment["check"]
            target_role = attachment["role"]
            if kind == "semantic_parameter":
                expected = source_anchor(source_spec)
                actual = selected[check_role].event.semantic_args.get(target_role)
                if not expected or actual != expected:
                    raise Refusal("semantic parameter attachment does not match")
            elif kind == "material_ref_equality":
                selected_operands = operands(check_role, target_role)
                expected = source_anchor(source_spec)
                if (
                    not expected
                    or len(selected_operands) != 1
                    or binding(selected_operands[0]) != expected
                ):
                    raise Refusal("material-reference attachment does not match")
            elif kind == "value_identity":
                selected_operands = operands(check_role, target_role)
                if source_spec["kind"] == "producer_dependency":
                    expected = producer_dep(claim, source_spec["role"])
                elif source_spec["kind"] == "producer_message":
                    expected = producer_message(
                        claim, source_spec["role"], source_spec["index"]
                    )
                else:
                    raise Refusal("value identity has incompatible source")
                if selected_operands != [expected]:
                    raise Refusal("SSA attachment does not match")
            elif kind == "material_ref_vector_equality":
                selected_operands = operands(check_role, target_role)
                expected = source_anchor_vector(source_spec)
                actual = [binding(value) for value in selected_operands]
                if not expected or actual != expected:
                    raise Refusal("material-reference vector does not match")
            elif kind == "common_material_ref_equality":
                selected_operands = operands(check_role, target_role)
                references = source_anchor_vector(source_spec)
                common = references[0] if references else ""
                if (
                    not common
                    or any(reference != common for reference in references)
                    or claim.anchors.get(attachment["claim_anchor"]) != common
                    or len(selected_operands) != 1
                    or binding(selected_operands[0]) != common
                ):
                    raise Refusal("common material-reference attachment does not match")
            else:
                raise Refusal(f"unknown terminal attachment kind {kind!r}")
        records.append({"claim": sink.claim, "rule": sink.rule, "checks": sink.checks})

    if _return_used:
        return records, used_bindings
    return records


def reduction_closure(
    protocol: dict[str, Any],
    vocabulary: ProtocolVocabulary,
    *,
    _return_used: bool = False,
) -> list[dict[str, Any]] | tuple[list[dict[str, Any]], set[str]]:
    """Reconstruct every exact local reduction implication.

    This traversal is purpose-specific: it does not call terminal closure and
    it does not treat a transcript-shape match as proposition evidence.
    """

    # Shape is part of ReductionClosureOK, not an ambient precondition.  Keep
    # the transcript-order derivation in its small independent helper, but run
    # it from this public judgment so direct closure callers cannot bypass it.
    _validate_contract_shape(protocol, vocabulary)

    events: list[Any] = protocol["events"]
    event_positions = {event.label: index for index, event in enumerate(events)}
    value_classes = {
        event.label: event.payload_class
        for event in events
        if isinstance(event, (Bind, Slot))
    }
    value_classes.update(
        (event.label, event.payload_class)
        for event in events
        if isinstance(event, Chal)
    )

    checks: dict[str, CheckView] = {}
    for event in (entry for entry in events if isinstance(entry, Check)):
        check_contract = vocabulary.contracts.get(event.contract)
        if check_contract is None:
            raise Refusal(f"check contract {event.contract!r} is not admitted")
        if sorted(event.params) != check_contract["parameters"]:
            raise Refusal(f"check {event.label!r} has wrong parameter names")
        if sorted(event.semantic_args) != check_contract["semantic_parameters"]:
            raise Refusal(f"check {event.label!r} has wrong semantic arguments")
        transparent = check_contract["mode"] == "transparent"
        if transparent != (event.expr is not None):
            raise Refusal(f"check {event.label!r} has wrong transparency mode")
        layouts = _solve_layout(check_contract, event.inputs, value_classes)
        if len(layouts) != 1:
            raise Refusal(f"check {event.label!r} has {len(layouts)} operand layouts")
        roles, positions = layouts[0]
        view = CheckView(event, check_contract, roles, positions, None)
        if event.expr is not None:
            view.normalized_expr = _normalize_expr(event.expr, view)
        checks[event.label] = view

    claims: dict[str, ClaimView] = {}
    for entry in protocol["sources"]:
        claims[entry.label] = ClaimView(
            entry.label, entry.profile, dict(entry.anchors), None, 0
        )
    for reduce in protocol.get("reduces", []):
        for index, ((label, profile), anchors) in enumerate(
            zip(reduce.produced, reduce.anchors)
        ):
            claims[label] = ClaimView(label, profile, dict(anchors), reduce, index)

    messages: dict[str, dict[str, dict[int, str]]] = {}
    for event in events:
        if not isinstance(event, Slot) or event.membership is None:
            continue
        instance, role, index = event.membership
        occurrences = messages.setdefault(instance, {}).setdefault(role, {})
        if index in occurrences:
            raise Refusal(f"reduction message {instance}.{role}[{index}] is duplicated")
        occurrences[index] = event.label

    binding_by_value: dict[str, str] = {}
    value_by_reference: dict[str, str] = {}
    for binding_entry in protocol.get("material_bindings", []):
        if binding_entry.value not in value_classes:
            raise Refusal(f"material binding names unknown value {binding_entry.value!r}")
        if not is_sha256_ref(binding_entry.semantic_ref):
            raise Refusal("material binding target is not a sha256 reference")
        if binding_entry.value in binding_by_value:
            raise Refusal(f"value {binding_entry.value!r} has two material bindings")
        if binding_entry.semantic_ref in value_by_reference:
            raise Refusal("semantic material reference has two local producers")
        binding_by_value[binding_entry.value] = binding_entry.semantic_ref
        value_by_reference[binding_entry.semantic_ref] = binding_entry.value

    _, normalized_reduces, _, transformer_positions = _normalized_transformers(protocol)
    used_bindings: set[str] = set()
    selected_checks: set[str] = set()
    records = []

    for reduce in normalized_reduces:
        contract = vocabulary.reductions.get(reduce.contract)
        if contract is None:
            raise Refusal(f"reduce {reduce.label!r} cites unknown contract")
        if sorted(reduce.params) != sorted(contract["parameters"]):
            raise Refusal(f"reduce {reduce.label!r} has wrong parameter names")
        for parameter, sort in contract["parameters"].items():
            value = reduce.params[parameter]
            if sort == "material_ref" and not is_sha256_ref(value):
                raise Refusal(f"reduce {reduce.label!r} has invalid MaterialRef parameter")
            if sort == "material_ref_vector" and not (
                isinstance(value, list) and all(is_sha256_ref(member) for member in value)
            ):
                raise Refusal(
                    f"reduce {reduce.label!r} has invalid MaterialRefVector parameter"
                )
            if sort == "atom":
                check_atom_domain(value)

        try:
            input_claims = [claims[label] for label in reduce.consumed]
        except KeyError as error:
            raise Refusal(
                f"reduce {reduce.label!r} consumes unknown claim {error.args[0]!r}"
            ) from None
        dep_by_role = {
            slot["role"]: label
            for slot, label in zip(contract["dep_slots"], reduce.deps)
        }
        instance_messages = messages.get(reduce.label, {})

        def ordered_inputs(order: str) -> list[ClaimView]:
            result = list(input_claims)
            if order == "operand":
                return result
            result.sort(key=lambda claim: claim.descriptor_bytes)
            if any(
                left.descriptor_bytes == right.descriptor_bytes
                for left, right in zip(result, result[1:])
            ):
                raise Refusal(
                    f"reduce {reduce.label!r} canonical_unique inputs are not unique"
                )
            return result

        def binding(value: str) -> str:
            try:
                result = binding_by_value[value]
            except KeyError:
                raise Refusal(
                    f"reduction material value {value!r} has no MaterialBinding"
                ) from None
            used_bindings.add(value)
            return result

        def local_value(node: dict[str, Any]) -> str:
            if node["kind"] == "dependency":
                try:
                    return dep_by_role[node["role"]]
                except KeyError:
                    raise Refusal("reduction attachment has unknown dependency") from None
            if node["kind"] == "message":
                try:
                    return instance_messages[node["role"]][node["occurrence"]]
                except KeyError:
                    raise Refusal("reduction attachment has unknown message") from None
            raise Refusal("value identity source is not a local-value selector")

        def evaluate(node: dict[str, Any]) -> tuple[str, Any]:
            kind = node["kind"]
            if kind == "literal_ref":
                return "ref", node["value"]
            if kind == "input_anchor":
                try:
                    return "ref", input_claims[node["input"]].anchors[node["anchor"]]
                except (IndexError, KeyError):
                    raise Refusal("reduction input anchor does not resolve") from None
            if kind in {"dependency", "message"}:
                return "ref", binding(local_value(node))
            if kind == "parameter_ref":
                return "ref", reduce.params[node["name"]]
            if kind == "construct":
                typed_args = []
                for argument in node["args"]:
                    sort, value = evaluate(argument)
                    typed_args.append([sort, value])
                return "ref", material_construct(node["tag"], typed_args)
            if kind == "input_anchors":
                return "refs", [
                    claim.anchors[node["anchor"]]
                    for claim in ordered_inputs(node["order"])
                ]
            if kind == "messages":
                try:
                    occurrences = instance_messages[node["role"]]
                    labels = [occurrences[index] for index in range(len(occurrences))]
                except KeyError:
                    raise Refusal("reduction message vector does not resolve") from None
                return "refs", [binding(label) for label in labels]
            if kind == "parameter_refs":
                return "refs", list(reduce.params[node["name"]])
            if kind == "list":
                values = []
                for item in node["items"]:
                    sort, value = evaluate(item)
                    if sort != "ref":
                        raise Refusal("reduction list contains a non-reference")
                    values.append(value)
                return "refs", values
            if kind == "input_descriptor":
                try:
                    return "claim", input_claims[node["input"]].descriptor
                except IndexError:
                    raise Refusal("reduction input descriptor does not resolve") from None
            if kind == "input_descriptors":
                return "claims", [
                    claim.descriptor for claim in ordered_inputs(node["order"])
                ]
            if kind == "parameter_atom":
                return "atom", reduce.params[node["name"]]
            if kind == "literal":
                return "atom", node["value"]
            raise Refusal(f"unknown material expression constructor {kind!r}")

        if sorted(reduce.checks) != sorted(contract["checks"]):
            raise Refusal(f"reduce {reduce.label!r} has wrong body-check roles")
        normalized_selected = []
        for role, slot in sorted(contract["checks"].items()):
            label = reduce.checks[role]
            view = checks.get(label)
            if view is None or view.event.contract != slot["contract"]:
                raise Refusal(f"reduce {reduce.label!r} body check {role!r} does not match")
            if label in selected_checks:
                raise Refusal(f"check {label!r} justifies more than one reduction")
            selected_checks.add(label)
            if view.event.params != slot["parameters"]:
                raise Refusal(f"reduce {reduce.label!r} body check parameters do not match")
            expected_predicate = slot.get("transparent_predicate")
            if view.normalized_expr != expected_predicate:
                raise Refusal(f"reduce {reduce.label!r} body predicate does not match")

            for attachment in slot["attachments"]:
                kind = attachment["kind"]
                target = attachment["target_role"]
                # Value identity is deliberately a local SSA judgment.  A
                # dependency/message selected for this purpose is not
                # semantic material and therefore neither evaluates through
                # MaterialExpr nor consumes a MaterialBinding.
                if kind == "value_identity":
                    selected_operands = view.roles.get(target)
                    if selected_operands is None:
                        raise Refusal(
                            "reduction attachment targets unknown operand role"
                        )
                    if selected_operands != [local_value(attachment["source"])]:
                        raise Refusal("reduction local-value attachment mismatch")
                    continue

                source_sort, expected = evaluate(attachment["source"])
                if kind == "semantic_parameter":
                    actual = view.event.semantic_args.get(target)
                    if source_sort != "ref" or actual != expected:
                        raise Refusal("reduction semantic-parameter attachment mismatch")
                    continue
                selected_operands = view.roles.get(target)
                if selected_operands is None:
                    raise Refusal("reduction attachment targets unknown operand role")
                if kind == "material_ref_equality":
                    if (
                        source_sort != "ref"
                        or len(selected_operands) != 1
                        or binding(selected_operands[0]) != expected
                    ):
                        raise Refusal("reduction material-reference attachment mismatch")
                elif kind == "material_ref_vector_equality":
                    actual = [binding(value) for value in selected_operands]
                    if source_sort != "refs" or actual != expected:
                        raise Refusal("reduction material-vector attachment mismatch")
                elif kind == "common_material_ref_equality":
                    common = expected[0] if expected else None
                    if (
                        source_sort != "refs"
                        or common is None
                        or any(member != common for member in expected)
                        or len(selected_operands) != 1
                        or binding(selected_operands[0]) != common
                    ):
                        raise Refusal("reduction common-material attachment mismatch")
                else:
                    raise Refusal(f"unknown reduction attachment kind {kind!r}")
            normalized_selected.append([role, event_positions[label]])

        for constraint in contract["constraints"]:
            left_sort, left = evaluate(constraint["left"])
            right_sort, right = evaluate(constraint["right"])
            if left_sort != right_sort or left != right:
                raise Refusal(f"reduce {reduce.label!r} material constraint fails")

        if len(reduce.anchors) != len(contract["outputs"]):
            raise Refusal(f"reduce {reduce.label!r} has wrong output-anchor arity")
        for index, (output, authored) in enumerate(zip(contract["outputs"], reduce.anchors)):
            expected_anchors = {}
            for anchor, expression in output["anchors"].items():
                sort, value = evaluate(expression)
                if sort != "ref":
                    raise Refusal("reduction output constructor is not a RefExpr")
                expected_anchors[anchor] = value
            if authored != expected_anchors:
                raise Refusal(
                    f"reduce {reduce.label!r} output {index} anchors do not "
                    f"match: expected {expected_anchors} got {authored}"
                )

        records.append(
            {
                "checks": normalized_selected,
                "contract": reduce.contract,
                "kind": "reduction_closure",
                "transformer": transformer_positions[reduce.label],
            }
        )

    records.sort(key=lambda record: record["transformer"])
    if _return_used:
        return records, used_bindings
    return records


def _validate_contract_shape(
    protocol: dict[str, Any], vocabulary: ProtocolVocabulary
) -> None:
    """Validate reduction-contract shape and derive transcript obligations.

    This is intentionally independent of the C++ seal battery. A contract is
    not merely an implication label: its round structure generates the
    prefix that each round challenge must bind (kernel.md 5.2).  Keeping that
    derivation here prevents the differential suite from being two front-ends
    over one implementation of the property under test.
    """

    event_sequence = protocol["events"]
    events = {event.label: event for event in event_sequence}
    positions = {event.label: index for index, event in enumerate(event_sequence)}
    claim_profiles = {entry.label: entry.profile for entry in protocol["sources"]}

    membership: dict[str, dict[str, dict[int, Slot]]] = {}
    for event in event_sequence:
        if not isinstance(event, Slot) or event.membership is None:
            continue
        instance, role, index = event.membership
        occurrences = membership.setdefault(instance, {}).setdefault(role, {})
        if index in occurrences:
            raise Refusal(
                f"[zkc-E244] duplicate occurrence {instance!r}.{role}[{index}]"
            )
        occurrences[index] = event

    challenge_consumer: dict[str, str] = {}
    for reduce in protocol.get("reduces", []):
        contract = vocabulary.reductions.get(reduce.contract)
        if contract is None:
            raise Refusal(f"unknown reduction contract {reduce.contract!r}")
        consumed = [claim_profiles.get(label) for label in reduce.consumed]
        patterns = contract["consumes"]
        if len(patterns) == 1 and isinstance(patterns[0], dict):
            expected = patterns[0]
            if len(consumed) < expected["min"] or any(
                profile != expected["profile"] for profile in consumed
            ):
                raise Refusal(f"reduce {reduce.label!r} violates variadic consumes")
        elif consumed != patterns:
            raise Refusal(f"reduce {reduce.label!r} has wrong input profiles")
        produced_profiles = [profile for _, profile in reduce.produced]
        if produced_profiles != [output["profile"] for output in contract["outputs"]]:
            raise Refusal(f"reduce {reduce.label!r} has wrong output profiles")
        if len(reduce.deps) != len(contract["dep_slots"]):
            raise Refusal(
                f"[zkc-E243] reduce {reduce.label!r} has wrong dependency arity"
            )
        dep_by_role: dict[str, Any] = {}
        bound_here: set[str] = set()
        for label, dep_slot in zip(reduce.deps, contract["dep_slots"]):
            event = events.get(label)
            if event is None:
                raise Refusal(f"reduce {reduce.label!r} has unknown dependency")
            if isinstance(event, (Bind, Slot, Chal)):
                actual_class = event.payload_class
            else:
                raise Refusal(
                    f"reduce {reduce.label!r} dependency {label!r} is not a value"
                )
            source = dep_slot["source"]
            source_matches = (
                source == "any"
                or (source == "public_bind" and isinstance(event, Bind))
                or (source == "prover_slot" and isinstance(event, Slot))
                or (
                    source == "challenge_capability"
                    and isinstance(event, Chal)
                )
            )
            if actual_class != dep_slot["class"] or not source_matches:
                raise Refusal(
                    f"[zkc-E243] reduce {reduce.label!r} dependency "
                    f"{dep_slot['role']!r} has the wrong source or class"
                )
            dep_by_role[dep_slot["role"]] = event

        declared_messages = {
            message["role"]: _resolve_message_count(
                message["count"], len(reduce.consumed)
            )
            for round_ in contract["rounds"]
            for message in round_["messages"]
        }
        bound_messages = membership.get(reduce.label, {})
        for role in bound_messages:
            if role not in declared_messages:
                raise Refusal(
                    f"[zkc-E244] contract {reduce.contract!r} has no message role "
                    f"{role!r}"
                )
        for role, count in declared_messages.items():
            occurrences = bound_messages.get(role, {})
            if set(occurrences) != set(range(count)):
                raise Refusal(
                    f"[zkc-E244] message role {role!r} requires occurrence "
                    f"indices 0..{count - 1}, got {sorted(occurrences)}"
                )

        prior_challenges: list[tuple[str, Chal]] = []
        covered_roles: list[str] = []
        for round_ in contract["rounds"]:
            challenge_use = round_["challenge_use"]
            challenge_role = challenge_use["role"]
            challenge = dep_by_role.get(challenge_role)
            if not isinstance(challenge, Chal):
                # Vocabulary admission and E243 normally make this impossible;
                # keep the refusal local so malformed data cannot weaken E213.
                raise Refusal(
                    f"[zkc-E243] round {challenge_role!r} has no challenge dep"
                )
            expected_count = challenge_use.get("count", 1)
            actual_count = 1
            if challenge.mode is not None:
                try:
                    actual_count = int(challenge.mode[1])
                except (IndexError, TypeError, ValueError):
                    raise Refusal(
                        f"[zkc-E243] round {challenge_role!r} has malformed "
                        "challenge shape"
                    ) from None
            if actual_count != expected_count:
                raise Refusal(
                    f"[zkc-E243] round {challenge_role!r} realizes challenge "
                    f"count {actual_count}, contract requires {expected_count}"
                )
            if challenge.label in bound_here:
                raise Refusal(
                    f"[zkc-E245] challenge {challenge.label!r} fills two "
                    "priced round uses"
                )
            bound_here.add(challenge.label)
            previous = challenge_consumer.setdefault(
                challenge.label, reduce.label
            )
            if previous != reduce.label:
                raise Refusal(
                    f"[zkc-E245] challenge {challenge.label!r} is shared by "
                    f"reduces {previous!r} and {reduce.label!r}"
                )
            challenge_pos = positions[challenge.label]
            for prior_role, prior in prior_challenges:
                if positions[prior.label] > challenge_pos:
                    raise Refusal(
                        f"[zkc-E213] round challenge {challenge_role!r} is "
                        f"sampled before prior challenge {prior_role!r}"
                    )
            covered_roles.extend(message["role"] for message in round_["messages"])
            for role in covered_roles:
                for occurrence in bound_messages[role].values():
                    if positions[occurrence.label] > challenge_pos:
                        raise Refusal(
                            f"[zkc-E213] round message {role!r} must precede "
                            f"challenge {challenge_role!r}"
                        )
                    if not occurrence.absorbed:
                        raise Refusal(
                            f"[zkc-E213] round message {role!r} is not absorbed "
                            f"before challenge {challenge_role!r}"
                        )
            prior_challenges.append((challenge_role, challenge))

        for label, profile in reduce.produced:
            claim_profiles[label] = profile


def validate_protocol(
    protocol: dict[str, Any], vocabulary: ProtocolVocabulary
) -> None:
    """Run the reference seal subset, including TerminalClosureOK."""

    if protocol["policy"] not in PERMITTED_SINKS:
        raise Refusal("unknown seal policy")
    event_labels = [event.label for event in protocol["events"]]
    if len(event_labels) != len(set(event_labels)):
        raise Refusal("event labels are not unique")
    for event in protocol["events"]:
        if isinstance(event, Chal):
            if event.payload_class == "chal":
                raise Refusal(
                    "[zkc-E145] challenge payload class 'chal' is retired; "
                    "use the sampled value's semantic class"
                )
            if (
                not event.space
                or not event.space.isascii()
                or not event.space.isdigit()
                or event.space[0] == "0"
            ):
                raise Refusal("challenge space is not minimal decimal")
            if len(set(event.deps)) != len(event.deps):
                raise Refusal("challenge dependency set has duplicates")
            if event.mode is not None and not (
                len(event.mode) == 3
                and event.mode[0] == "vector"
                and event.mode[1].isascii()
                and event.mode[1].isdigit()
                and event.mode[1] not in {"0", "1"}
                and not event.mode[1].startswith("0")
                and event.mode[2] == "uniform_independent"
            ):
                raise Refusal("invalid vector challenge mode")

    produced = Counter(source.label for source in protocol["sources"])
    produced.update(
        label for reduce in protocol.get("reduces", []) for label, _ in reduce.produced
    )
    consumed = Counter(
        label for reduce in protocol.get("reduces", []) for label in reduce.consumed
    )
    permitted = PERMITTED_SINKS[protocol["policy"]]
    for sink in protocol["sinks"]:
        if sink.tag not in permitted:
            raise Refusal(f"sink {sink.tag!r} is forbidden by policy")
        consumed[sink.claim] += 1
    for label in set(produced) | set(consumed):
        if produced[label] != 1 or consumed[label] != 1:
            raise Refusal(f"claim {label!r} is not linear")

    segment_starts = list(protocol.get("segments", []))
    previous = 0
    for start in segment_starts:
        if type(start) is not int or start <= previous or start >= len(protocol["events"]):
            raise Refusal(
                "[zkc-E215] segment starts must be strictly increasing event "
                "positions inside the spine"
            )
        previous = start

    absorbed: set[str] = set()
    first_unabsorbed: str | None = None
    first_challenge: str | None = None
    next_segment = 0
    domains: set[str] = set()
    for event_position, event in enumerate(protocol["events"]):
        if (
            next_segment < len(segment_starts)
            and event_position == segment_starts[next_segment]
        ):
            next_segment += 1
            first_challenge = None
        if isinstance(event, Bind):
            if first_challenge is not None:
                raise Refusal(
                    f"[zkc-E214] statement binding {event.label!r} follows "
                    f"challenge {first_challenge!r} in its segment"
                )
            absorbed.add(event.label)
        elif isinstance(event, Slot):
            if event.absorbed:
                absorbed.add(event.label)
            elif first_unabsorbed is None:
                first_unabsorbed = event.label
        elif isinstance(event, Chal):
            if event.domain in domains:
                raise Refusal(f"duplicate challenge domain {event.domain!r}")
            domains.add(event.domain)
            if first_challenge is None:
                first_challenge = event.label
            if any(dep not in absorbed for dep in event.deps):
                raise Refusal(f"challenge {event.label!r} has unabsorbed dependency")
            if first_unabsorbed is not None:
                raise Refusal("challenge follows an unabsorbed proof slot")
            absorbed.add(event.label)

    _, reduction_bindings = reduction_closure(
        protocol, vocabulary, _return_used=True
    )
    _, terminal_bindings = terminal_closure(
        protocol, vocabulary, _return_used=True
    )
    all_bindings = {
        binding.value for binding in protocol.get("material_bindings", [])
    }
    unused = all_bindings - reduction_bindings - terminal_bindings
    if unused:
        raise Refusal(f"unused material bindings: {sorted(unused)}")
    # The authored model contains structural booleans (for example a proof
    # slot's absorbed bit).  They lower to integers before entering the
    # canonical attribute domain, so validate that domain on the PIR
    # document rather than on the Python carrier objects.
    canonical_document(protocol, vocabulary)


def resolved_vocabulary(
    protocol: dict[str, Any], vocabulary: ProtocolVocabulary
) -> dict[str, dict[str, str]]:
    profiles = {source.profile for source in protocol["sources"]}
    contracts = {
        event.contract for event in protocol["events"] if isinstance(event, Check)
    }
    reductions = {reduce.contract for reduce in protocol.get("reduces", [])}
    rules = {
        sink.rule for sink in protocol["sinks"] if isinstance(sink, Discharge)
    }
    for rule_name in list(rules):
        try:
            rule = vocabulary.rules[rule_name]
        except KeyError:
            raise Refusal(f"unknown terminal rule {rule_name!r}") from None
        profiles.add(rule["claim_profile"])
        contracts.update(rule["checks"].values())
        if "producer" in rule:
            reductions.add(rule["producer"]["contract"])
    for contract_name in list(reductions):
        try:
            reduction_contract = vocabulary.reductions[contract_name]
        except KeyError:
            raise Refusal(f"unknown reduction contract {contract_name!r}") from None
        profiles.update(
            member if isinstance(member, str) else member["profile"]
            for member in reduction_contract["consumes"]
        )
        profiles.update(output["profile"] for output in reduction_contract["outputs"])
        contracts.update(
            slot["contract"] for slot in reduction_contract["checks"].values()
        )
    for reduce in protocol.get("reduces", []):
        profiles.update(profile for _, profile in reduce.produced)

    construction = {f"sponge:{protocol['kappa']['sponge']}"}
    construction.update(
        f"codec:{codec}" for codec in protocol["kappa"].get("codecs", {}).values()
    )
    table = {
        "claim_profiles": {
            name: vocabulary.digest_for("claim_profiles", name)
            for name in sorted(profiles)
        },
        "check_contracts": {
            name: vocabulary.digest_for("check_contracts", name)
            for name in sorted(contracts)
        },
        "reduction_contracts": {
            name: vocabulary.digest_for("reduction_contracts", name)
            for name in sorted(reductions)
        },
        "terminal_rules": {
            name: vocabulary.digest_for("terminal_rules", name)
            for name in sorted(rules)
        },
        "construction_profiles": {
            name: construction_digest(name) for name in sorted(construction)
        },
    }
    # Hole contracts are cited by construction routes; the sixth section
    # exists exactly when at least one contract is cited, so a protocol
    # without routes keeps its exact table shape and bytes.
    routes = protocol.get("routes")
    if routes:
        hole_ids = sorted(
            {
                instance["contract"]
                for instance in routes.get("instances", {}).values()
            }
        )
        if hole_ids:
            table["hole_contracts"] = {
                name: vocabulary.digest_for("hole_contracts", name)
                for name in hole_ids
            }
    return table


def _normalized_transformers(protocol: dict[str, Any]):
    event_pos = {
        event.label: position for position, event in enumerate(protocol["events"])
    }
    sources = sorted(
        protocol["sources"],
        key=lambda entry: (entry.profile, canon_json(entry.anchors)),
    )
    reduces = protocol.get("reduces", [])
    claim_pos: dict[str, int] = {}
    transformer_pos: dict[str, int] = {}
    claim_count = 0
    transformer_count = 0
    for entry in sources:
        claim_pos[entry.label] = claim_count
        claim_count += 1
        transformer_count += 1

    waiters: dict[str, list[int]] = {}
    missing = [0] * len(reduces)
    for index, reduce in enumerate(reduces):
        for claim in reduce.consumed:
            if claim not in claim_pos:
                waiters.setdefault(claim, []).append(index)
                missing[index] += 1

    def key(index: int):
        reduce = reduces[index]
        return (
            reduce.contract,
            [claim_pos[claim] for claim in reduce.consumed],
            [event_pos[dependency] for dependency in reduce.deps],
            [profile for _, profile in reduce.produced],
            canon_json(reduce.params),
            canon_json(reduce.anchors),
            [
                [role, event_pos[label]]
                for role, label in sorted(reduce.checks.items())
            ],
            index,
        )

    ready = [key(index) for index, count in enumerate(missing) if count == 0]
    heapq.heapify(ready)
    normalized = []
    while ready:
        index = heapq.heappop(ready)[-1]
        reduce = reduces[index]
        transformer_pos[reduce.label] = transformer_count
        transformer_count += 1
        normalized.append(reduce)
        for label, _ in reduce.produced:
            claim_pos[label] = claim_count
            claim_count += 1
            for waiter in waiters.get(label, []):
                missing[waiter] -= 1
                if missing[waiter] == 0:
                    heapq.heappush(ready, key(waiter))
    if len(normalized) != len(reduces):
        raise Refusal("reduction claim flow is cyclic")
    return sources, normalized, claim_pos, transformer_pos


def canonical_document(
    protocol: dict[str, Any], vocabulary: ProtocolVocabulary
) -> dict[str, Any]:
    """Build the canonical PIR object."""

    events = protocol["events"]
    event_pos = {event.label: index for index, event in enumerate(events)}
    sources, reduces, claim_pos, transformer_pos = _normalized_transformers(protocol)

    # Route references normalize to label-free canonical forms: events
    # by position, witness payloads by ordinal, hole outputs by
    # (instance, index) — mirroring the carrier's identity walk, so
    # renaming stays id-stable and an ambiguous referenced label is
    # refused, never guessed (docs/spec/carrier.md §6).
    kind_pos: dict[str, dict[str, int]] = {"bind": {}, "slot": {}, "chal": {}}
    duplicate_refs: set[str] = set()
    for index, event in enumerate(events):
        kind = (
            "bind"
            if isinstance(event, Bind)
            else "slot"
            if isinstance(event, Slot)
            else "chal"
            if isinstance(event, Chal)
            else None
        )
        if kind is not None:
            if event.label in kind_pos[kind]:
                duplicate_refs.add(f"{kind}:{event.label}")
            else:
                kind_pos[kind][event.label] = index
    routes = protocol.get("routes")
    witness_index = {
        label: index
        for index, (label, _cls) in enumerate(
            (routes or {}).get("witnesses", [])
        )
    }

    def normalize_route_ref(text: str) -> list[Any]:
        for tag in ("bind", "slot", "chal"):
            prefix = tag + ":"
            if text.startswith(prefix):
                name = text[len(prefix):]
                if text in duplicate_refs:
                    raise Refusal(
                        f"route reference {text!r} names an ambiguous label"
                    )
                if name not in kind_pos[tag]:
                    raise Refusal(f"route reference {text!r} does not resolve")
                return ["event", kind_pos[tag][name]]
        if text.startswith("const:"):
            return ["const", text[len("const:"):]]
        if text.startswith("witness:"):
            name = text[len("witness:"):]
            if name not in witness_index:
                raise Refusal(
                    f"route reference {text!r} names an undeclared payload"
                )
            return ["witness", witness_index[name]]
        instance, _dot, output = text.rpartition(".")
        if not instance or not output.isdigit():
            raise Refusal(f"{text!r} is not a route reference")
        return ["hole", instance, int(output)]

    transformers = [
        ["source", entry.profile, entry.anchors] for entry in sources
    ]
    for reduce in reduces:
        transformers.append(
            [
                "reduce",
                reduce.contract,
                [claim_pos[label] for label in reduce.consumed],
                [event_pos[label] for label in reduce.deps],
                [profile for _, profile in reduce.produced],
                reduce.params,
                reduce.anchors,
                [
                    [role, event_pos[label]]
                    for role, label in sorted(reduce.checks.items())
                ],
            ]
        )

    event_rows = []
    for event in events:
        if isinstance(event, Bind):
            event_rows.append(
                ["bind", event.payload_class, event.stage, event.value]
            )
        elif isinstance(event, Slot):
            membership = None
            if event.membership is not None:
                instance, role, index = event.membership
                membership = [transformer_pos[instance], role, index]
            row = [
                "slot",
                event.payload_class,
                1 if event.absorbed else 0,
                membership,
            ]
            if event.binding is not None:
                row.append(normalize_route_ref(event.binding))
            event_rows.append(row)
        elif isinstance(event, Chal):
            row = [
                "chal",
                event.payload_class,
                event.domain,
                event.space,
                sorted(event_pos[label] for label in event.deps),
            ]
            if event.mode is not None:
                row.append(list(event.mode))
            event_rows.append(row)
        elif isinstance(event, Check):
            event_rows.append(
                [
                    "check",
                    event.contract,
                    [event_pos[label] for label in event.inputs],
                    event.params,
                    event.semantic_args,
                    event.expr,
                ]
            )
        else:
            raise Refusal(f"event has no PIR encoding: {event!r}")

    material_bindings = sorted(
        [event_pos[binding.value], binding.semantic_ref]
        for binding in protocol.get("material_bindings", [])
    )
    sinks = []
    for sink in sorted(protocol["sinks"], key=lambda item: claim_pos[item.claim]):
        if isinstance(sink, Discharge):
            sinks.append(
                [
                    "discharge",
                    claim_pos[sink.claim],
                    sink.rule,
                    {
                        role: event_pos[label]
                        for role, label in sorted(sink.checks.items())
                    },
                ]
            )
        else:
            sinks.append([sink.tag, claim_pos[sink.claim], sink.route])

    document = {
        "policy": protocol["policy"],
        "kappa": protocol["kappa"],
        "vocab": resolved_vocabulary(protocol, vocabulary),
        "transformers": transformers,
        "events": event_rows,
        "material_bindings": material_bindings,
        "sinks": sinks,
    }
    if protocol.get("segments"):
        document["segments"] = list(protocol["segments"])
    if routes:
        instances_json = {}
        for name, instance in routes["instances"].items():
            entry: dict[str, Any] = {
                "contract": instance["contract"],
                "inputs": [
                    normalize_route_ref(ref) for ref in instance["inputs"]
                ],
            }
            params = instance.get("params") or {}
            if params:
                entry["params"] = params
            instances_json[name] = entry
        document["routes"] = {
            "instances": instances_json,
            "witnesses": [cls for _label, cls in routes.get("witnesses", [])],
        }
    check_domain(document)
    return document


def canonical_encoding(
    protocol: dict[str, Any], vocabulary: ProtocolVocabulary
) -> bytes:
    return canon_json(canonical_document(protocol, vocabulary)).encode("ascii")


def compute_id(
    protocol: dict[str, Any], vocabulary: ProtocolVocabulary
) -> str:
    return hashlib.sha256(
        b"zkc/pir\n" + canonical_encoding(protocol, vocabulary)
    ).hexdigest()


_LICENSES = {
    "const+absorb": {"const", "absorb"},
    "arg+absorb": {"absorb"},
    "read+absorb": {"read", "absorb"},
    "read": {"read"},
    "squeeze.scalar": {"squeeze"},
    "squeeze.vector": {"squeeze"},
    "assert_eq": {"assert_eq", "const", "f_neg", "f_add", "f_mul", "g_exp", "g_mul"},
    "check_call": {"check_call"},
}

_REALIZES = {
    "const+absorb": {"const", "absorb"},
    "arg+absorb": {"absorb"},
    "read+absorb": {"read", "absorb"},
    "read": {"read"},
    "squeeze.scalar": {"squeeze"},
    "squeeze.vector": {"squeeze"},
    "assert_eq": {"assert_eq"},
    "check_call": {"check_call"},
}


def obligations(protocol: dict[str, Any]) -> list[tuple[int, str, str]]:
    table = []
    for position, event in enumerate(protocol["events"]):
        if isinstance(event, Bind):
            discharge_kind = "const+absorb" if event.stage == "seal" else "arg+absorb"
        elif isinstance(event, Slot):
            discharge_kind = "read+absorb" if event.absorbed else "read"
        elif isinstance(event, Chal):
            discharge_kind = "squeeze.vector" if event.mode else "squeeze.scalar"
        elif isinstance(event, Check):
            discharge_kind = "assert_eq" if event.expr is not None else "check_call"
        else:
            raise Refusal("event has no projection obligation")
        table.append((position, "executable", discharge_kind))
    return table


def project(
    protocol: dict[str, Any],
    vocabulary: ProtocolVocabulary,
    kind: str = "verifier",
) -> dict[str, Any]:
    """Derive the current OIR endpoint image from a PIR object."""

    if kind == "prover_skeleton":
        return _project_prover(protocol, vocabulary)
    if kind != "verifier":
        raise Refusal(f"unknown endpoint {kind!r}")
    kappa = protocol["kappa"]
    statement_labels = [
        event.label
        for event in protocol["events"]
        if isinstance(event, Bind) and event.stage == "instance"
    ]
    rows: list[list[Any]] = []
    value_ref: dict[str, list[Any]] = {}
    stream: list[Any] = ["a", len(statement_labels)]

    def emit(row: list[Any]) -> int:
        rows.append(row)
        return len(rows) - 1

    emit(["init", kappa["sponge"], kappa["iv"]])
    sponge: list[Any] = ["r", 0, 0]
    argument = 0
    constants = kappa.get("constants", {})
    for position, event in enumerate(protocol["events"]):
        src = [position]
        if isinstance(event, Bind):
            if event.stage == "instance":
                value = ["a", argument]
                argument += 1
            elif event.value is None:
                continue
            else:
                value = [
                    "r",
                    emit(["const", event.value, event.payload_class, src]),
                    0,
                ]
            sponge = ["r", emit(["absorb", sponge, value, src]), 0]
            value_ref[event.label] = value
        elif isinstance(event, Slot):
            row = emit(["read", stream, event.label, event.payload_class, src])
            stream, value = ["r", row, 0], ["r", row, 1]
            value_ref[event.label] = value
            if event.absorbed:
                sponge = ["r", emit(["absorb", sponge, value, src]), 0]
        elif isinstance(event, Chal):
            count = event.mode[1] if event.mode is not None else "1"
            rule = event.mode[2] if event.mode is not None else "uniform"
            row = emit(
                [
                    "squeeze",
                    sponge,
                    event.label,
                    event.payload_class,
                    count,
                    event.domain,
                    rule,
                    event.space,
                    src,
                ]
            )
            sponge, value_ref[event.label] = ["r", row, 0], ["r", row, 1]
        elif isinstance(event, Check):
            if any(label not in value_ref for label in event.inputs):
                continue
            inputs = [value_ref[label] for label in event.inputs]
            if event.expr is None:
                static_values = [
                    event.params[name] for name in sorted(event.params)
                ] + [
                    event.semantic_args[name] for name in sorted(event.semantic_args)
                ]
                # Both the human-readable contract id and the sealed content
                # digest enter OIR identity; the digest is the dispatch
                # authority (carrier.md section 6).  Resolution is the same
                # fail-closed lookup seal used for the vocab table.
                emit(
                    [
                        "check_call",
                        inputs,
                        event.label,
                        event.contract,
                        vocabulary.digest_for("check_contracts", event.contract),
                        static_values,
                        src,
                    ]
                )
            else:
                def lower(node: list[Any]) -> list[Any]:
                    tag = node[0]
                    if tag == "in":
                        return inputs[node[1]]
                    if tag == "const":
                        spec = constants[node[1]]
                        return [
                            "r",
                            emit(["const", spec["value"], spec["class"], src]),
                            0,
                        ]
                    if tag == "f_neg":
                        return ["r", emit(["f_neg", lower(node[1]), src]), 0]
                    return [
                        "r",
                        emit([tag, lower(node[1]), lower(node[2]), src]),
                        0,
                    ]

                lhs, rhs = lower(event.expr[1]), lower(event.expr[2])
                emit(["assert_eq", lhs, rhs, event.label, src])
    emit(["expect_end", stream])
    emit(["decide", sponge])

    table = obligations(protocol)
    realized = {position: set() for position, _, _ in table}
    for row in rows:
        if row[0] in {"init", "expect_end", "decide"}:
            continue
        for position in row[-1]:
            if position not in realized:
                raise Refusal("OIR src references a non-event position")
            discharge_kind = table[position][2]
            if row[0] not in _LICENSES[discharge_kind]:
                raise Refusal("OIR family is not licensed for its event")
            realized[position].add(row[0])
    missing = [
        (position, discharge_kind)
        for position, _, discharge_kind in table
        if not _REALIZES[discharge_kind] <= realized[position]
    ]
    if missing:
        raise Refusal(f"OIR realization is incomplete: {missing}")
    entry = [
        ["val", event.payload_class]
        for event in protocol["events"]
        if isinstance(event, Bind) and event.stage == "instance"
    ] + [["stream"]]
    return {
        "endpoint": kind,
        "source": "sha256:" + compute_id(protocol, vocabulary),
        "codecs": kappa.get("codecs", {}),
        "entry": entry,
        "statement_labels": statement_labels,
        # The sealed construction pins travel with the endpoint: an executor
        # gates them against its supplier set before any transcript event
        # (endpoints.md section 2), so which construction bytes an artifact
        # was sealed against is part of what the artifact says.
        "param_digests": [
            f"{name}={construction_digest(name)}"
            for name in sorted(
                {f"codec:{codec}" for codec in kappa.get("codecs", {}).values()}
                | {f"sponge:{kappa['sponge']}"})
        ],
        "program": rows,
    }


_PROVER_LICENSES = {
    "const+absorb": {"const", "absorb"},
    "arg+absorb": {"absorb"},
    "read+absorb": {"write", "absorb"},
    "read": {"write"},
    "squeeze.scalar": {"squeeze"},
    "squeeze.vector": {"squeeze"},
}


def _project_prover(
    protocol: dict[str, Any], vocabulary: ProtocolVocabulary
) -> dict[str, Any]:
    """The second projection of the same seal
    (docs/spec/endpoints.md §6.1): write where the verifier reads,
    absorb and squeeze identically, holes for the compute, checks
    counterparty-realized as rows."""

    kappa = protocol["kappa"]
    routes = protocol.get("routes")
    if not routes:
        raise Refusal("prover projection requires construction routes")
    instances = routes.get("instances", {})
    witnesses = list(routes.get("witnesses", []))
    statement_labels = [
        event.label
        for event in protocol["events"]
        if isinstance(event, Bind) and event.stage == "instance"
    ]
    for event in protocol["events"]:
        if isinstance(event, Slot) and event.binding is None:
            raise Refusal(
                f"prover projection requires a construction route for "
                f"slot {event.label!r}"
            )

    rows: list[list[Any]] = []
    value_ref: dict[str, list[Any]] = {}
    witness_arg = {
        label: ["a", len(statement_labels) + index]
        for index, (label, _cls) in enumerate(witnesses)
    }
    stream: list[Any] = ["a", len(statement_labels) + len(witnesses)]

    def emit(row: list[Any]) -> int:
        rows.append(row)
        return len(rows) - 1

    emit(["init", kappa["sponge"], kappa["iv"]])
    sponge: list[Any] = ["r", 0, 0]
    argument = 0
    constants = kappa.get("constants", {})
    hole_results: dict[str, list[list[Any]]] = {}

    def materialize_const(name: str) -> list[Any]:
        spec = constants[name]
        # Pure materialization covers no obligation: empty src.
        return ["r", emit(["const", spec["value"], spec["class"], []]), 0]

    def resolve_ref(text: str) -> list[Any]:
        if text.startswith("bind:"):
            return value_ref[text[len("bind:"):]]
        if text.startswith("slot:"):
            return value_ref[text[len("slot:"):]]
        if text.startswith("chal:"):
            return value_ref[text[len("chal:"):]]
        if text.startswith("const:"):
            return materialize_const(text[len("const:"):])
        if text.startswith("witness:"):
            return witness_arg[text[len("witness:"):]]
        instance, _dot, output = text.rpartition(".")
        materialize(instance)
        return hole_results[instance][int(output)]

    def materialize(name: str) -> None:
        nonlocal sponge
        if name in hole_results:
            return
        instance = instances[name]
        contract = vocabulary.hole_contracts[instance["contract"]]
        params = [
            instance.get("params", {})[param]
            for param in contract["parameters"]
        ]
        semantic_params = [
            instance.get("params", {})[param]
            for param in contract["semantic_parameters"]
        ]
        operands = []
        input_index = 0
        for segment in contract["operands"]:
            if segment["sort"] == "sponge":
                operands.append(sponge)
                continue
            operands.append(resolve_ref(instance["inputs"][input_index]))
            input_index += 1
        results = []
        for segment in contract["results"]:
            if segment["sort"] == "value":
                results.append(["val", segment["class"]])
            elif segment["sort"] == "handle":
                results.append(["handle", segment["class"]])
            else:
                results.append(["sponge"])
        row = emit(
            [
                "hole_call",
                operands,
                results,
                name,
                contract["kind"],
                vocabulary.digest_for("hole_contracts", instance["contract"]),
                params,
                semantic_params,
            ]
        )
        outputs = [["r", row, index] for index in range(len(results))]
        for index, segment in enumerate(contract["results"]):
            if segment["sort"] == "sponge":
                sponge = outputs[index]
        hole_results[name] = outputs

    counterparty = []
    table = obligations(protocol)
    for position, event in enumerate(protocol["events"]):
        src = [position]
        if isinstance(event, Bind):
            if event.stage == "instance":
                value = ["a", argument]
                argument += 1
            elif event.value is None:
                continue
            else:
                value = [
                    "r",
                    emit(["const", event.value, event.payload_class, src]),
                    0,
                ]
            sponge = ["r", emit(["absorb", sponge, value, src]), 0]
            value_ref[event.label] = value
        elif isinstance(event, Slot):
            value = resolve_ref(event.binding)
            row = emit(
                [
                    "write",
                    stream,
                    value,
                    event.label,
                    event.payload_class,
                    src,
                ]
            )
            stream = ["r", row, 0]
            value_ref[event.label] = value
            if event.absorbed:
                sponge = ["r", emit(["absorb", sponge, value, src]), 0]
        elif isinstance(event, Chal):
            count = event.mode[1] if event.mode is not None else "1"
            rule = event.mode[2] if event.mode is not None else "uniform"
            row = emit(
                [
                    "squeeze",
                    sponge,
                    event.label,
                    event.payload_class,
                    count,
                    event.domain,
                    rule,
                    event.space,
                    src,
                ]
            )
            sponge, value_ref[event.label] = ["r", row, 0], ["r", row, 1]
        elif isinstance(event, Check):
            counterparty.append([position, table[position][2]])
    emit(["end_stream", stream])
    emit(["finish", sponge])

    realized = {position: set() for position, _, _ in table}
    for row in rows:
        if row[0] in {"init", "end_stream", "finish", "hole_call"}:
            continue
        for position in row[-1]:
            if position not in realized:
                raise Refusal("OIR src references a non-event position")
            discharge_kind = table[position][2]
            if row[0] not in _PROVER_LICENSES.get(discharge_kind, set()):
                raise Refusal(
                    "OIR family is not licensed for its event on the "
                    "prover endpoint"
                )
            realized[position].add(row[0])
    counterparty_positions = {position for position, _ in counterparty}
    for position, _, discharge_kind in table:
        if position in counterparty_positions:
            continue
        if not realized[position]:
            raise Refusal(f"prover realization is incomplete at {position}")

    entry = (
        [
            ["val", event.payload_class]
            for event in protocol["events"]
            if isinstance(event, Bind) and event.stage == "instance"
        ]
        + [["handle", cls] for _label, cls in witnesses]
        + [["stream"]]
    )
    return {
        "endpoint": "prover_skeleton",
        "source": "sha256:" + compute_id(protocol, vocabulary),
        "codecs": kappa.get("codecs", {}),
        "entry": entry,
        "statement_labels": statement_labels,
        "param_digests": [
            f"{name}={construction_digest(name)}"
            for name in sorted(
                {f"codec:{codec}" for codec in kappa.get("codecs", {}).values()}
                | {f"sponge:{kappa['sponge']}"})
        ],
        "program": rows,
        "witness_labels": [list(pair) for pair in witnesses],
        "counterparty": counterparty,
    }


def canonical_oir_encoding(
    protocol: dict[str, Any],
    vocabulary: ProtocolVocabulary,
    kind: str = "verifier",
) -> bytes:
    document = project(protocol, vocabulary, kind)
    check_domain(document)
    return canon_json(document).encode("ascii")


def compute_oir_id(
    protocol: dict[str, Any],
    vocabulary: ProtocolVocabulary,
    kind: str = "verifier",
) -> str:
    return hashlib.sha256(
        b"zkc/oir\n" + canonical_oir_encoding(protocol, vocabulary, kind)
    ).hexdigest()


def compute_oir_semantic_id(
    protocol: dict[str, Any],
    vocabulary: ProtocolVocabulary,
    kind: str = "verifier",
) -> str:
    """Provenance-independent endpoint identity (carrier.md section 6.1).

    The erasure drops the PIR source citation and every row's src position
    list; everything the endpoint does survives, everything about where it
    came from is gone."""

    document = project(protocol, vocabulary, kind)
    del document["source"]
    document["program"] = [
        row[:-1] + [[]] if isinstance(row[-1], list) and row[0] not in
        {"init", "hole_call", "end_stream", "finish", "expect_end", "decide"}
        else row
        for row in document["program"]
    ]
    check_domain(document)
    return hashlib.sha256(
        b"zkc/oir-semantic\n" + canon_json(document).encode("ascii")
    ).hexdigest()


def _self_test() -> None:
    import copy

    from . import witnesses

    checks = 0

    def ok(condition: bool, message: str) -> None:
        nonlocal checks
        if not condition:
            raise AssertionError(message)
        checks += 1

    for witness in witnesses.PIR_WITNESSES.values():
        validate_protocol(witness, VOCABULARY)
        ok(len(compute_id(witness, VOCABULARY)) == 64, "PIR id shape")
        ok(compute_id(witness, VOCABULARY) == compute_id(copy.deepcopy(witness), VOCABULARY), "determinism")

    wrong_relation = copy.deepcopy(witnesses.RELATION_DIRECT)
    check_event = next(event for event in wrong_relation["events"] if isinstance(event, Check))
    check_event.semantic_args["contract"] = witnesses.ref_digest("wrong.contract")
    try:
        terminal_closure(wrong_relation, VOCABULARY)
    except Refusal:
        ok(True, "relation semantic attachment rejects mutation")
    else:
        raise AssertionError("wrong relation semantic argument accepted")

    tautology = copy.deepcopy(witnesses.SCHNORR)
    equation = next(event for event in tautology["events"] if isinstance(event, Check))
    equation.expr[:] = ["eq", ["in", 3], ["in", 3]]
    try:
        terminal_closure(tautology, VOCABULARY)
    except Refusal:
        ok(True, "Schnorr terminal predicate is exact")
    else:
        raise AssertionError("tautological Schnorr check accepted")

    crossed = copy.deepcopy(witnesses.KZG_SINGLE)
    first = next(
        event for event in crossed["events"] if isinstance(event, Check)
    )
    first.inputs[0] = "C2"
    try:
        terminal_closure(crossed, VOCABULARY)
    except Refusal:
        ok(True, "KZG material attachment rejects crossed check")
    else:
        raise AssertionError("crossed KZG check accepted")

    bad_batch = copy.deepcopy(witnesses.KZG_BATCH)
    batch_claim = bad_batch["reduces"][0].anchors[0]
    batch_claim["members"] = witnesses.ref_digest("wrong.members")
    try:
        reduction_closure(bad_batch, VOCABULARY)
    except Refusal:
        ok(True, "batch output constructor is exact")
    else:
        raise AssertionError("wrong batch member digest accepted")

    checkless_sumcheck = copy.deepcopy(witnesses.SUMCHECK)
    checkless_sumcheck["events"] = [
        event
        for event in checkless_sumcheck["events"]
        if not isinstance(event, Check)
    ]
    checkless_sumcheck["reduces"][0].checks.clear()
    try:
        validate_protocol(checkless_sumcheck, VOCABULARY)
    except Refusal:
        ok(True, "check-free sumcheck reduction is refused")
    else:
        raise AssertionError("check-free sumcheck reduction accepted")

    wrong_suite = copy.deepcopy(witnesses.KZG_BATCH)
    next(
        event
        for event in wrong_suite["events"]
        if isinstance(event, Check) and event.label == "batch_ok"
    ).params["suite"] = "garbage"
    try:
        validate_protocol(wrong_suite, VOCABULARY)
    except Refusal:
        ok(True, "KZG batch suite is contract-pinned")
    else:
        raise AssertionError("unrecognized KZG batch suite accepted")

    split_dleq_response = copy.deepcopy(witnesses.CHAUM_PEDERSEN)
    second_response = slot("resp_z2", "scalar", True)
    second_check_index = next(
        index
        for index, event in enumerate(split_dleq_response["events"])
        if isinstance(event, Check) and event.label == "verify2"
    )
    split_dleq_response["events"].insert(second_check_index, second_response)
    next(
        event
        for event in split_dleq_response["events"]
        if isinstance(event, Check) and event.label == "verify2"
    ).inputs[-1] = "resp_z2"
    try:
        reduction_closure(split_dleq_response, VOCABULARY)
    except Refusal:
        ok(True, "DLEQ equations must share the exact response value")
    else:
        raise AssertionError("DLEQ with split response values accepted")

    crossed_or_share = copy.deepcopy(witnesses.OR_SIGMA)
    next(
        event
        for event in crossed_or_share["events"]
        if isinstance(event, Check) and event.label == "verify1"
    ).inputs[2] = "share_c2"
    try:
        reduction_closure(crossed_or_share, VOCABULARY)
    except Refusal:
        ok(True, "OR equation and split must share exact challenge shares")
    else:
        raise AssertionError("OR proof with crossed challenge share accepted")

    weak_statement_binding = copy.deepcopy(witnesses.LINKED)
    weak_statement_binding.pop("segments")
    try:
        validate_protocol(weak_statement_binding, VOCABULARY)
    except Refusal as error:
        ok("[zkc-E214]" in str(error), "statement-binding default is mirrored")
    else:
        raise AssertionError("post-challenge statement binding accepted")

    late_round_message = copy.deepcopy(witnesses.SUMCHECK)
    events = late_round_message["events"]
    message_index = next(
        index
        for index, event in enumerate(events)
        if isinstance(event, Slot) and event.label == "g2_2"
    )
    message = events.pop(message_index)
    challenge_index = next(
        index
        for index, event in enumerate(events)
        if isinstance(event, Chal) and event.label == "c2"
    )
    events.insert(challenge_index + 1, message)
    try:
        validate_protocol(late_round_message, VOCABULARY)
    except Refusal as error:
        ok("[zkc-E213]" in str(error), "contract-generated prefix is mirrored")
    else:
        raise AssertionError("late contract-round message accepted")

    wrong_dependency = copy.deepcopy(witnesses.SUMCHECK)
    wrong_dependency["events"].insert(1, slot("aux", "scalar", True))
    wrong_dependency["reduces"][0] = wrong_dependency["reduces"][0]._replace(
        deps=["aux", "c2"]
    )
    try:
        validate_protocol(wrong_dependency, VOCABULARY)
    except Refusal as error:
        ok("[zkc-E243]" in str(error), "contract dependency typing is mirrored")
    else:
        raise AssertionError("object value accepted in a challenge dependency slot")

    duplicate_membership = copy.deepcopy(witnesses.SUMCHECK)
    message_index = next(
        index
        for index, event in enumerate(duplicate_membership["events"])
        if isinstance(event, Slot) and event.label == "g1_2"
    )
    duplicate_membership["events"][message_index] = duplicate_membership["events"][
        message_index
    ]._replace(membership=("sc", "g1", 1))
    try:
        validate_protocol(duplicate_membership, VOCABULARY)
    except Refusal as error:
        ok("[zkc-E244]" in str(error), "contract message membership is mirrored")
    else:
        raise AssertionError("duplicate contract message occurrence accepted")

    shared_challenge = copy.deepcopy(witnesses.SUMCHECK)
    c1_index = next(
        index
        for index, event in enumerate(shared_challenge["events"])
        if isinstance(event, Chal) and event.label == "c1"
    )
    shared_challenge["events"][c1_index:c1_index] = [
        slot("other_commitment", "scalar", True, ("other", "m", 0)),
        slot("other_value", "scalar", True, ("other", "m", 1)),
    ]
    shared_challenge["reduces"].append(
        reduce_row(
            label="other",
            contract="evalopen",
            consumed=["evaluation"],
            deps=["c1"],
            produced=[("other-opening", "single_opening")],
        )
    )
    shared_challenge["sinks"] = [
        route("residual", "other-opening", "shared-challenge-negative")
    ]
    try:
        validate_protocol(shared_challenge, VOCABULARY)
    except Refusal as error:
        ok("[zkc-E245]" in str(error), "exclusive challenge ownership is mirrored")
    else:
        raise AssertionError("challenge shared by two reductions was accepted")

    dropped_sink = copy.deepcopy(witnesses.SCHNORR)
    dropped_sink["sinks"] = []
    try:
        validate_protocol(dropped_sink, VOCABULARY)
    except Refusal as error:
        ok("is not linear" in str(error), "claim linearity refuses a dropped sink")
    else:
        raise AssertionError("unconsumed claim accepted")

    doubled_sink = copy.deepcopy(witnesses.SCHNORR)
    doubled_sink["sinks"] = doubled_sink["sinks"] * 2
    try:
        validate_protocol(doubled_sink, VOCABULARY)
    except Refusal as error:
        ok("is not linear" in str(error), "claim linearity refuses a doubled sink")
    else:
        raise AssertionError("doubly consumed claim accepted")

    forbidden_sink = copy.deepcopy(witnesses.SCHNORR)
    forbidden_sink["sinks"] = [route("residual", "evaluation", "negative")]
    try:
        validate_protocol(forbidden_sink, VOCABULARY)
    except Refusal as error:
        ok(
            "forbidden by policy" in str(error),
            "closed_proof refuses a residual sink",
        )
    else:
        raise AssertionError("residual sink accepted under closed_proof")

    padded_space = copy.deepcopy(witnesses.SCHNORR)
    chal_index = next(
        index
        for index, event in enumerate(padded_space["events"])
        if isinstance(event, Chal)
    )
    padded_event = padded_space["events"][chal_index]
    padded_space["events"][chal_index] = padded_event._replace(
        space="0" + padded_event.space
    )
    try:
        validate_protocol(padded_space, VOCABULARY)
    except Refusal as error:
        ok(
            "not minimal decimal" in str(error),
            "challenge-space spelling is exact",
        )
    else:
        raise AssertionError("zero-padded challenge space accepted")

    malformed_anchor = copy.deepcopy(witnesses.SCHNORR)
    malformed_anchor["sources"][0].anchors["statement"] = "sha256:not-a-digest"
    try:
        validate_protocol(malformed_anchor, VOCABULARY)
    except Refusal:
        ok(True, "malformed source anchor is refused")
    else:
        raise AssertionError("malformed source anchor accepted")

    descriptors = [
        [source.profile, source.anchors]
        for source in witnesses.KZG_BATCH["sources"]
    ]
    old_anchor_only = tagged_digest(
        "zkc/claim-vector\n",
        sorted([source.anchors for source in witnesses.KZG_BATCH["sources"]], key=canon_json),
    )
    ok(
        claim_vector_digest(descriptors) != old_anchor_only,
        "claim vector commits to full descriptors",
    )

    base = compute_id(witnesses.SCHNORR, VOCABULARY)
    renamed = witnesses.rename_protocol(witnesses.SCHNORR, "renamed")
    ok(compute_id(renamed, VOCABULARY) == base, "author labels are not identity")
    ok(len(compute_oir_id(witnesses.SCHNORR, VOCABULARY)) == 64, "OIR id shape")

    opaque_call = next(
        row
        for row in project(witnesses.RELATION_DIRECT, VOCABULARY)["program"]
        if row[0] == "check_call"
    )
    ok(
        opaque_call[3:5]
        == [
            "zkc.check.relation-predicate",
            VOCABULARY.digest_for(
                "check_contracts", "zkc.check.relation-predicate"
            ),
        ],
        "opaque check_call carries its contract id and content digest",
    )
    print(f"oracle: {checks} checks ok")


if __name__ == "__main__":
    from oracle.model import _self_test as package_self_test

    package_self_test()
