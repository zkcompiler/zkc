"""Deterministic PIR encoder/closure differential generator.

The generator stays inside the shipped semantic vocabulary.  Every case is a
valid Schnorr terminal closure, but labels, auxiliary transcript material,
dependency sets, challenge domains/spaces, and trailing proof layout vary.
This exercises generic spine normalization without arbitrary check kinds or
fixture-specific terminal logic.
"""

from __future__ import annotations

import random
import sys

from . import model
from .model import Bind, Chal, Check, Slot
from .witnesses import EMPTY_DIGEST, TOY_KAPPA, ref_digest


SEED = 711
VARIANTS = 12
SPACES = ["61", "1024", "2147483648", "2305843009213693952"]


def _variant(rng: random.Random, index: int) -> tuple[str, dict]:
    statement = ref_digest(f"fuzz.statement.{index}")
    events = []
    classes: dict[str, str] = {}
    absorbed: list[str] = []

    for auxiliary in range(rng.randint(0, 2)):
        label = f"public_{auxiliary}"
        payload_class = rng.choice(["tg", "scalar"])
        classes[label] = payload_class
        events.append(model.bind(label, payload_class, "instance"))
        absorbed.append(label)

    classes["statement"] = "tg"
    events.append(model.bind("statement", "tg", "instance"))
    absorbed.append("statement")

    for auxiliary in range(rng.randint(0, 2)):
        label = f"message_{auxiliary}"
        payload_class = rng.choice(["tg", "scalar"])
        classes[label] = payload_class
        events.append(model.slot(label, payload_class, True))
        absorbed.append(label)

    classes["commitment"] = "tg"
    events.append(model.slot("commitment", "tg", True, ("sig", "a", 0)))
    absorbed.append("commitment")

    mandatory = {"statement", "commitment"}
    dependencies = [
        label
        for label in absorbed
        if label in mandatory or rng.random() < 0.55
    ]
    classes["challenge"] = "scalar"
    events.append(
        model.chal(
            "challenge",
            "scalar",
            f"fuzz.{index}.challenge",
            rng.choice(SPACES),
            dependencies,
        )
    )

    classes["response"] = "scalar"
    events.append(model.slot("response", "scalar", True))
    if rng.random() < 0.5:
        classes["trailer"] = rng.choice(["tg", "scalar"])
        events.append(model.slot("trailer", classes["trailer"], False))

    events.append(
        model.check(
            "equation",
            "zkc.check.schnorr-equation",
            ["statement", "commitment", "challenge", "response"],
            expr=[
                "eq",
                ["g_exp", ["const", "g"], ["in", 3]],
                ["g_mul", ["in", 1], ["g_exp", ["in", 0], ["in", 2]]],
            ],
        )
    )

    protocol = {
        "policy": "closed_proof",
        "kappa": TOY_KAPPA,
        "sources": [
            model.source(
                "relation",
                "opaque_relation",
                {"contract": EMPTY_DIGEST, "statement": statement},
            )
        ],
        "events": events,
        "reduces": [
            model.reduce_row(
                "sig",
                "sigma",
                ["relation"],
                ["challenge"],
                [("evaluation", "schnorr_evaluation")],
                checks={"equation": "equation"},
                anchors=[{"statement": statement}],
            )
        ],
        "material_bindings": [model.material("statement", statement)],
        "sinks": [
            model.discharge(
                "evaluation",
                "zkc.terminal.schnorr-evaluation",
                {"equation": "equation"},
            )
        ],
    }
    model.validate_protocol(protocol, model.VOCABULARY)
    return f"fuzz{index}", protocol


def variants() -> list[tuple[str, dict]]:
    rng = random.Random(SEED)
    return [_variant(rng, index) for index in range(VARIANTS)]


def _attribute(value) -> str:
    if isinstance(value, str):
        return f'"{value}"'
    if isinstance(value, int):
        return str(value)
    if value is None:
        return "null"
    if isinstance(value, list):
        return "[" + ", ".join(_attribute(member) for member in value) + "]"
    if isinstance(value, dict):
        return "{" + ", ".join(
            f"{key} = {_attribute(member)}" for key, member in sorted(value.items())
        ) + "}"
    raise TypeError(f"cannot spell MLIR attribute {value!r}")


def _emit_protocol(name: str, protocol: dict, output: list[str]) -> None:
    classes: dict[str, str] = {}
    for event in protocol["events"]:
        if isinstance(event, (Bind, Slot)):
            classes[event.label] = event.payload_class
        elif isinstance(event, Chal):
            classes[event.label] = event.payload_class

    def typed_operands(labels: list[str]) -> str:
        values = ", ".join("%" + label for label in labels)
        types = ", ".join(f'!pir.val<"{classes[label]}">' for label in labels)
        return f"{values} : {types}"

    kappa = protocol["kappa"]
    output.append(
        f'pir.protocol "{name}" kappa {_attribute(kappa)} policy "closed_proof" {{'
    )
    source = protocol["sources"][0]
    output.append(
        f'  %{source.label} = pir.instantiate "{source.label}" anchors '
        f'{_attribute(source.anchors)} : !pir.claim<"{source.profile}">'
    )
    output.append("  %t0 = pir.begin")
    thread = "%t0"
    step = 0
    for event in protocol["events"]:
        if isinstance(event, Check):
            line = (
                f'  pir.check "{event.label}" contract "{event.contract}" '
                f'({typed_operands(event.inputs)})'
            )
            if event.params:
                line += " params " + _attribute(event.params)
            if event.semantic_args:
                line += " semantic_args " + _attribute(event.semantic_args)
            if event.expr is not None:
                line += " expr " + _attribute(event.expr)
            output.append(line)
            continue

        step += 1
        next_thread = f"%t{step}"
        if isinstance(event, Bind):
            line = (
                f'  {next_thread}, %{event.label} = pir.bind {thread} '
                f'"{event.label}" : "{event.payload_class}" stage {event.stage}'
            )
        elif isinstance(event, Slot):
            line = (
                f'  {next_thread}, %{event.label} = pir.slot {thread} '
                f'"{event.label}" : "{event.payload_class}"'
            )
            if not event.absorbed:
                line += " unabsorbed"
            if event.membership is not None:
                instance, role, member_index = event.membership
                line += f' in "{instance}" as "{role}"'
                if member_index:
                    line += f" idx {member_index}"
        elif isinstance(event, Chal):
            line = f'  {next_thread}, %{event.label} = pir.chal {thread}'
            if event.deps:
                line += f" deps({typed_operands(event.deps)})"
            line += (
                f' "{event.label}" : "{event.payload_class}" '
                f'domain "{event.domain}" space "{event.space}"'
            )
        else:
            raise AssertionError(f"unexpected fuzz event {event!r}")
        output.append(line)
        thread = next_thread
    output.append(f"  pir.end {thread}")

    reduction = protocol["reduces"][0]
    consumed = ", ".join("%" + label for label in reduction.consumed)
    consumed_types = ", ".join(
        '!pir.claim<"opaque_relation">' for _ in reduction.consumed
    )
    produced_label, produced_profile = reduction.produced[0]
    reduction_checks = ", ".join(
        f'{role} = "{label}"' for role, label in sorted(reduction.checks.items())
    )
    output.append(
        f'  %{produced_label} = pir.reduce "{reduction.label}" contract '
        f'"{reduction.contract}" '
        f'({consumed} : {consumed_types}) deps({typed_operands(reduction.deps)}) '
        f'checks {{{reduction_checks}}} '
        f'anchors {_attribute(reduction.anchors)} '
        f'-> !pir.claim<"{produced_profile}">'
    )
    binding = protocol["material_bindings"][0]
    output.append(
        f'  pir.material_bind %{binding.value} to "{binding.semantic_ref}" : '
        f'!pir.val<"{classes[binding.value]}">'
    )
    sink = protocol["sinks"][0]
    check_map = ", ".join(
        f'{role} = "{label}"' for role, label in sorted(sink.checks.items())
    )
    output.append(
        f'  pir.discharge %{sink.claim} : !pir.claim<"{produced_profile}"> '
        f'rule "{sink.rule}" checks {{{check_map}}}'
    )
    output.append("}")


def main(argv: list[str] | None = None) -> None:
    args = list(sys.argv[1:] if argv is None else argv)
    if args == ["mlir"]:
        lines: list[str] = []
        for name, protocol in variants():
            _emit_protocol(name, protocol, lines)
        sys.stdout.write("\n".join(lines) + "\n")
    elif args == ["ids"]:
        for _name, protocol in variants():
            print(f'id "{model.compute_id(protocol, model.VOCABULARY)}"')
    else:
        raise SystemExit("usage: python -m oracle.fuzz (mlir | ids)")


if __name__ == "__main__":
    main()
