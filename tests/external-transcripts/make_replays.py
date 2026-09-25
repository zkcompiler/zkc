#!/usr/bin/env python3
"""Export archived transcript fixtures to explicit external_replay JSON.

This test-only protocol schedule is deliberately outside the native provider.
No crypto is implemented here. OpenVM input is the recorded observe/sample log,
not a full proof-container decoder; source origins identify exact log entries.
"""
import argparse
import json
from pathlib import Path

CORPUS = Path(__file__).resolve().parents[2] / "tests/fixtures/external-transcript"


def item(name, kind, values, wire_index=None, origin=None):
    return dict(id=name, origin=origin or f"fixture:{name}", wire_index=wire_index,
                kind=kind, values=values)


def monero(path, expected):
    proof = path.with_name(path.name.replace(".transcript.json", ".proof")).read_bytes()
    cursor = 0

    def take(n):
        nonlocal cursor
        result = proof[cursor:cursor+n]
        if len(result) != n:
            raise ValueError("truncated proof")
        cursor += n
        return result

    items = [item("V", "words", expected["V"])]
    for i, name in enumerate(["A", "A1", "B", "r1", "s1", "d1"]):
        items.append(item(name, "words", [take(32).hex()], i))
    rounds = None
    for side in ["L", "R"]:
        count = take(1)[0]
        if not 6 <= count <= 10 or rounds is not None and rounds != count:
            raise ValueError("outside canonical bounded fixture shape")
        rounds = count
        for j in range(count):
            index = 6 + j + (count if side == "R" else 0)
            items.append(item(f"{side}{j}", "words", [take(32).hex()], index))
    if cursor != len(proof):
        raise ValueError("trailing bytes")
    events = [dict(op="hash", items=["V"], output="Hv"),
              dict(op="update", items=["Hv"]),
              dict(op="update", items=["A"], expect=expected["y"]),
              dict(op="update", items=[], expect=expected["z"])]
    for i in range(rounds):
        events.append(dict(op="update", items=[f"L{i}", f"R{i}"], expect=expected["x"][i]))
    events.append(dict(op="update", items=["A1", "B"], expect=expected["e"]))
    return dict(version=1, profile="monero-hash-chain-v1", initial=expected["initial"],
                items=items, events=events,
                unobserved=[dict(item=n, guard="bp-plus:verification-equation") for n in ["r1", "s1", "d1"]])


def openvm(path, expected):
    items, events = [], []
    for i, entry in enumerate(expected):
        if entry["sample"]:
            events.append(dict(op="sample", expect=entry["value"]))
        else:
            name = f"observation{i}"
            items.append(item(name, "fields", [entry["value"]], origin=f"{path.name}:{i}"))
            events.append(dict(op="observe", items=[name]))
    return dict(version=1, profile="openvm-babybear-poseidon2-v1", items=items,
                events=events, unobserved=[])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_directory", type=Path)
    args = parser.parse_args()
    args.output_directory.mkdir(parents=True, exist_ok=True)
    count = 0
    for path in sorted(CORPUS.glob("*.transcript.json")):
        source = json.loads(path.read_text())
        replay = openvm(path, source) if "openvm" in path.name else monero(path, source)
        target = args.output_directory / path.name.replace(".transcript.json", ".replay.json")
        target.write_text(json.dumps(replay, separators=(",", ":")) + "\n")
        count += 1
    print(f"Exported {count} explicit event schedules to {args.output_directory}")


if __name__ == "__main__":
    main()
