"""Independent, source-driven replay of bounded Direct quartic Keccak FRI.

Only canonical native proof inputs and descriptor origins enter the replay.
No target output, bytecode interpreter, native prover or compiler is used.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re

from authentication_controls import authenticate
from coset_reference import CosetReference
from hash_chain_reference import Chain, QUARTIC_SUITE, rejection31le
from logical_tree import decode_tree, encode_tree


FIELD = "koala-bear.ext4-binomial3"
SCHEME = f"rows.merkle-keccak256.{FIELD}/0"
MATH = CosetReference(FIELD)


class Stop(Exception):
    def __init__(self, cause, revert, detail=None):
        super().__init__(cause)
        self.cause, self.revert, self.detail = cause, list(revert), detail


def require(condition, detail):
    if not condition:
        raise Stop("rejected:require", ("source", 16), detail)


def frame(tag, payload):
    return b"ZKCV\x00" + bytes([tag]) + payload


def index_wire(value):
    return frame(31, value.to_bytes(8, "little"))


def vector_wire(values):
    return frame(22, len(values).to_bytes(4, "little") + b"".join(
        MATH.arithmetic.coordinates(value) for value in values))


def indices_wire(values):
    return frame(68, len(values).to_bytes(4, "little") + b"".join(
        value.to_bytes(8, "little") for value in values))


def aggregate(tag, values):
    return frame(tag, (len(values) if tag == 69 else 0).to_bytes(4, "little")
                 + b"".join(len(value).to_bytes(4, "little") + value for value in values))


def decode(wire, kind):
    """Scan the WHOLE message before checking canonical scalar coordinates."""
    decode_value(wire, kind, canonical=False)
    return decode_value(wire, kind, canonical=True)


def decode_value(wire, kind, *, canonical):
    fixed = {"field": (21, 22), "index": (31, 14), "root": (79, 38)}
    tags = {"vector": 22, "path": 80, "packet": 69, "opening": 65}
    tag, width = fixed.get(kind, (tags.get(kind), None))
    if (width is not None and len(wire) != width) or (width is None and len(wire) < 10):
        raise Stop("artifact-stopped:Decode(Length)", ("decode", 2))
    if wire[:6] != b"ZKCV\x00" + bytes([tag]):
        raise Stop("artifact-stopped:Decode(Header)", ("decode", 3))
    if kind == "root":
        return wire[6:]
    if kind == "index":
        return int.from_bytes(wire[6:], "little")
    if kind in ("field", "vector", "path"):
        count = 1 if kind == "field" else int.from_bytes(wire[6:10], "little")
        if count > 1024:
            raise ValueError("unsupported-fixture:collection-resource-profile")
        start, element = (6 if kind == "field" else 10), (32 if kind == "path" else 16)
        if len(wire) != start + count * element:
            raise Stop("artifact-stopped:Decode(Length)", ("decode", 2))
        if kind == "path":
            return [wire[i:i + 32] for i in range(10, len(wire), 32)]
        values = [tuple(int.from_bytes(wire[i + j:i + j + 4], "little")
                        for j in range(0, 16, 4))
                  for i in range(start, len(wire), 16)]
        if canonical and any(x >= MATH.modulus for value in values for x in value):
            raise Stop("artifact-stopped:Decode(Scalar)", ("decode", 4))
        return values[0] if kind == "field" else values
    count = int.from_bytes(wire[6:10], "little")
    if kind == "packet" and count > 32:
        raise ValueError("unsupported-fixture:packet-resource-profile")
    # There is exactly one constructor in this source closure.
    if kind == "opening" and count != 0:
        raise Stop("artifact-stopped:Decode(Header)", ("decode", 3))
    at, children = 10, []
    expected = count if kind == "packet" else 2
    for ordinal in range(expected):
        if at + 4 > len(wire):
            raise Stop("artifact-stopped:Decode(Length)", ("decode", 2))
        size = int.from_bytes(wire[at:at + 4], "little")
        at += 4
        if size > len(wire) - at:
            raise Stop("artifact-stopped:Decode(Length)", ("decode", 2))
        child_kind = "opening" if kind == "packet" else ("vector", "path")[ordinal]
        children.append(decode_value(wire[at:at + size], child_kind, canonical=canonical))
        at += size
    if at != len(wire):
        raise Stop("artifact-stopped:Decode(Length)", ("decode", 2))
    return children


def profile(descriptor, sampling, queries):
    """Admit only this source recipe, with descriptor-owned opaque labels.

    This is a bounded structural profile, not a generic source/descriptor
    correspondence checker. The parent must authenticate the native deployment.
    """
    def check(condition, name):
        if not condition:
            raise ValueError("unsupported-descriptor:" + name)

    check(queries in (2, 8) and sampling in ("scalar", "block"), "parameters")
    check(isinstance(descriptor, list) and len(descriptor) == 9
          and descriptor[0] == "zkc.native-proof-descriptor/0", "shape")
    policy = descriptor[1]
    check(len(policy) == 12 and policy[0] == "zkc.native-proof-policy/0"
          and policy[4:8] == ["0", QUARTIC_SUITE, ["4"], ["1", "2", "3"]]
          and policy[9:] == ["zkc.framed/0", "", []]
          and descriptor[2] == "zkc.native-origin/0"
          and descriptor[6:8] == [[], []], "construction")
    entry, producer, validator = policy[1:4]
    check(producer == "role00000000" and validator == "role00000001", "roles")
    check(descriptor[4] == [[validator, "1", f"field:{FIELD}", f"zkcv.field.{FIELD}/0"],
                            [validator, "2", "index", "zkcv.index/0"],
                            [validator, "3", "index", "zkcv.index/0"]], "ports")
    selection = json.loads(descriptor[8])
    check(json.dumps(selection, sort_keys=True, separators=(",", ":")) == descriptor[8],
          "canonical-selection")
    check(set(selection) == {"authentication", "format", "order", "roots"}
          and selection["format"] == "zkc.oracle-selection/0"
          and selection["authentication"] == "atomic-blocks"
          and selection["order"] == "after-final-draw", "selection")
    roots = selection["roots"]
    check(set(roots) == {"kind", "entries"} and roots["kind"] == "exact"
          and len(roots["entries"]) == 1, "roots")
    root = roots["entries"][0]
    check(set(root) == {"entry", "grouping", "order", "path", "scheme"}
          and root["entry"] == entry and root["scheme"] == SCHEME
          and root["grouping"] in ("individual", "antipodal-pairs")
          and root["order"] in ("natural", "bit-reversed")
          and root["path"] == [39, 0]
          and all(type(component) is int and 0 <= component < 1 << 32
                  for component in root["path"]), "root-layout")
    kinds = ["message", "query", "message", "message",
             "index" if sampling == "scalar" else "indices", "message"]
    kinds += ["reconstructed-message", "message"] * 4
    check([r[0] for r in descriptor[3]] == kinds, "event-order")
    templates = []
    for ordinal, row in enumerate(descriptor[3]):
        parameters = (["32"] + ([str(queries)] if sampling == "block" else [])) if ordinal == 4 else []
        check(len(row) == 2 + len(parameters) and row[2:] == parameters, "event-parameters")
        template = decode_tree(bytes.fromhex(row[1]))
        check(encode_tree(template).hex() == row[1] and len(template) == 5
              and template[:2] == ["zkc.native-origin-template/0", entry]
              and template[3] == [], "template")
        for step in template[2]:
            check(len(step) == 3 and step[0] in ("apply", "repeat")
                  and all(isinstance(s, str) and 0 < len(s) <= 128
                          and all(33 <= ord(c) <= 126 for c in s) for s in step), "path-step")
        event = template[4]
        if ordinal in (1, 4):
            method, port = ("draw", "input_4") if ordinal == 1 else (
                "index" if sampling == "scalar" else "indices", "input_1")
            check(len(event) == 7 and event[0] == "query"
                  and event[3:] == [port, f"random.{FIELD}/0", method, validator], "query")
        else:
            direction = [validator, producer] if ordinal in (2, 5, 6, 8, 10, 12) else [producer, validator]
            check(len(event) == 6 and event[0] == "message" and event[2] == event[3]
                  and event[4:] == direction, "message")
        templates.append(template)
    paths = [t[2] for t in templates]
    outer = ["apply", entry, "s0"]
    check(all(p and p[0] == outer for p in paths), "entry-application")
    check([s[0] for s in paths[0]] == ["apply", "apply", "repeat"]
          and paths[0] == paths[1] == paths[2]
          and paths[3] == paths[0][:-1]
          and paths[0][-1][2] == "s46"
          and templates[1][4][1:3] == [paths[0][-1][1], "s54"]
          and templates[2][4][1:3] == [paths[0][-1][1], "s56_0"]
          and templates[3][4][1:3] == [paths[0][-1][1], "s125_0"], "commit-recipe")
    check(paths[4] == paths[5]
          and [s[0] for s in paths[4]] == (["apply", "apply", "repeat"] if sampling == "scalar"
                                       else ["apply", "apply"])
          and paths[4][1][:2] == paths[0][1][:2]
          and paths[4][1][2] == "label_71756572696573", "sampling-recipe")
    if sampling == "scalar":
        check(paths[4][-1][2] == "s12"
              and templates[4][4][1:3] == [paths[4][-1][1], "s13"]
              and templates[5][4][1:3] == [paths[4][-1][1], "s15_0"], "scalar-recipe")
    base = paths[6][:-1]
    check([s[0] for s in base] == ["apply", "apply", "apply", "repeat"]
          and base[1] == ["apply", paths[0][1][1], "s6"]
          and base[2][2] == "s3" and base[3][2] == "s58", "check-recipe")
    for ordinal in (6, 8, 10, 12):
        expected = base + ([["repeat", base[-1][1], "s100"]] if ordinal >= 10 else [])
        check(paths[ordinal] == paths[ordinal + 1]
              and paths[ordinal][:-1] == expected and paths[ordinal][-1][0] == "repeat"
              and re.fullmatch(r"oracle_0_[0-9]+_query_requests", paths[ordinal][-1][2]) is not None
              and templates[ordinal][4][2].endswith("_opening_request")
              and templates[ordinal + 1][4][2].endswith("_opening_response"), "opening-recipe")
    # Exact occurrence identities and constructor path belong to this bounded
    # source recipe. A matching suffix does not select a source occurrence.
    # The caller separately authenticates source identity/specialization.
    expected_draws = [["apply_13_apply_2_s0_s0_s54", "apply_13_apply_2_s0_s0_s56_0"],
                      ["apply_31_apply_2_s0_label_71756572696573_s13",
                       "apply_31_apply_2_s0_label_71756572696573_s15_0"]]
    if sampling == "block":
        expected_draws[1] = ["apply_31_apply_2_s0_label_71756572696573_label_706f736974696f6e73",
                             "apply_31_apply_2_s0_label_71756572696573_s8_0"]
    check(policy[8] == expected_draws, "draw-selection")
    message_indices = [i for i in range(14) if i not in (1, 4)]
    messages = descriptor[5]
    check(len(messages) == len(message_indices), "message-inventory")
    types = {}
    for row, ordinal in zip(messages, message_indices, strict=True):
        check(len(row) == 3 and row[0] == descriptor[3][ordinal][1], "message-origin")
        types[ordinal] = row[1:]
    check(types[0] == [f"commitment:{SCHEME}", f"zkcv.commitment.rows-merkle-keccak256.{FIELD}/0"]
          and types[2] == [f"field:{FIELD}", f"zkcv.field.{FIELD}/0"]
          and types[3] == [f"vector:{FIELD}", "zkc.native-data/0"]
          and types[5] == (["index", "zkcv.index/0"] if sampling == "scalar"
                           else ["indices", "zkc.native-data/0"]), "message-codecs")
    for parity, label in ((0, "request"), (1, "response")):
        first = types[6 + parity]
        check(all(types[i] == first for i in range(6 + parity, 14, 2))
              and first[1] == "zkc.native-data/0"
              and first[0].startswith("sequence<variant:") and first[0].endswith(">"), "packet-type")
        identity = json.loads(bytes.fromhex(first[0][17:-1]))
        check(identity[0] == "zkc.variant/0" and len(identity) == 2, "packet-identity")
        record = identity[1]
        check(record[:5] == [f"zkc.oracle.opening-{label}/0", entry.encode().hex(),
                             validator.encode().hex(), producer.encode().hex(), "0"], "packet-owner")
        check(record[5:7] == [["4"], ["0", "1", "2", "3", "5"]], "packet-inputs")
        payload = ["Record", "index"] if label == "request" else [
            "Constructor0", f"vector:{FIELD}", f"proof:{SCHEME}"]
        check(record[7:7 + len(payload)] == payload, "packet-payload")
        suffix = ([["8", "8", "8"], ["7", "9"], ["10"], ["6", "11"]]
                  if label == "request" else [["8", "9"], ["7", "10"], ["11"], ["6", "12"]])
        check(record[7 + len(payload):] == suffix, "packet-identity-layout")
    return templates, root


def invocation_root(fixture):
    descriptor = fixture["descriptor"]
    rows = [[*port[:3], wire] for port, wire in zip(descriptor[4], fixture["public"], strict=True)]
    return encode_tree(["zkc.native-proof-binding/0", "sha256", descriptor[2],
                        fixture["source"], *descriptor[1][1:4], descriptor, rows, fixture["context"]])


def reconstruct(fixture, *, sampling="scalar", queries=8, transition_budget=4096):
    """Return a complete reached trace/outcome, including budget and decode stops.

    Parameters are the explicitly selected fixture profile (5,0,3,queries).
    Native reported outputs, counters and decisions are never replay inputs.
    """
    if fixture.get("format") != "zkc.evm-native-fixture/0":
        raise ValueError("native-fixture-format")
    if type(transition_budget) is not int or not 0 <= transition_budget < 1 << 64:
        raise ValueError("transition-budget")
    templates, layout = profile(fixture["descriptor"], sampling, queries)
    shift_wire, round_wire, query_wire = map(bytes.fromhex, fixture["public"])
    shift, round_count, query_count = (decode(shift_wire, "field"), decode(round_wire, "index"),
                                       decode(query_wire, "index"))
    root = invocation_root(fixture)
    digest = hashlib.sha256(root).digest()
    proof = bytes.fromhex(fixture["proof"])
    if len(proof) > 65536 or len(root) > 262144 or len(bytes.fromhex(fixture["context"])) > 4096:
        raise ValueError("unsupported-fixture:ingress-resource-profile")
    trace = []
    chain, cursor, transitions, flushed = None, 0, 0, 0
    events, frames, openings, challenges, positions, values = [], [], [], [], [], []
    stop, decision, frontier, coefficients = None, None, None, []

    def flush():
        nonlocal flushed
        if chain is not None:
            trace.extend({"kind": "keccak256", "input": data.hex(), "output": hashed.hex(),
                          "status": "return"} for data, hashed in chain.calls[flushed:])
            flushed = len(chain.calls)

    def location(ordinal, coordinates):
        template = templates[ordinal]
        if len(coordinates) != sum(s[0] == "repeat" for s in template[2]):
            raise ValueError("reference-coordinate-count")
        return encode_tree(["zkc.native-origin/0", template[1], template[2],
                            list(map(str, coordinates)), template[4]])

    def debit(ordinal, coordinates):
        nonlocal transitions, frontier
        frontier = {"event": ordinal, "coordinates": coordinates,
                    "origin": location(ordinal, coordinates).hex(), "proof_position": cursor}
        if transitions == transition_budget:
            raise Stop("exhausted:resource-budget", ("resource", 8), "transcript-transition")
        transitions += 1

    def observe(ordinal, coordinates, wire):
        debit(ordinal, coordinates)
        begin = len(trace)
        chain.absorb(b"origin", location(ordinal, coordinates))
        chain.absorb(b"value", wire)
        flush()
        events.append({**frontier, "transition": transitions, "hash_start": begin,
                       "hash_end": len(trace), "wire": wire.hex()})

    def receive(ordinal, coordinates, kind):
        nonlocal cursor, frontier
        frontier = {"event": ordinal, "coordinates": coordinates, "proof_position": cursor,
                    "phase": "receive"}
        if cursor + 8 > len(proof):
            raise Stop("proof-truncated", ("decode", 5), "frame-length")
        start = cursor
        size = int.from_bytes(proof[cursor:cursor + 8], "little")
        cursor += 8
        if size > 65536:
            raise ValueError("unsupported-fixture:frame-resource-profile")
        if size > len(proof) - cursor:
            raise Stop("proof-truncated", ("decode", 5), "frame-payload")
        wire = proof[cursor:cursor + size]
        cursor += size
        frames.append({"event": ordinal, "coordinates": coordinates, "start": start,
                       "end": cursor, "wire": wire.hex()})
        value = decode(wire, kind)
        observe(ordinal, coordinates, wire)
        return value

    def request(ordinal, coordinates, kind):
        debit(ordinal, coordinates)
        begin = len(trace)
        chain.absorb(b"origin", location(ordinal, coordinates))
        decoder = None
        if kind == "field":
            blocks = []

            def answer():
                raw = chain.request(b"challenge", 64)
                blocks.append(raw)
                return raw

            value = tuple(rejection31le(answer, degree=4))
            examined, accepted = [], 0
            for attempt, raw in enumerate(blocks):
                for offset in range(0, 64, 4):
                    word = int.from_bytes(raw[offset:offset + 4], "little") & 0x7fffffff
                    examined.append({"attempt": attempt, "offset": offset, "word": word,
                                     "accepted": word < MATH.modulus})
                    accepted += word < MATH.modulus
                    if accepted == 4:
                        break
            decoder = {"blocks": [raw.hex() for raw in blocks], "words": examined}
            wire = frame(21, MATH.arithmetic.coordinates(value))
        else:
            chain.absorb(b"bound", (32).to_bytes(8, "little"))
            if kind == "block":
                chain.absorb(b"count", queries.to_bytes(8, "little"))
                raw = chain.request(b"indices", 8 * queries)
                value = [int.from_bytes(raw[i:i + 8], "little") & 31
                         for i in range(0, len(raw), 8)]
                wire = indices_wire(value)
            else:
                value = int.from_bytes(chain.request(b"index", 64)[:8], "little") & 31
                wire = index_wire(value)
        flush()
        events.append({**frontier, "transition": transitions, "hash_start": begin,
                       "hash_end": len(trace), "sample": value, "decoder": decoder})
        observe(ordinal + 1, coordinates, wire)
        return value

    def physical(position, rows):
        width = 2 if layout["grouping"] == "antipodal-pairs" else 1
        height = rows // width
        leaf, slot = position % height, position // height
        if layout["order"] == "bit-reversed":
            leaf = int(f"{leaf:0{height.bit_length() - 1}b}"[::-1], 2) if height > 1 else 0
        return width, height, leaf, slot

    def packet(ordinal, coordinates, layer, logical):
        """Group physical packets, then authenticate EVERY logical occurrence."""
        rows = 32 >> layer
        unique, groups, keys = [], [], []
        for position in logical:
            _, _, leaf, _ = physical(position, rows)
            key = (0, layer, leaf)
            if key not in keys:
                keys.append(key)
                unique.append(position)
            groups.append(keys.index(key))
        wire = aggregate(69, [aggregate(65, [index_wire(0), index_wire(layer), index_wire(p)])
                              for p in unique])
        # The final repeat is the reached request-window iteration, always zero
        # in this recipe. It is NOT an opening ordinal or a sampled position.
        coordinates = [*coordinates, 0]
        observe(ordinal, coordinates, wire)
        responses = receive(ordinal + 1, coordinates, "packet")
        require(len(responses) == len(unique), "packet-physical-response-length")
        answers = []
        for occurrence, (position, group) in enumerate(zip(logical, groups, strict=True)):
            row, path = responses[group]
            width, height, leaf, slot = physical(position, rows)
            begin = len(trace)
            valid, hashes = authenticate(FIELD, roots[layer], width, height, leaf, row, path)
            trace.extend(hashes)
            openings.append({"event": ordinal, "coordinates": coordinates, "layer": layer,
                             "logical_ordinal": occurrence, "position": position, "physical_group": group,
                             "leaf": leaf, "slot": slot, "width": width, "height": height,
                             "valid": valid, "hash_start": begin, "hash_end": len(trace)})
            require(valid, "merkle-authentication")
            answers.append(row[slot])
        return answers

    def fold(layer, position, pair):
        rows = 32 >> layer
        point = MATH.domain(MATH.power(shift, 1 << layer), rows)[position]
        inverse_x = MATH.power(point, MATH.modulus**4 - 2)
        half = MATH.embed(pow(2, -1, MATH.modulus))
        even = MATH.mul(MATH.add(*pair), half)
        odd = MATH.mul(MATH.mul(MATH.sub(*pair), half), inverse_x)
        return MATH.add(even, MATH.mul(challenges[layer], odd))

    roots = []
    try:
        if len(proof) < 40:
            raise Stop("proof-truncated", ("decode", 11))
        if proof[:8] != b"ZKCPRF00":
            raise Stop("proof-header", ("decode", 11))
        trace.append({"kind": "sha256", "input": root.hex(), "output": digest.hex(), "status": "return"})
        if proof[8:40] != digest:
            raise Stop("proof-header", ("decode", 12))
        cursor, chain = 40, Chain(QUARTIC_SUITE, root)
        flush()
        require(round_count == 3, "round-count")
        if shift == MATH.zero:
            raise Stop("refused:coset-zero-shift", ("source", 13))
        for layer in range(3):
            roots.append(receive(0, [layer], "root"))
            challenges.append(request(1, [layer], "field"))
        coefficients = receive(3, [], "vector")
        require(len(coefficients) == 1, "terminal-coefficient-count")
        require(query_count == queries, "query-count")
        if sampling == "scalar":
            for query in range(queries):
                positions.append(request(4, [query], "index"))
        else:
            positions.extend(request(4, [], "block"))
        for query, position in enumerate(positions):
            values.extend(packet(6, [query], 0, [position]))
            at = position & 15
            expected = fold(0, at, packet(8, [query], 0, [at, at + 16]))
            for step in range(2):
                layer = step + 1
                actual, = packet(10, [query, step], layer, [at])
                require(actual == expected, "fold-layer-consistency")
                at &= (32 >> layer) // 2 - 1
                pair = packet(12, [query, step], layer, [at, at + (32 >> layer) // 2])
                expected = fold(layer, at, pair)
            point = MATH.domain(MATH.power(shift, 8), 4)[at]
            require(MATH.horner(coefficients, point) == expected, "terminal-polynomial-consistency")
        frontier = {"phase": "eof", "proof_position": cursor}
        if cursor != len(proof):
            raise Stop("proof-trailing", ("decode", 13))
        decision = True
    except Stop as error:
        stop = error
    except ValueError as error:
        if str(error) != "challenge-rejection-limit":
            raise
        stop = Stop("exhausted:challenge-rejection-limit", ("resource", 15))
    flush()
    return {"format": "zkc.evm-expected-execution/0", "trace": trace,
            "decision": decision, "stop": stop.cause if stop else None,
            "stop_detail": stop.detail if stop else None,
            "evm_revert": stop.revert if stop else None,
            "transitions": transitions, "transition_budget": transition_budget,
            "proof_position": cursor, "proof_bytes": len(proof), "proof_consumed": cursor == len(proof),
            "source_sha256": fixture["source"],
            "proof_sha256": hashlib.sha256(proof).hexdigest(),
            "descriptor_sha256": hashlib.sha256(encode_tree(fixture["descriptor"])).hexdigest(),
            "parameters": [5, 0, 3, queries], "sampling": sampling,
            "resource_model": "transcript-transitions-only",
            "scope": "bounded-diagnostic" if queries == 2 else "original-eight-query",
            "frontier": frontier, "final_state": chain.state.hex() if chain else None,
            "positions": positions, "challenges": challenges, "coefficients": coefficients,
            "events": events, "frames": frames, "openings": openings,
            "outputs": {"0": frame(5, b"\x01").hex(), "2": indices_wire(positions).hex(),
                        "3": vector_wire(values).hex()} if decision else None}


def inspect(fixture):
    """Show source descriptors and proof framing, excluding native outcomes."""
    descriptor = fixture["descriptor"]
    proof, at, frames = bytes.fromhex(fixture["proof"]), 40, []
    while at < len(proof):
        size = int.from_bytes(proof[at:at + 8], "little")
        wire = proof[at + 8:at + 8 + size]
        frames.append({"offset": at, "size": size, "prefix": wire[:32].hex()})
        at += 8 + size
    return {"events": [[row[0], decode_tree(bytes.fromhex(row[1])), *row[2:]]
                       for row in descriptor[3]], "frames": frames}


def controls(fixture, directory, *, sampling, queries):
    """Reference-only mutations of an existing native proof; never a prover."""
    from message_frames import children, replace_child

    directory.mkdir(parents=True, exist_ok=True)
    full = reconstruct(fixture, sampling=sampling, queries=queries)
    if full["decision"] is not True:
        raise ValueError("controls-require-a-complete-honest-native-fixture")
    proof = bytes.fromhex(fixture["proof"])
    spans = full["frames"]
    cases = []

    def save(name, candidate, *, budget=4096, expected=None):
        result = reconstruct(candidate, sampling=sampling, queries=queries, transition_budget=budget)
        if expected is not None and (result["stop"], result["stop_detail"]) != expected:
            raise AssertionError(f"{name}: unexpected reference stop")
        (directory / f"{name}.json").write_text(json.dumps(result, indent=2) + "\n")
        cases.append({"case": name, "decision": result["decision"], "stop": result["stop"],
                      "detail": result["stop_detail"], "transitions": result["transitions"],
                      "proof_position": result["proof_position"], "primitives": len(result["trace"]),
                      "evm_revert": result["evm_revert"]})
        return result

    def changed(ordinal, wire):
        span = spans[ordinal]
        return fixture | {"proof": (proof[:span["start"]] + len(wire).to_bytes(8, "little")
                                    + wire + proof[span["end"]:]).hex()}

    for budget in sorted({0, 1, 9, 10, 11, 26, 27, 28, 63, 64, 65,
                          full["transitions"] - 1, full["transitions"]}):
        result = save(f"budget-{budget}", fixture, budget=budget)
        if budget < full["transitions"]:
            if (result["transitions"] != budget or result["evm_revert"] != ["resource", 8]
                    or result["trace"] != full["trace"][:len(result["trace"])]):
                raise AssertionError("incorrect resource frontier")
        elif result["trace"] != full["trace"]:
            raise AssertionError("completion budget changed the trace")
    for name, wire, cause, detail in (
        ("trailing", proof + b"\x00", "proof-trailing", None),
        ("short-header", proof[:39], "proof-truncated", None),
        ("wrong-magic", bytes([proof[0] ^ 1]) + proof[1:], "proof-header", None),
        ("wrong-binding", proof[:8] + bytes([proof[8] ^ 1]) + proof[9:], "proof-header", None),
        ("short-first-length", proof[:44], "proof-truncated", "frame-length"),
        ("short-first-payload", proof[:85], "proof-truncated", "frame-payload"),
        ("short-final-payload", proof[:-1], "proof-truncated", "frame-payload"),
    ):
        result = save(name, fixture | {"proof": wire.hex()}, expected=(cause, detail))
        if name in ("short-header", "wrong-magic") and result["trace"]:
            raise AssertionError("header refusal reached an invocation hash")
        if name == "wrong-binding" and result["trace"] != full["trace"][:1]:
            raise AssertionError("binding refusal must reach exactly the invocation hash")
    masking_budget = min(64, full["transitions"] - 1)
    masked = save(f"budget{masking_budget}-before-short-tail", fixture | {"proof": proof[:-1].hex()},
                  budget=masking_budget)
    limited = reconstruct(fixture, sampling=sampling, queries=queries, transition_budget=masking_budget)
    if masked["trace"] != limited["trace"] or masked["stop"] != limited["stop"]:
        raise AssertionError("unreached malformed tail changed the earlier frontier")
    save("terminal-empty", changed(3, vector_wire([])),
         expected=("rejected:require", "terminal-coefficient-count"))
    terminal = vector_wire([MATH.add(full["coefficients"][0], MATH.one)])
    save("terminal-changed", changed(3, terminal),
         expected=("rejected:require", "merkle-authentication"))
    first_root = bytearray.fromhex(spans[0]["wire"])
    first_root[6] ^= 1
    save("wrong-root", changed(0, bytes(first_root)),
         expected=("rejected:require", "merkle-authentication"))
    packet_wire = bytes.fromhex(spans[4]["wire"])
    row, path = children(children(packet_wire)[0])
    noncanonical = row[:10] + MATH.modulus.to_bytes(4, "little") + row[14:]
    wrong_row = row[:10] + ((int.from_bytes(row[10:14], "little") + 1)
                           % MATH.modulus).to_bytes(4, "little") + row[14:]
    wrong_path = path[:10] + bytes([path[10] ^ 1]) + path[11:]
    short_path = frame(80, (int.from_bytes(path[6:10], "little") - 1).to_bytes(4, "little") + path[10:-32])
    for name, wire, cause, detail in (
        ("wrong-row", replace_child(packet_wire, [0, 0], wrong_row), "rejected:require", "merkle-authentication"),
        ("wrong-path", replace_child(packet_wire, [0, 1], wrong_path), "rejected:require", "merkle-authentication"),
        ("short-path", replace_child(packet_wire, [0, 1], short_path), "rejected:require", "merkle-authentication"),
        ("noncanonical-row", replace_child(packet_wire, [0, 0], noncanonical), "artifact-stopped:Decode(Scalar)", None),
        ("wrong-constructor", replace_child(packet_wire, [0],
                                            children(packet_wire)[0][:6] + (1).to_bytes(4, "little")
                                            + children(packet_wire)[0][10:]), "artifact-stopped:Decode(Header)", None),
        ("empty-responses", aggregate(69, []), "rejected:require", "packet-physical-response-length"),
        ("scan-before-scalar", replace_child(replace_child(packet_wire, [0, 0], noncanonical),
                                             [0, 1], path[:-1]), "artifact-stopped:Decode(Length)", None),
    ):
        save(name, changed(4, wire), expected=(cause, detail))
    # Verify explicit refusals before root hashing; these are not source stops.
    def root_path(descriptor, value):
        selection = json.loads(descriptor[8])
        selection["roots"]["entries"][0]["path"][0] = value
        descriptor[8] = json.dumps(selection, sort_keys=True, separators=(",", ":"))

    for name, alter in (
        ("unrelated-draw-prefix", lambda d: d[1][8][0].__setitem__(0, "unrelated_" + d[1][8][0][0])),
        ("unrelated-delivery-prefix", lambda d: d[1][8][0].__setitem__(1, "unrelated_" + d[1][8][0][1])),
        ("negative-root-ordinal", lambda d: root_path(d, -1)),
        ("overflowing-root-ordinal", lambda d: root_path(d, 1 << 32)),
        ("unrelated-root-ordinal", lambda d: root_path(d, 38)),
        ("boolean-root-ordinal", lambda d: root_path(d, True)),
        ("unexpected-request-bound", lambda d: d[3][4].__setitem__(2, "16")),
        ("unexpected-event", lambda d: d[3][6].__setitem__(0, "message")),
        ("unexpected-gate", lambda d: d[1][11].append(["unknown", "0"])),
        ("unexpected-witness", lambda d: d[7].append([])),
    ):
        descriptor = json.loads(json.dumps(fixture["descriptor"]))
        alter(descriptor)
        try:
            reconstruct(fixture | {"descriptor": descriptor}, sampling=sampling, queries=queries)
        except ValueError as error:
            if not str(error).startswith("unsupported-descriptor:"):
                raise
            cases.append({"case": name, "refusal": str(error)})
        else:
            raise AssertionError("unexpected descriptor was accepted")
    (directory / "cases.json").write_text(json.dumps(cases, indent=2) + "\n")
    return {"cases": len(cases), "output": str(directory)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fixture", type=Path, required=True)
    parser.add_argument("--inspect", action="store_true")
    parser.add_argument("--sampling", choices=("scalar", "block"), default="scalar")
    parser.add_argument("--queries", type=int, choices=(2, 8), default=8)
    parser.add_argument("--transition-budget", type=int, default=4096)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--controls", type=Path, help="write reference-only mutation/frontier evidence")
    parser.add_argument("--expectation", type=Path, help="write the four-field parent adapter expectation")
    parser.add_argument("--fork", choices=("osaka", "prague", "cancun"))
    parser.add_argument("--check-native", action="store_true",
                        help="compare the independently derived outcome and returned public values")
    args = parser.parse_args()
    fixture = json.loads(args.fixture.read_text())
    if args.controls:
        print(json.dumps(controls(fixture, args.controls, sampling=args.sampling, queries=args.queries)))
        return
    if args.inspect:
        result = inspect(fixture)
    else:
        result = reconstruct(fixture, sampling=args.sampling, queries=args.queries,
                             transition_budget=args.transition_budget)
        if args.check_native:
            if result["decision"] != fixture["decision"] or result["stop"] != fixture["native_error"]:
                raise AssertionError("independent/native outcome disagreement")
            if result["outputs"] is not None and result["outputs"] != fixture["outputs"]:
                raise AssertionError("independent/native output disagreement")
            resources = [row for row in fixture.get("native", {}).get("resources", [])
                         if row.get("stage") == "transcript"]
            if resources and (len(resources) != 1 or resources[0]["transitions"] != result["transitions"]):
                raise AssertionError("independent/native transition count disagreement")
    if args.expectation:
        if not args.fork or args.inspect:
            parser.error("--expectation requires --fork and a replay")
        expected = {key: result[key] for key in ("proof_sha256", "trace", "evm_revert")}
        args.expectation.write_text(json.dumps(expected | {"fork": args.fork}, indent=2) + "\n")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
        summary = {key: result[key] for key in (
            "decision", "stop", "stop_detail", "evm_revert", "transitions", "proof_position",
            "proof_bytes", "proof_sha256", "parameters", "scope", "positions")} if not args.inspect else {}
        print(json.dumps(summary | ({"primitives": len(result["trace"])} if not args.inspect else
                                    {"events": len(result["events"]), "frames": len(result["frames"])})))
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
