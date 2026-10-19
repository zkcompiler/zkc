"""Runtime differential support: proof scenarios and runtime observations.

The scenarios are generic edits of a framed proof: the header, the framing
and each message's payload, chosen by the payload's shape and never by the
subject. A framed proof is the 8-byte magic, the 32-byte binding, then one
frame per message: an 8-byte little-endian length and the payload. A payload
is the 5-byte codec magic, a one-byte type tag and the value: 32 little-endian
bytes for a scalar field element, 48 for a compressed group element.

For each scenario the driver also names the payloads the runtime codec refuses
(`invalid`) and the payloads it reads as another value (`ones`), so that the
Lean prediction reads the same bytes the same way.
"""

HEADER = 40
FIELD_BYTES = 32
GROUP_BYTES = 48


def replace(data, offset, value):
    return data[:offset] + value + data[offset + len(value):]


def frames(proof):
    """The (offset of the length, offset of the payload, payload) of each frame."""
    result, offset = [], HEADER
    while offset < len(proof):
        length = int.from_bytes(proof[offset:offset + 8], "little")
        start = offset + 8
        result.append((offset, start, proof[start:start + length]))
        offset = start + length
    if offset != len(proof):
        raise ValueError("proof frames do not cover the proof")
    return result


def shape(payload):
    width = len(payload) - 6
    return "field" if width == FIELD_BYTES else "group" if width == GROUP_BYTES else "other"


def scenarios(proof):
    """Generic proof edits: (bytes, invalid payloads, payloads read as one, wrong-value)."""
    if proof[:8] != b"ZKCPRF00":
        raise ValueError("not a framed proof")
    found = frames(proof)
    result = {"honest": (proof, [], [], False)}
    if found:
        offset, start, payload = found[0]
        changed = replace(payload, 5, b"\x07")
        result["first-message-wrong-tag"] = (replace(proof, start, changed), [changed], [], False)
    fields = [frame for frame in found if shape(frame[2]) == "field"]
    groups = [frame for frame in found if shape(frame[2]) == "group"]
    if groups:
        _, start, payload = groups[0]
        changed = replace(payload, 12, bytes([payload[12] ^ 0x01]))
        result["group-message-not-in-group"] = (replace(proof, start, changed), [changed], [], False)
    if fields:
        _, start, payload = fields[0]
        changed = replace(payload, 6, b"\xff" * FIELD_BYTES)
        result["field-message-out-of-range"] = (replace(proof, start, changed), [changed], [], False)
    for index, (_, start, payload) in enumerate(found):
        if shape(payload) != "field":
            continue
        # The value is little-endian: its lowest bit flips, so the payload stays
        # canonical and decodes to another value, which the prediction reads as one.
        changed = replace(payload, 6, bytes([payload[6] ^ 0x01]))
        result[f"message-{index}-wrong-value"] = (replace(proof, start, changed), [], [changed], True)
    if found:
        offset, start, payload = found[-1]
        result["last-message-missing"] = (proof[:offset], [], [], False)
        result["last-message-truncated"] = (proof[:start + len(payload) // 2], [], [], False)
    result["trailing-byte"] = (proof + b"\x00", [], [], False)
    result["header-binding"] = (replace(proof, 8, bytes([proof[8] ^ 0x01])), [], [], False)
    return result


def capacity(instructions):
    return ["zkc.native-capacity/0", "65536", "4096", "16777216", "67108864",
            [str(instructions), "100000", "4294967296"], ["67108864", "268435456"]]


def observed(exit_code, report):
    """The runtime's observation in the vocabulary of the Lean prediction."""
    execution = report.get("execution") or {}
    stop = execution.get("stop") or {}
    code = report.get("code")
    kind = str(stop.get("kind", ""))
    transcript = [r for r in execution.get("resources") or [] if r.get("stage") == "transcript"]
    if code == "proof-header":
        outcome = "header"
    elif exit_code == 0:
        outcome = "accepted"
    elif code in ("artifact-rejected", "proof-trailing"):
        outcome = "returned"
    elif code == "proof-truncated":
        outcome = "truncated"
    elif kind == "Limit":
        outcome = "limit"
    elif kind.startswith("Decode"):
        outcome = "decode"
    elif kind.startswith("Explicit(") and kind.endswith(")"):
        outcome = "explicit:" + kind[len("Explicit("):-1].strip('"')
    else:
        outcome = f"other:{code}:{kind}"
    local = stop.get("local")
    return dict(outcome=outcome,
                site=stop.get("site") if outcome not in ("header", "truncated") else None,
                call=[local["site"], local["function"]] if local else None,
                used=execution.get("instructions"),
                transitions=transcript[0]["transitions"] if transcript else None,
                messages=execution.get("messages"),
                complete=code != "proof-trailing" if outcome in ("accepted", "returned") else None)


def lean_bytes(data):
    return "[" + ", ".join(str(byte) for byte in data) + "]"


PREDICTION = r'''def challengeZero : History Scalar Scalar → Id Scalar := fun _ => 0

def decodeWith (invalid ones : List (List UInt8)) : PhysicalType → List UInt8 →
    Option (Payload Scalar Scalar)
  | ⟨.data (.group domain), _⟩, payload => if invalid.contains payload then none
      else some (.group domain (if ones.contains payload then 1 else 0))
  | ⟨.data (.field domain), _⟩, payload => if invalid.contains payload then none
      else some (.field domain (if ones.contains payload then 1 else 0))
  | _, _ => none

def text : Option String → String
  | some value => "\"" ++ value ++ "\""
  | none => "null"

def cause : Cause → String
  | .limit => "limit" | .decode => "decode" | .truncated => "truncated"
  | .contract => "contract" | .kernel reason => "kernel:" ++ toString (repr reason)
  | .explicit .reject => "explicit:reject"
  | .explicit reason => "explicit:" ++ toString (repr reason)

def predict (budget : Nat) (binding bytes : List UInt8) (invalid ones : List (List UInt8)) : String :=
  if bytes.take 40 = magic ++ binding then
    let run := Id.run (execute installed Fresh.Actual.validator
      CONTEXT challengeZero
      (decodeWith invalid ones) budget DATA []
      (bytes.drop 40))
    let (outcome, site, call) := match run.result with
      | .returned _ => ("returned", none, none)
      | .stopped stop site call => (cause stop, site, call)
    "{\"outcome\": \"" ++ outcome ++ "\", \"site\": " ++ text site ++
      ", \"call\": " ++ (match call with
        | some (site, function) => "[\"" ++ site ++ "\", \"" ++ function ++ "\"]"
        | none => "null") ++
      ", \"used\": " ++ toString run.used ++ ", \"transitions\": " ++
      toString run.transitions ++ ", \"messages\": " ++ toString run.messages ++
      ", \"complete\": " ++ toString run.unread.isEmpty ++ "}"
  else "{\"outcome\": \"header\"}"'''


def prediction_data(entry, public):
    """The executable's data inputs for the prediction: the shapes of the
    public inputs (vector lengths and indices, which control the run) with every
    scalar value mapped to zero."""
    terms = []
    for index, (ty, name) in enumerate(zip(entry.types, entry.source_names)):
        value = public.get(name)
        tag = ty[0]
        if tag == "vector":
            terms.append(f".vector {json_text(ty[1])} [{', '.join('0' for _ in value)}]")
        elif tag == "index":
            terms.append(f".index {int(value)}")
        elif tag in ("field", "group"):
            terms.append(f".data (.{tag} {json_text(ty[1])} 0)")
        elif tag == "bool":
            terms.append(".data (.boolean false)")
        else:
            raise ValueError(f"unsupported public input type {ty}")
    return "[" + ", ".join(terms) + "]"


def json_text(value):
    import json
    return json.dumps(value)
