"""Small explicit-binding test authoring vocabulary, independent of the compiler.

These builders create /2 records directly. They never accept a serialized /1
module or candidate. Instruction sites and order are supplied by each test.
"""
import copy

FIELD = "bls12-381.fr"
GROUP = "bls12-381.g1"
PCS = "multilinear.kzg.bls12-381/1"
SUITE = "merlin3.bls12-381.fr64be/1"


def nominal(kind):
    if kind in ("bool", "index", "indices"):
        return kind
    identity = GROUP if kind in ("group", "groups") else PCS if kind in (
        "commitment", "proof", "prover_key", "verifier_key", "opening_state"
    ) else SUITE if kind == "transcript" else FIELD
    return f"{kind}:{identity}"


def arguments(contract):
    if contract in ("bool.and", "control.require"):
        return []
    if contract.startswith("pcs."):
        return [PCS]
    if contract.startswith("curve.") and contract != "curve.response":
        return [GROUP]
    if contract.startswith("transcript."):
        if contract == "transcript.challenge":
            return [SUITE]
        kind = contract.removeprefix("transcript.observe.")
        ty = nominal(kind)
        args = [] if kind == "bool" else [ty.split(":", 1)[1]]
        codec = f"zkcv.{kind}" + (".multilinear-kzg.bls12-381" if args == [PCS]
                                  else "." + args[0] if args else "") + "/1"
        return [SUITE, *args, codec]
    return [FIELD]


def module(functions, protocols, instances, entries):
    functions, protocols = copy.deepcopy((functions, protocols))
    bindings = {}
    for f in functions:
        f[2] = [[n, nominal(t)] for n, t in f[2]]
        f[3] = list(map(nominal, f[3]))
        f.append([f[1], []])
        if f[4] == "external":
            continue
        for op in f[4]:
            if op[0] == "op":
                key = op[2]
                bindings[key] = [key, key, arguments(key), ""]
    for p in protocols:
        p[4] = [[n, r, nominal(t)] for n, r, t in p[4]]
        p[5] = [[r, nominal(t)] for r, t in p[5]]
    return ["zkc.protocol/1", list(bindings.values()), functions, protocols,
            copy.deepcopy(instances), copy.deepcopy(entries)]


def declaration(key, name="binding", physical=False):
    implementation = "arkworks/" + key if physical else ""
    import json
    return (f'"pir.operation_binding"() <{{sym_name = "{name}", contract = "{key}", '
            f'arguments = {json.dumps(arguments(key))}, implementation = "{implementation}"}}> : () -> ()')


REPRESENTATIONS = {"bool": "native.bool/1", "field": "arkworks.fr/1",
                   "table": "arkworks.mle-lsb/1", "point": "arkworks.point/1",
                   "round": "arkworks.quadratic/1", "group": "arkworks.g1/1",
                   "groups": "arkworks.g1-vector/1", "rng": "host.resource/1",
                   "nonce": "host.resource/1", "transcript": "host.resource/1",
                   **dict.fromkeys(("prover_key", "verifier_key", "opening_state", "commitment", "proof"),
                                   "arkworks.multilinear-pcs/1")}
