"""Inert declaration substitution for independent conformance tests.

This module neither admits a contract nor supplies facts to any consumer. It
substitutes chosen closed names into generated terms to obtain *expected* port
spellings, which are compared with independently resolved API results. Formation,
requirements, representation selection and interpretation remain consumer-owned.
"""


def indexed(records):
    result = {record["name"]: record for record in records}
    assert len(result) == len(records), "duplicate inventory names"
    return result


def roots(operation):
    return [term for term in operation["scope"]
            if term["kind"] == "root"]


def instantiate(operation, arguments, declarations, catalog):
    """Substitute an acyclic inventory expression; this is not admission."""
    constructors = indexed(declarations["types"])
    domains = {entry["identity"]: entry for entry in catalog["domains"]}
    values = []
    supplied = iter(arguments)

    def spelling(constructor, args):
        parameters = constructors[constructor]["parameters"]
        assert len(parameters) == len(args), (constructor, args)
        if not parameters:
            return constructor
        if len(parameters) == 1 and parameters[0]["kind"] == "Domain":
            return f"{constructor}:{args[0]}"
        return f"{constructor}<{','.join(args)}>"

    for term in operation["scope"]:
        if term["kind"] == "natural":
            values.append(term["value"])
        elif term["kind"] == "project":
            values.append(domains[values[term["parent"]]]["associated"][term["member"]])
        elif term["kind"] == "apply":
            values.append(spelling(term["constructor"], [values[i] for i in term["arguments"]]))
        else:
            values.append(next(supplied))
    signature = operation["signature"]
    if signature["kind"] == "numerical":
        field = values[signature["fieldTerm"]]
        mask = next(supplied)
        assert all(bit in "01" for bit in mask) and len(mask) <= 1023
        assert next(supplied, None) is None, "excess closed arguments"
        return {
            "inputs": ["index"] + [f"{'vector' if bit == '1' else 'field'}:{field}" for bit in mask],
            "outputs": [f"{'vector' if signature['result'] == 'map' else 'field'}:{field}"],
        }
    assert signature["kind"] == "fixed"
    assert next(supplied, None) is None, "excess closed arguments"
    return {
        direction: [values[port["term"]] if "term" in port else spelling(port["constructor"], [values[i] for i in port["arguments"]])
                    for port in operation["signature"][direction]]
        for direction in ("inputs", "outputs")
    }


def dispositions(profile, declarations):
    """Every declaration needs an explicit review disposition, including absences."""
    operations = indexed(declarations["operations"])
    selected = {}
    for group, names in profile["operations"].items():
        for name in names:
            assert name not in selected, f"duplicate disposition: {name}"
            selected[name] = group
    assert selected.keys() == operations.keys(), {
        "without_disposition": sorted(operations.keys() - selected.keys()),
        "stale_dispositions": sorted(selected.keys() - operations.keys()),
    }
    types = indexed(declarations["types"])
    assigned = [name for names in profile["types"].values() for name in names]
    assert len(assigned) == len(set(assigned)), "duplicate type disposition"
    assert set(assigned) == types.keys(), {
        "types_without_disposition": sorted(types.keys() - set(assigned)),
        "stale_type_dispositions": sorted(set(assigned) - types.keys()),
    }
    return selected
