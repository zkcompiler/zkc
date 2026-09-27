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
            if "parent" not in term and "arguments" not in term and "constant" not in term]


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
        if "constant" in term:
            values.append(str(term["constant"]))
        elif "parent" in term:
            values.append(domains[values[term["parent"]]]["associated"][term["name"]])
        elif "arguments" in term:
            values.append(spelling(term["name"], [values[i] for i in term["arguments"]]))
        else:
            values.append(next(supplied))
    assert next(supplied, None) is None, "excess closed arguments"
    return {
        direction: [spelling(port["constructor"], [values[i] for i in port["arguments"]])
                    for port in operation[direction]]
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
