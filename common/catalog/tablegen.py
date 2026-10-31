"""Project neutral declarations into ordinary TableGen records.

This renderer supplies no interpretation or admission privilege. zkc-tblgen
independently validates the resulting declarations before producing native data.
"""


def symbol(category, name):
    """Injective ASCII spelling, independent of declaration array positions."""
    return (
        "Catalog"
        + category
        + "_"
        + "".join(
            chr(byte) if chr(byte).isascii() and chr(byte).isalnum() else f"_{byte:02x}"
            for byte in name.encode("utf-8")
        )
    )


def project(catalog):
    lines = []

    def q(value):
        # TableGen accepts UTF-8 and literal control bytes, but not JSON's
        # Unicode/control escapes. A code literal preserves carriage return,
        # which its quoted-string lexer otherwise refuses.
        def quoted(part):
            return (
                '"'
                + part.translate(
                    str.maketrans(
                        {
                            "\\": "\\\\",
                            '"': '\\"',
                            "\n": "\\n",
                            "\t": "\\t",
                        }
                    )
                )
                + '"'
            )

        parts = [quoted(part) for part in value.split("\r")]
        return (
            parts[0]
            if len(parts) == 1
            else "!strconcat(" + ", [{\r}], ".join(parts) + ")"
        )

    def seq(values):
        return "[" + ", ".join(values) + "]"

    uid = 0

    def emit(base, fields=(), name=None):
        nonlocal uid
        if name is None:
            name = "CatalogRecord" + str(uid)
            uid += 1
        body = " ".join(fields)
        lines.append(f"def {name} : {base}" + (" { " + body + " }" if body else ";"))
        return name

    def ordinal(i):
        return f"int ordinal = {i};"

    def flag(v):
        return str(int(v))

    def kind(k):
        if k["kind"] == "Domain":
            return symbol("Domain", k["sort"])
        return "TypeParameter" if k["kind"] == "Type" else "NatParameter"

    def inst(base):
        return emit(base)

    def kinds(ks):
        return seq(kind(k) for k in ks)

    meanings = {}
    for i, m in enumerate(catalog["mathematicalIdentities"]):
        fields = []
        if m["laws"]:
            law = m["laws"]
            f = [
                f"let {k} = {flag(v) if isinstance(v, bool) else q(v)};"
                for k, v in law.items()
                if k not in ("algebra", "signature")
            ]
            laws = emit(
                f"ZKC_ScalarLaws<{q(law['algebra'])}, {q(law['signature'])}>",
                f,
                symbol("Laws", m["name"]),
            )
            fields.append("let laws = " + laws + ";")
        meanings[m["name"]] = emit(
            f"ZKC_MathematicalIdentity<{q(m['name'])}, {i}>",
            fields,
            symbol("Meaning", m["name"]),
        )
    for i, m in enumerate(catalog["mathematicalIntrinsics"]):
        emit(
            f"ZKC_MathematicalIntrinsic<{q(m['name'])}, {meanings[m['identity']]}, {q(m['domainKind'])}, {i}, {m['naturals']}, {flag(m['domainPoints'])}, {flag(m['scalar'])}>"
        )
    mathematical = lines[:]
    lines.clear()
    sorts = {
        name: emit("ZKC_Sort<" + q(name) + ">", [ordinal(i)], symbol("Sort", name))
        for i, name in enumerate(catalog["sorts"])
    }
    for name, sort in sorts.items():
        emit(f"ZKC_Domain<{sort}>", name=symbol("Domain", name))
    types = {}
    for i, t in enumerate(catalog["types"]):
        fields = [
            ordinal(i),
            *[
                f"let {k} = {flag(t[k])};"
                for k in (
                    "nativeLocal",
                    "mathematical",
                    "participants",
                    "constructible",
                    "message",
                )
            ],
        ]
        types[t["name"]] = emit(
            f"ZKC_Type<{q(t['name'])}, {kinds(t['parameters'])}, {t['custody']}, {flag(t['copy'])}, {flag(t['drop'])}>",
            fields,
            symbol("Type", t["name"]),
        )
    caps = {
        c["name"]: emit(
            f"ZKC_Capability<{q(c['name'])}, {kinds(c['parameters'])}>",
            [ordinal(i)],
            symbol("Capability", c["name"]),
        )
        for i, c in enumerate(catalog["capabilities"])
    }
    members = {}
    for i, m in enumerate(catalog["members"]):
        a, b = (kind(m[k]) for k in ("owner", "result"))
        members[(m["owner"]["kind"], m["owner"]["sort"], m["name"])] = emit(
            f"ZKC_Member<{q(m['name'])}, {a}, {b}>", [ordinal(i)]
        )
    for i, (a, b) in enumerate(catalog["rules"]):
        emit(f"ZKC_Implication<{caps[a]}, {caps[b]}>", [ordinal(i)])
    families = {}
    for i, f in enumerate(catalog["families"]):
        family = f["family"]
        if family not in families:
            families[family] = emit(
                f"ZKC_TypeFamily<{q(family)}>", name=symbol("Family", family)
            )
        emit(
            f"ZKC_TypeFamilyCase<{families[family]}, {types[f['elementConstructor']]}, {types[f['resultConstructor']]}>",
            [ordinal(i)],
        )
    for i, a in enumerate(catalog["associatedTypes"]):
        owner = inst("ZKC_Parameter<DomainKind, " + q(a["sort"]) + ">")
        emit(
            f"ZKC_AssociatedType<{owner}, {q(a['member'])}, {types[a['constructor']]}>",
            [ordinal(i)],
        )
    for i, e in enumerate(catalog["exports"]):
        if "constructor" in e:
            name = e["constructor"]
            target = types.get(name, families.get(name))
            cls = "ZKC_TypeExport"
        else:
            target = caps[e["predicate"]]
            cls = "ZKC_CapabilityExport"
        emit(f"{cls}<{q(e['module'])}, {q(e['name'])}, {target}>", [ordinal(i)])
    operations = {
        o["name"]: symbol("Operation", o["name"]) for o in catalog["operations"]
    }
    # Counterparts are declared before the declarations referencing them, while
    # ordinals keep the original inventory order independently of generation order.
    done = set()
    pending = set()

    def operation(i, o, consumer=False):
        if not consumer and o["name"] in done:
            return
        if not consumer and o["name"] in pending:
            raise ValueError("cyclic derived counterpart")
        if not consumer:
            pending.add(o["name"])
        if "derivedCounterpart" in o:
            target = o["derivedCounterpart"]
            j = next(
                j for j, x in enumerate(catalog["operations"]) if x["name"] == target
            )
            operation(j, catalog["operations"][j])
        terms = []
        scope_kinds = []
        for t in o["scope"]:
            if t["kind"] == "root":
                p = kind(t["parameter"])
                term = emit(f"ZKC_Root<{q(t['name'])}, {p}>")
                parameter = t["parameter"]
            elif t["kind"] == "project":
                parent = t["parent"]
                owner = scope_kinds[parent]
                member = members[(owner["kind"], owner["sort"], t["member"])]
                term = emit(f"ZKC_Project<{terms[parent]}, {member}>")
                parameter = next(
                    m["result"]
                    for m in catalog["members"]
                    if m["name"] == t["member"] and m["owner"] == owner
                )
            elif t["kind"] == "natural":
                term = emit(f"ZKC_Natural<{t['value']}>")
                parameter = {"kind": "Nat", "sort": ""}
            else:
                term = emit(
                    f"ZKC_Apply<{types[t['constructor']]}, {seq(terms[a] for a in t['arguments'])}>"
                )
                parameter = {"kind": "Type", "sort": ""}
            terms.append(term)
            scope_kinds.append(parameter)

        def port(p):
            return (
                terms[p["term"]]
                if "term" in p
                else emit(
                    f"ZKC_Apply<{types[p['constructor']]}, {seq(terms[a] for a in p['arguments'])}>"
                )
            )

        sig = o["signature"]
        fields = ([] if consumer else [ordinal(i)]) + ["let stage = " + o["stage"] + ";"]
        if sig["kind"] == "fixed":
            inputs, outputs = (
                seq(port(p) for p in sig[k]) for k in ("inputs", "outputs")
            )
        else:
            inputs = outputs = "[]"
            fields.append(
                "let numerical = "
                + emit(
                    f"ZKC_NumericalSignature<{terms[sig['fieldTerm']]}, {q(sig['result'])}>"
                )
                + ";"
            )
        params = o["parameters"]
        f = []
        if "assetFormat" in params:
            f.append("let assetFormat = " + q(params["assetFormat"]) + ";")
        schema = emit(
            f"ZKC_Parameters<{q(params['validator'])}, {params['minimum']}, {params['maximum'] if params['maximum'] is not None else -1}>",
            f,
        )
        fields.append("let parameters = " + schema + ";")
        if "fieldTerm" in params:
            fields.append("let parameterField = " + terms[params["fieldTerm"]] + ";")
        facets = []
        for f in o.get("facets", []):
            k = f["kind"]
            base = "ZKC_" + k
            if k in (
                "PublicReplay",
                "DeterministicData",
                "AcceptanceGuard",
                "Conjunction",
                "SourceHistory",
                "ManagedHistory",
            ):
                facets.append(k)
                continue
            if k == "Mathematical":
                args = [meanings[f["identity"]]]
            elif k in ("History", "Observation", "Diagonal", "Contraction", "Coset"):
                keys = {
                    "History": ["stateInput", "stateOutput"],
                    "Observation": ["stateInput", "payloadInput", "stateOutput"],
                    "Diagonal": ["factorsInput", "valuesInput", "resultOutput"],
                    "Contraction": ["coefficientsInput", "valuesInput"],
                    "Coset": [
                        "shiftInput",
                        "sizeInput",
                        "sizeIsLength",
                        "vectorOutput",
                        "foldedOutput",
                    ],
                }[k]
                args = [str(int(f[x])) if f[x] is not None else "-1" for x in keys]
            elif k == "Sampling":
                args = [
                    {"Entropy": "Entropy", "Transcript": "TranscriptProvider"}[
                        f["provider"]
                    ],
                    {
                        "Field": "FieldSample",
                        "FieldVector": "VectorSample",
                        "BoundedIndex": "IndexSample",
                        "IndexBlock": "IndexBlockSample",
                    }[f["domain"]],
                    str(f["boundInput"] if f["boundInput"] is not None else -1),
                ]
                fields2 = [
                    f"let {x} = {f[x]};"
                    for x in ("stateInput", "valueOutput", "stateOutput")
                ]
                facets.append(emit(base + "<" + ", ".join(args) + ">", fields2))
                continue
            elif k == "DomainValue":
                args = [
                    f["rule"] + "Value",
                    str(f["output"]),
                    str(f.get("parameter", f.get("input", 0))),
                    str(f.get("otherInput", 1)),
                ]
            else:
                raise ValueError(k)
            facets.append(emit(base + "<" + ", ".join(args) + ">"))
        if not consumer:
            fields.append("let facets = " + seq(facets) + ";")
        if "derivedCounterpart" in o:
            fields.append(
                "let derivedCounterpart = " + operations[o["derivedCounterpart"]] + ";"
            )
        needs = seq(
            emit(
                f"ZKC_Holds<{caps[n['capability']]}, {seq(terms[a] for a in n['arguments'])}>"
            )
            for n in o["requirements"]
        )
        result = emit(
            (f"ZKC_ConsumerOperation<{operations[o['name']]}" if consumer
             else f"ZKC_Operation<{q(o['name'])}")
            + f", {seq(terms)}, {inputs}, {outputs}, {needs}>",
            fields,
            None if consumer else operations[o["name"]],
        )
        if not consumer:
            done.add(o["name"])
        return result

    for i, o in enumerate(catalog["operations"]):
        operation(i, o)
    for i, profile in enumerate(catalog["consumerProfiles"]):
        entries = [operation(j, dict(member, name=member["operation"]), consumer=True)
                   for j, member in enumerate(profile["operations"])]
        emit(
            f"ZKC_ConsumerProfile<{q(profile['name'])}, "
            f"{seq(types[t] for t in profile['typeConstructors'])}, "
            f"{seq(q(v) for v in profile['parameterValidators'])}, {seq(entries)}>",
            [ordinal(i), f"let implementation = {q(profile['implementation'])};"],
            symbol("ConsumerProfile", profile["name"]),
        )
    schema = 'include "zkc/Contracts/Declarations/Schema.td"\n'
    math = (
        "#ifndef ZKC_CATALOG_MATHEMATICAL\n#define ZKC_CATALOG_MATHEMATICAL\n"
        + schema
        + "\n".join(mathematical)
        + "\n#endif\n"
    )
    declarations = (
        "#ifndef ZKC_CATALOG_DECLARATIONS\n#define ZKC_CATALOG_DECLARATIONS\n"
        + schema
        + 'include "zkc/Contracts/Mathematical.td"\n'
        + "\n".join(lines)
        + "\n#endif\n"
    )
    return declarations, math
