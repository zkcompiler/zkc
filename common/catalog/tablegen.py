"""Project neutral declarations into ordinary TableGen records.

This renderer supplies no interpretation or admission privilege. zkc-tblgen
independently validates the resulting declarations before producing native data.
The native installation document is projected into its own file, so the logical
catalog records never contain physical choices. Every row is projected
explicitly; record names are presentation only.
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


def project(catalog, installation):
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
                    "sourceData",
                )
            ],
        ]
        if t["collection"] is not None:
            c = t["collection"]
            fields.append(
                f"let collection = ZKC_TypeCollection<{c['rank']}, {q(c['element'])}>;"
            )
        if t["setup"] is not None:
            fields.append(f"let setup = {q(t['setup'])};")
        types[t["name"]] = emit(
            f"ZKC_Type<{q(t['name'])}, {kinds(t['parameters'])}, {t['custody']}, {flag(t['copy'])}, {flag(t['drop'])}>",
            fields,
            symbol("Type", t["name"]),
        )
    caps = {
        c["name"]: emit(
            f"ZKC_Capability<{q(c['name'])}, {kinds(c['parameters'])}, "
            f"{seq(q(m) for m in c['requires'])}, {seq(q(m) for m in c['permits'])}>",
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
    def source_term(t):
        if "constructor" in t:
            return inst(f"ZKC_SourceTerm<-1, \"\", {q(t['constructor'])}>")
        return inst(f"ZKC_SourceTerm<{t['static']}, {q(t.get('member', ''))}>")

    def source_output(t):
        return seq([] if t is None else [source_term(t)])

    for i, r in enumerate(catalog["frontendRules"]):
        emit(f"ZKC_FrontendRule<{q(r['name'])}, {q(r['kind'])}, {kinds(r['statics'])}, "
             f"{seq(source_term(t) for t in r['inputs'])}, {source_output(r['output'])}>", [ordinal(i)])
    for i, d in enumerate(catalog["frontendDeclarations"]):
        statics = seq(inst(f"ZKC_SourceStatic<{q(s['name'])}, {kind(s['parameter'])}>") for s in d["statics"])
        inputs = seq(inst(f"ZKC_SourceInput<{q(s['name'])}, {source_term(s['type'])}>") for s in d["inputs"])
        emit(f"ZKC_FrontendDeclaration<{q(d['identity'])}, {q(d['owner'])}, {q(d['name'])}, {q(d['kind'])}, "
             f"{statics}, {inputs}, {source_output(d['output'])}, {q(d['association']['kind'])}, "
             f"{q(d['association']['target'])}, {flag(d['implicit'])}>", [ordinal(i)])
    for i, n in enumerate(catalog["frontendNotations"]):
        fixity = n["fixity"] or {"associativity": "", "precedence": 0}
        emit(f"ZKC_FrontendNotation<{q(n['owner'])}, {q(n['symbol'])}, {q(fixity['associativity'])}, "
             f"{fixity['precedence']}, {q(n['target'])}, {flag(n['public'])}>", [ordinal(i)])
    for i, c in enumerate(catalog["frontendConstructors"]):
        emit(f"ZKC_FrontendConstructor<{q(c['name'])}>", [ordinal(i)])
    for i, h in enumerate(catalog["frontendHomes"]):
        emit(f"ZKC_FrontendHome<{q(h['constructor'])}, {q(h['module'])}, {seq(q(m) for m in h['members'])}>", [ordinal(i)])
    for i, m in enumerate(catalog["serviceSignatures"]):
        emit(f"ZKC_ServiceSignature<{q(m['name'])}, {q(m['capability'])}>", [ordinal(i)])
    for i, m in enumerate(catalog["serviceMethods"]):
        emit(f"ZKC_ServiceMethod<{q(m['name'])}, {q(m['signature'])}, {q(m['capability'])}>", [ordinal(i)])
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
            elif k in (
                "History",
                "Succession",
                "Observation",
                "Diagonal",
                "Contraction",
                "Coset",
            ):
                keys = {
                    "History": ["stateInput", "stateOutput"],
                    "Succession": ["stateInput", "stateOutput"],
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
    project_instances(catalog, emit, ordinal, flag, q, seq)
    native = project_installation(installation, q, seq, flag)
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
    return declarations, math, native


def project_instances(catalog, emit, ordinal, flag, q, seq):
    """Installed-instance rows. Nested facts are records with explicit fields."""
    for i, d in enumerate(catalog["domains"]):
        fields = [ordinal(i)]
        if "field" in d:
            facts = d["field"]
            structure = facts["structure"]
            if structure["kind"] == "prime":
                shape = emit(f"ZKC_FieldStructure<{q(structure['kind'])}>")
            else:
                terms = seq(
                    f"ZKC_ReductionTerm<{e}, {q(c)}>" for e, c in structure["reduction"]
                )
                shape = emit(
                    f"ZKC_FieldStructure<{q(structure['kind'])}>",
                    [
                        f"let over = {q(structure['over'])};",
                        f"let degree = {structure['degree']};",
                        f"let reduction = {terms};",
                    ],
                )
            extra = []
            if facts["twoAdic"] is not None:
                t = facts["twoAdic"]
                convention = emit(
                    f"ZKC_TwoAdicConvention<{q(t['convention'])}, {q(t['maximalRoot'])}, "
                    f"{t['twoAdicity']}, {q(t['ordering'])}>"
                )
                extra.append(f"let twoAdic = {convention};")
            record = emit(
                f"ZKC_FieldFacts<{q(facts['characteristic'])}, {shape}>", extra
            )
            fields.append(f"let fieldFacts = {record};")
        if "transcript" in d:
            facts = d["transcript"]
            extra = [] if facts["hash"] is None else [f"let hash = {q(facts['hash'])};"]
            record = emit(
                f"ZKC_TranscriptFacts<{q(facts['family'])}, {q(facts['decoder'])}, "
                f"{flag(facts['bindsSuite'])}>",
                extra,
            )
            fields.append(f"let transcriptFacts = {record};")
        if "commitment" in d:
            facts = d["commitment"]
            extra = [
                f"let {key} = {q(value) if isinstance(value, str) else value};"
                for key, value in facts.items()
                if key != "scheme"
            ]
            record = emit(f"ZKC_CommitmentFacts<{q(facts['scheme'])}>", extra)
            fields.append(f"let commitmentFacts = {record};")
        members = seq(seq(q(part) for part in member) for member in d["members"])
        emit(
            f"ZKC_InstalledDomain<{q(d['identity'])}, {q(d['sort'])}, {members}, "
            f"{seq(q(c) for c in d['capabilities'])}>",
            fields,
        )
    for i, t in enumerate(catalog["logicalTypes"]):
        emit(f"ZKC_LogicalTypeInstance<{q(t['kind'])}, {q(t['domain'])}>", [ordinal(i)])
    for i, t in enumerate(catalog["frameTags"]):
        fields = [ordinal(i)]
        if t["shared"] is not None:
            shared = t["shared"]
            fields.append(
                f"let shared = ZKC_SharedFrame<{q(shared['kind'])}, {q(shared['scheme'])}>;"
            )
        emit(f"ZKC_FrameTag<{t['tag']}, {q(t['layout'])}>", fields)
    for i, c in enumerate(catalog["codecs"]):
        fields = [ordinal(i)]
        if c["frame"] is not None:
            frame = c["frame"]
            extra = [f"let {key} = {value};" for key, value in frame.items() if key != "tag"]
            record = emit("ZKC_CodecFrame<" + str(frame["tag"]) + ">", extra)
            fields.append(f"let frame = {record};")
        emit(
            f"ZKC_Codec<{q(c['identity'])}, {q(c['kind'])}, {q(c['domain'])}>", fields
        )
    for i, a in enumerate(catalog["aggregateFrames"]):
        emit(
            f"ZKC_AggregateFrame<{q(a['constructor'])}, {q(a['domain'])}, {a['tag']}>",
            [ordinal(i)],
        )
    for i, s in enumerate(catalog["randomServices"]):
        emit(f"ZKC_RandomService<{q(s['contract'])}, {q(s['field'])}>", [ordinal(i)])
    for i, limit in enumerate(catalog["limits"]):
        emit(
            f"ZKC_Limit<{q(limit['name'])}, {limit['value']}, {q(limit['unit'])}, "
            f"{q(limit['owner'])}, {q(limit['scope'])}, {q(limit['phase'])}>",
            [ordinal(i)],
        )
    for i, f in enumerate(catalog["finiteDefinitions"]):
        fields = [ordinal(i)]
        if f["collection"] is not None:
            fields.append(f"let collection = {q(f['collection'])};")
        emit(
            f"ZKC_FiniteDefinition<{q(f['identity'])}, {q(f['mode'])}, "
            f"{q(f['operation'])}, {flag(f['filtered'])}>",
            fields,
        )
    for i, c in enumerate(catalog["domainConstructors"]):
        emit(
            f"ZKC_DomainConstructor<{q(c['identity'])}, {q(c['kind'])}, {c['axis']}>",
            [ordinal(i)],
        )


def project_installation(installation, q, seq, flag):
    """The physical installation records, in their own generated file."""
    lines = []

    def emit(base, fields=()):
        name = f"InstallationRecord{len(lines)}"
        body = " ".join(fields)
        lines.append(f"def {name} : {base}" + (" { " + body + " }" if body else ";"))

    def ordinal(i):
        return f"int ordinal = {i};"

    def tree(value):
        if not isinstance(value, list) or len(value) != 3 or value[0] != "apply":
            raise ValueError("installation type patterns are constructor applications")
        arguments = []
        for argument in value[2]:
            if argument[0] == "domain":
                arguments.append(f"ZKC_DomainTypeArgument<{q(argument[1])}, {q(argument[2])}>")
            elif argument[0] == "type":
                arguments.append(f"ZKC_NestedTypeArgument<{tree(argument[1])}>")
            elif argument[0] == "nat":
                arguments.append(f"ZKC_NatTypeArgument<{q(argument[1])}>")
            else:
                raise ValueError("unknown type argument")
        return f"ZKC_TypeTree<{q(value[1])}, {seq(arguments)}>"

    def pattern(value):
        tag = value[0]
        if tag == "any":
            return "ZKC_AnyPattern<>"
        if tag == "domain":
            return f"ZKC_DomainPattern<{q(value[1])}, {q(value[2])}>"
        if tag == "type":
            return f"ZKC_TypePattern<{tree(value[1])}>"
        if tag == "natRange":
            return f"ZKC_NatRangePattern<{q(value[1])}, {q(value[2])}>"
        raise ValueError("unknown argument pattern")

    for i, r in enumerate(installation["representations"]):
        emit(
            f"ZKC_NativeRepresentation<{q(r['identity'])}, {q(r['kind'])}, {q(r['domain'])}, "
            f"{flag(r['default'])}, {q(r['layout'])}, {q(r['frame'])}, {q(r['unit'])}>",
            [ordinal(i)],
        )
    for i, r in enumerate(installation["appliedRepresentations"]):
        fields = [ordinal(i)]
        for column in ("child", "vectorPort"):
            if r[column] is not None:
                reference = r[column]
                fields.append(
                    f"let {column} = ZKC_RepresentationReference<{q(reference['kind'])}, "
                    f"{q(reference['domain'])}, {q(reference['representation'])}>;"
                )
        if r["provider"] is not None:
            fields.append(f"let provider = {q(r['provider'])};")
        emit(
            f"ZKC_AppliedRepresentation<{q(r['constructor'])}, "
            f"{seq(pattern(p) for p in r['arguments'])}, {q(r['identity'])}, "
            f"{flag(r['default'])}, {q(r['frame'])}, {q(r['unit'])}>",
            fields,
        )
    for i, p in enumerate(installation["providers"]):
        emit(
            f"ZKC_ProviderPreference<{q(p['domain'])}, {q(p['default'])}, "
            f"{seq(q(a) for a in p['alternatives'])}>",
            [ordinal(i)],
        )
    for i, u in enumerate(installation["providerUnits"]):
        emit(f"ZKC_ProviderUnit<{q(u['provider'])}, {q(u['unit'])}>", [ordinal(i)])
    for i, f in enumerate(installation["fieldForms"]):
        fields = [ordinal(i)]
        if f["arithmetic"] is not None:
            a = f["arithmetic"]
            fields.append(
                f"let arithmetic = ZKC_ResidueArithmetic<{q(a['form'])}, {q(a['representation'])}>;"
            )
        if f["montgomery"] is not None:
            m = f["montgomery"]
            fields.append(
                f"let montgomery = ZKC_MontgomeryForm<{m['wordBytes']}, {m['radixBits']}>;"
            )
        if f["byteEncoding"] is not None:
            b = f["byteEncoding"]
            fields.append(
                f"let byteEncoding = ZKC_ByteEncoding<{q(b['codec'])}, {q(b['order'])}>;"
            )
        emit(f"ZKC_FieldForm<{q(f['field'])}>", fields)
    for i, p in enumerate(installation["physicalArguments"]):
        emit(f"ZKC_PhysicalArguments<{q(p['operation'])}>", [ordinal(i)])
    return (
        "#ifndef ZKC_NATIVE_INSTALLATION\n#define ZKC_NATIVE_INSTALLATION\n"
        'include "zkc/Contracts/Declarations/NativeInstallationSchema.td"\n'
        + "\n".join(lines)
        + "\n#endif\n"
    )
