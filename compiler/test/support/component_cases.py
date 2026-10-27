"""Actual source controls for repeat effects and deduplicated logical slots."""


def repeat_cases(source):
    """The accepting extension must refuse; a protocol handoff stays explicit."""
    variants = {
        "carried-sample": (source, "component-seam-sampling"),
        "carried-receive": (source.replace("let seed@V=challenges.draw();",
                                           "let seed=send P -> V(sent);"), "component-seam-message"),
        "capture-sample": (source.replace("ordinary@V=seed", "ordinary@V=0")
                           .replace("ordinary=ordinary;", "ordinary=seed;"), "component-seam-sampling"),
        "yield-sample": (source.replace("let seed@V=challenges.draw();", "let seed@V=0;")
                         .replace("ordinary=ordinary;", "ordinary=challenges.draw();"), "component-seam-sampling"),
        "yield-receive": (source.replace("let seed@V=challenges.draw();", "let seed@V=0;")
                          .replace("roles(V) max 2", "roles(P,V) max 2")
                          .replace("n:index@V", "n:index@(P,V)")
                          .replace("ordinary=ordinary;", "ordinary=send P -> V(sent);"), "component-seam-message"),
        "zero-alternative": (source.replace("ordinary=ordinary;", "ordinary=0;"), "component-seam-sampling"),
        "count-sample": (source.replace("ordinary@V=seed", "ordinary@V=0")
                         .replace("0..n roles(V)", "0..count(seed) roles(V)"), "component-seam-sampling"),
        "count-receive": (source.replace("let seed@V=challenges.draw();", "let seed:F@V=0;\n  let received=send P -> V(n);")
                          .replace("n:index@V", "n:index@P")
                          .replace("0..n roles(V)", "0..received roles(V)"), "component-seam-message"),
        "maximum-zero": (source.replace("max 2", "max 0"), "component-seam-sampling"),
        "backedge-sample": (source.replace("let mut ordinary@V=seed;", "let mut ordinary@V=0;\n  let mut previous@V=0;")
                            .replace("ordinary=ordinary;", "ordinary=previous;\n    previous=challenges.draw();"), "component-seam-sampling"),
        "nested-sample": (source.replace("ordinary=ordinary;", "for _ in 0..n roles(V) max 2 { ordinary=ordinary; }"), "component-seam-sampling"),
        "pure": (source.replace("let seed@V=challenges.draw();", "let seed@V=0;"), None),
    }
    for name, (text, refusal) in variants.items():
        for local in ["seed", "ordinary", "previous"]:
            text = text.replace(local + "@V=0;", local + ":F@V=0;")
        yield name + "-handoff", text, None
        accepting = text.split("  let combined@V=", 1)[0] + """  let zero:F@V=0;
  let finished@V=finish(last,ordinary,zero);
  return(accepted=firstOk && finished);
}
entry fn Demo(inputs: Run::Inputs) { return Run::run(inputs); }
"""
        yield name + "-accepting", accepting, refusal


def slot_case(parameters, duplicate_residual=False, duplicate_clause=False):
    """Each relation application fits; only the deduplicated union is bounded."""
    names = [f"p{i}" for i in range(parameters)]
    outputs = [f"q{i}" for i in range(parameters)]
    relation = ",".join("parameter " + n + ":bool" for n in names)
    inputs = ",".join(n + ":bool@V" for n in names)
    result_types = ",".join(n + ":bool@V" for n in outputs)
    subject = ",".join("in." + n for n in names)
    selected = outputs[:-1] + [outputs[-2]] if duplicate_residual else outputs
    residual = ",".join("out." + n for n in selected)
    returned = ",".join(q + "=" + p for p, q in zip(names, outputs))
    clause = f"continuation step=R({subject},in.claim.value) residual R({residual},out.claim.value);"
    if duplicate_clause:
        clause += clause.replace("step=", "also=")
    return f"""module claims;
#[linear] struct Pending {{pub value:bool}}
relation R({relation},statement value:bool){{return value;}}
fn pending(value:bool)->Pending{{return Pending{{value:value}};}}
fn check(claim:Pending)->bool{{let payload=unpack(claim);return payload.0;}}
protocol Child roles(V)({inputs},claim:Pending@V)->({result_types},claim:Pending@V)
spec{{{clause}}}{{return({returned},claim=claim);}}
protocol Run roles(V)(value:bool@V)->(accepted:bool@V)
spec{{target result=R({','.join(['in.value'] * parameters)},in.value) accept out.accepted;}}
{{let initial@V=pending(value);
let ({','.join(outputs)},last)=Child roles(V)({','.join(['value'] * parameters)},initial);
let finished@V=check(last);return(accepted=finished);}}
entry fn Demo(inputs:Run::Inputs){{return Run::run(inputs);}}
"""


def descriptor_cases():
    """One corpus shared by the schema validator and strict Lean reader tests."""
    valid = [
        ["exec", "exec.apply", "binding", ["parameter"]], ["index.constant", "0"],
        ["index.constant", str(2**64 - 1)], ["field.constant", "F", "123"],
        ["field.embed", "E", "F"], ["group.scale", "G", "F"], ["bool.constant", True],
        ["select", ["product", "pair", "Pair", [["bool"], ["sequence", ["field", "F"]]]]],
        ["product.get", 511], ["protocol_apply", "child", ["P", "V"]],
        ["protocol_repeat", 512, 1048576, ["V"], [["V"]]], ["local_call", "helper", "V"],
        ["fold", "domain", "body", ""], ["restrict", ["V"]], ["exchange", "P", "V"],
        ["draw", "V", "F"], ["statement", "relation", ["selector"], 4096, None],
        ["statement", "relation", [], 0, "target"],
    ]
    valid += [[tag] for tag in ["index.equal", "index.less", "index.power_of_two", "bool.and",
                               "bool.or", "bool.xor", "bool.equal", "bool.not_equal", "if", "for", "for_condition"]]
    valid += [[tag, "F"] for tag in ["multilinear.restrict_prefix", "vector.length", "field.add",
                                    "field.subtract", "field.multiply", "field.equal", "bounded_at"]]
    valid += [[tag, "G"] for tag in ["group.identity", "group.add", "group.equal"]]
    valid += [[tag, "name"] for tag in ["product.make", "call", "apply", "guard"]]
    invalid = [[], ["future"], ["bool.constant", 0], ["local_call", "helper", ""],
               ["draw", "V", []], ["exec", "operation", "binding", [0]],
               ["index.constant", "00"], ["index.constant", "-1"], ["index.constant", str(2**64)],
               ["field.constant", "F", "01"], ["field.constant", "F", "1\n"],
               ["product.get", 512], ["product.get", -1], ["product.get", True],
               ["protocol_repeat", 513, 0, [], []], ["protocol_repeat", 0, 1048577, [], []],
               ["protocol_repeat", 0, 0, ["V"] * 17, []], ["protocol_repeat", 0, 0, [], [[0]]],
               ["statement", "relation", [], 4097, None], ["select", []],
               ["select", ["field", []]], ["select", ["product", "pair", "Pair", [0]]],
               ["fold", "domain", "body", None]]
    invalid += [value + [None] for value in valid]
    invalid += [value[:-1] for value in valid]
    return ([[f"valid-{i}", value, True] for i, value in enumerate(valid)] +
            [[f"invalid-{i}", value, False] for i, value in enumerate(invalid)])
