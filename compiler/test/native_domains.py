"""Typed fields, groups, services and suite selection in independent proofs."""

import json
from pathlib import Path
from cases import case, counted
from commands import Commands
from tools import compiler, records

OUT = records()
commands = Commands(OUT)
fixtures = Path(__file__).parent / "fixtures/mathematical"
manifest = []
for family, suite, service, public, roles, draws in [
    (
        "domain-values",
        "merlin3.koala-bear.ext8-binomial3.rejection31le/1",
        "5",
        ["0", "1", "2", "3", "4"],
        ["P", "V"],
        [["draw", "challenge"]],
    ),
    (
        "ristretto-services",
        "merlin3.ristretto255.scalar64le/1",
        "4",
        ["0", "2"],
        ["Alice", "Bob"],
        [["draw_challenge", "challenge"]],
    ),
]:
    for suffix, options in [
        ("", ()),
        ("_plain", ("--no-simplify",)),
        ("_release", ("--release-storage",)),
    ]:
        name = family + suffix
        with case(name):
            source = fixtures / (family + ".mlir")
            p = [
                "zkc.native-proof-policy/5",
                "main",
                *roles,
                "0",
                suite,
                service,
                public,
                draws,
            ]
            policy = OUT / (name + ".policy")
            policy.write_text(json.dumps(p))
            candidate = OUT / (name + ".candidate.mlir")
            candidate.write_text(
                commands.run([compiler, "protocol-construct-proof", source, policy])
            )
            commands.run([compiler, "protocol-check-proof", source, policy, candidate])
            (OUT / (name + ".deployment")).write_text(
                commands.run([compiler, "protocol-proof", source, policy, *options])
            )
            manifest.append(dict(name=name, family=family))
    # A second draw observes the first erased delivery and its exact typed frame.
    with case(family + " two draws"):
        name = family + "_two_draws"
        source = (fixtures / (family + ".mlir")).read_text()
        if family == "ristretto-services":
            ty = '!algebra.field<"ristretto255.scalar">'
            service_ty = '!protocol.service_ref<"random.ristretto255.scalar/1">'
            at = '%cx ='
            new = f'''%c2 = "protocol.query"(%challenge_service) {{method="draw",owner="Bob",site="draw2"}} : ({service_ty})->{ty}
%challenge2 = protocol.exchange %c2 {{site="challenge2",sender="Bob",receiver="Alice"}} : {ty}
%combinedP = algebra.field_add %challenge,%challenge2 : ({ty},{ty})->{ty}
%combinedV = algebra.field_add %c,%c2 : ({ty},{ty})->{ty}
'''
            source = source.replace(at, new + at).replace('field_multiply %challenge, %x', 'field_multiply %combinedP, %x').replace('group_scale %y, %challenge', 'group_scale %y, %combinedV')
        else:
            ty = '!algebra.field<"koala-bear.ext8-binomial3">'
            service_ty = '!protocol.service_ref<"random.koala-bear.ext8-binomial3/1">'
            at = '%sum ='
            new = f'''%c2 = "protocol.query"(%random) {{method="draw",owner="V",site="draw2"}} : ({service_ty})->{ty}
%challenge2 = protocol.exchange %c2 {{site="challenge2",sender="V",receiver="P"}} : {ty}
%combinedP = algebra.field_add %challenge,%challenge2 : ({ty},{ty})->{ty}
%combinedV = algebra.field_add %q,%c2 : ({ty},{ty})->{ty}
'''
            source = source.replace(at, new + at).replace('field_add %extP,%challenge', 'field_add %extP,%combinedP').replace('field_add %extV,%q', 'field_add %extV,%combinedV')
        src = OUT / (name + ".mlir")
        src.write_text(source)
        policy = OUT / (name + ".policy")
        two_draw_policy = [*p[:8], [*draws, ["draw2", "challenge2"]]]
        policy.write_text(json.dumps(two_draw_policy))
        (OUT / (name + ".deployment")).write_text(commands.run([compiler, "protocol-proof", src, policy]))
        manifest.append(dict(name=name, family=family, two_draws=True))
    with case(family + " production retries"):
        name = family + "_retries"
        source = (fixtures / (family + ".mlir")).read_text()
        source = source.replace('"protocol.return"(%ok) : (i1)', '%retry = arith.constant false\n"protocol.return"(%ok,%retry) : (i1,i1)')
        source = source.replace('->i1,roles=', '->(i1,i1),roles=').replace('-> (i1), roles=', '-> (i1,i1), roles=')
        source = source.replace('output_roles=[["V"]]', 'output_roles=[["V"],["P"]]').replace('output_roles=[["Bob"]]', 'output_roles=[["Bob"],["Alice"]]')
        src = OUT / (name + ".mlir")
        src.write_text(source)
        policy = OUT / (name + ".policy")
        policy.write_text(json.dumps(p))
        (OUT / (name + ".deployment")).write_text(commands.run([compiler, "protocol-proof", src, policy]))
        manifest.append(dict(name=name, family=family, retries=True))
    with case(family + " suite field mismatch"):
        source = fixtures / (family + ".mlir")
        p[5] = "merlin3.bls12-381.fr64be/1"
        policy = OUT / (family + "_suite_mismatch.policy")
        policy.write_text(json.dumps(p))
        commands.run(
            [compiler, "protocol-proof", source, policy],
            refuses="native-proof-verifier-service",
        )
(OUT / "manifest.json").write_text(json.dumps(manifest))
counted()
