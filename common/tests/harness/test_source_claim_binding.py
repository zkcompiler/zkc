"""Source-claim attachment changes and actual artifact changes have different identities."""

from copy import deepcopy
import json

import pytest

from harness import load


@pytest.fixture
def claims():
    return load("source_claim_binding", "lean/bridges/pipeline/source_claims.py")


def fixture(claims, stage="compiled-ideal"):
    source=b"original protocol"
    interface=json.dumps({"format":"zkc.language-interface/0", "entry":"test::Proof",
                          "protocol":"protocol", "original":claims.digest(source).split(":")[1]})
    original=json.dumps(["zkc.structured-source/0", "original", claims.digest(source), "protocol", []])
    export={"format":"zkc.source-claims/0", "entry":"test::Proof", "registry_resolution":"deferred-to-lean",
            "admission":{"format":"zkc.structured-source/0", "original_sha256":claims.digest(source),
                         "interface_sha256":claims.digest(interface.encode()), "protocol_symbol":"protocol",
                         "capture":"source-capture", "installation":"library-installation"},
            "claims":[{"request":{"subject":{"entry":"test::Proof", "stage":stage},
                                  "target":{"protocol":"protocol","clause":0,"name":"valid"},
                                  "quantity":{"kind":"scalar","expression":{"kind":"natural","value":"0"}},
                                  "property":{"name":"user.equal","version":7}},
                       "attachment":{"label":"old", "node":{"owner":"test","block":0,"claim":0}},
                       "method":None, "site_bindings":[]}]}
    arguments=dict(entry="test::Proof",source=source,interface_text=interface,original_text=original,
                   participant_text="compiled participant", program=b"verifier bytes")
    return export, arguments


def test_source_alias_resolves_to_exact_admitted_protocol(claims):
    export, args = fixture(claims)
    bound = claims.bind_export(export, **args)
    claim = bound["claims"][0]
    assert bound["entry"] == claim["source_entry"] == "test::Proof"
    assert claim["request"]["subject"]["entry"] == "protocol"
    assert claim["entry_association"] == {
        "source_entry": "test::Proof", "protocol": "protocol",
        "interface_digest": export["admission"]["interface_sha256"],
        "attribution": "trusted-frontend-checked-interface"}


@pytest.mark.parametrize("field", ["capture", "installation"])
@pytest.mark.parametrize("value", [None, 42, {}, []])
def test_provenance_requires_schema_strings(claims, field, value):
    export, args = fixture(claims)
    export["admission"][field] = value
    with pytest.raises(claims.Refused, match="must be a string"):
        claims.bind_export(export, **args)


def test_duplicate_original_identity_is_not_a_second_authority(claims):
    export, args = fixture(claims)
    export["admission"]["original_identity"] = claims.digest(args["source"]).split(":")[1]
    with pytest.raises(claims.Refused):
        claims.bind_export(export, **args)


@pytest.mark.parametrize("field,value", [("entry", "test::Other"), ("protocol", "other"),
                                       ("original", "other"), ("format", "other")])
def test_even_rehashed_interface_cannot_cross_entry_association(claims, field, value):
    export, args = fixture(claims)
    interface = json.loads(args["interface_text"])
    interface[field] = value
    args["interface_text"] = json.dumps(interface)
    export["admission"]["interface_sha256"] = claims.digest(args["interface_text"].encode())
    with pytest.raises(claims.Refused):
        claims.bind_export(export, **args)


def test_labels_and_methods_do_not_choose_request(claims):
    export,args=fixture(claims)
    before=claims.bind_export(export,**args)
    changed=deepcopy(export)
    changed["claims"][0]["attachment"]["label"]="renamed"
    changed["claims"][0]["method"]={"name":"another.method","version":42}
    after=claims.bind_export(changed,**args)
    assert before["claims"][0]["request_digest"]==after["claims"][0]["request_digest"]
    assert before["native_export_digest"]!=after["native_export_digest"]
    assert after["claims"][0]["resolution"]=="pending-lean"
    assert "source.correspondence" in after["required_links"]


@pytest.mark.parametrize("field", ["source","interface_text","original_text"])
def test_stale_native_artifacts_are_refused(claims,field):
    export,args=fixture(claims)
    args[field]=b"different" if isinstance(args[field],bytes) else "different"
    with pytest.raises(claims.Refused):
        claims.bind_export(export,**args)


def test_changed_formula_snapshot_detaches_receipt(claims):
    export,args=fixture(claims)
    before=claims.bind_export(export,**args)["claims"][0]["request_digest"]
    raw=json.loads(args["original_text"]);raw[4]=["different retained formula"]
    args["original_text"]=json.dumps(raw)
    after=claims.bind_export(export,**args)["claims"][0]["request_digest"]
    assert before!=after


def test_program_identity_only_binds_byte_stage(claims):
    export,args=fixture(claims,"executable-bytes")
    before=claims.bind_export(export,**args)["claims"][0]["request_digest"]
    args["program"]=b"different program"
    assert before!=claims.bind_export(export,**args)["claims"][0]["request_digest"]
    export["claims"][0]["request"]["subject"]["stage"]="compiled-ideal"
    before=claims.bind_export(export,**args)["claims"][0]["request_digest"]
    args["program"]=b"other irrelevant bytes"
    assert before==claims.bind_export(export,**args)["claims"][0]["request_digest"]


def test_missing_byte_program_is_not_an_ideal_claim(claims):
    export,args=fixture(claims,"executable-bytes");args["program"]=None
    with pytest.raises(claims.Refused,match="lacks its executable"):
        claims.bind_export(export,**args)


@pytest.mark.parametrize("mutation", ["entry","target","stage","duplicate-node"])
def test_cross_subject_and_ambiguous_bindings_are_refused(claims,mutation):
    export,args=fixture(claims)
    request=export["claims"][0]["request"]
    if mutation=="entry":request["subject"]["entry"]="another::Proof"
    elif mutation=="target":request["target"]["protocol"]="another"
    elif mutation=="stage":request["subject"]["stage"]="unknown"
    else:export["claims"].append(deepcopy(export["claims"][0]))
    with pytest.raises(claims.Refused):
        claims.bind_export(export,**args)


@pytest.mark.parametrize("text", ['{"model":1,"model":2}', '{"model":NaN}', '{"model":Infinity}'])
def test_ambiguous_json_is_refused(claims,text):
    with pytest.raises(claims.Refused):claims.decode(text)


def test_cli_interface_terminator_is_not_payload(claims):
    export,args=fixture(claims)
    before=claims.bind_export(export,**args)
    args["interface_text"]+="\n"
    assert before==claims.bind_export(export,**args)
    args["interface_text"]+="\n"
    with pytest.raises(claims.Refused,match="another native interface"):
        claims.bind_export(export,**args)


def site_fixture():
    query = [["draw", "V", "field"], [], [["field", "field"]], [], "leaf"]
    child = ["function", "child", "protocol", "public", [], [], None, [], [],
             ["block", [query], ["return", []]]]
    call = [["protocol_apply", "child", ["P", "V"]], [], [], [], "wrapper"]
    entry = ["function", "entry", "protocol", "public", [], [], None, [], [],
             ["block", [call], ["return", []]]]
    original = ["zkc.structured-source/0", "original", "source", "entry", [], [], [], [entry, child]]
    policy = [None] * 8 + [[["apply_7_wrapper_leaf", "delivery"]][0:1]]
    binding = {"site": "wrapper.challenge", "native_path": ["wrapper", "leaf"],
               "source": {"module": "test", "begin": 0, "end": 1}}
    return original, policy, binding


def test_full_call_path_selects_the_actual_constructed_occurrence(claims):
    original, policy, binding = site_fixture()
    selected = claims.resolve_sites(original, policy, [binding])
    assert selected[0]["native"] == "apply_7_wrapper_leaf"
    assert selected[0]["native_path"] == ["wrapper", "leaf"]
    assert selected[0]["attribution"] == "trusted-frontend-checked-policy"


@pytest.mark.parametrize("mutation", ["leaf-only", "wrong-wrapper", "wrong-policy", "duplicate-occurrence"])
def test_site_attribution_never_falls_back_to_a_first_leaf(claims, mutation):
    original, policy, binding = site_fixture()
    bindings = [binding]
    if mutation == "leaf-only":
        binding["native_path"] = ["leaf"]
    elif mutation == "wrong-wrapper":
        binding["native_path"][0] = "another"
    elif mutation == "wrong-policy":
        policy[8][0][0] = "some_other_leaf"
    else:
        other = deepcopy(binding)
        other["site"] = "alias.challenge"
        bindings.append(other)
    with pytest.raises(claims.Refused):
        claims.resolve_sites(original, policy, bindings)


def test_subject_export_preserves_raw_interface_and_rejects_reserialization(claims):
    bridge = load("explicit_native_subject", "lean/bridges/common/native_entry.py")
    export, arguments = fixture(claims, "interactive")
    interface = {"format": "zkc.language-interface/0", "entry": "test::Proof",
                 "protocol": "protocol", "job": {"kind": "run"},
                 "original": claims.digest(arguments["source"]).split(":")[1]}
    raw = json.dumps(interface, indent=3) + "\n"
    export["admission"]["interface_sha256"] = claims.digest(raw.removesuffix("\n").encode())
    emitted = {"language-emit": arguments["source"].decode(), "language-interface": raw}
    source, exact, parsed = bridge.native_subject(
        lambda command: emitted[command[1]], "compiler", ["--subject=test::Protocol"])
    arguments.update(source=source.encode(), interface_text=exact)
    claims.bind_export(export, **arguments)
    assert exact == raw and parsed == interface
    arguments["interface_text"] = json.dumps(parsed) + "\n"
    with pytest.raises(claims.Refused, match="another native interface"):
        claims.bind_export(export, **arguments)


@pytest.mark.parametrize("flags", [[], ["--entry=demo::Wrapper"],
                                   ["--subject=demo::P", "--entry=demo::Wrapper"],
                                   ["--subject=demo::P", "--subject=demo::Q"]])
def test_protocol_bridge_does_not_discover_a_child_from_a_host(flags):
    bridge = load("explicit_native_subject_refusal", "lean/bridges/common/native_entry.py")
    def unexpected(_command):
        pytest.fail("ambiguous subject reached the compiler")
    with pytest.raises(ValueError, match="one explicit --subject"):
        bridge.native_subject(unexpected, "compiler", flags)
