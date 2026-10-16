#!/usr/bin/env python3
"""Source-bound, sampled comparison with the actual native participant executor.

Requires the combined open structured importer and its evidence.py utility.
The Rust probe executes existing kernels/services; this file never interprets
program arithmetic. Source replay chooses the next request and expected value.
"""

import argparse
import copy
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


import check as structured

ROOT = Path(__file__).resolve().parents[3]
MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513
FORMAT = "zkc.structured-open-request/0"


class Mismatch(Exception):
    def __init__(self, message, reason=None):
        super().__init__(message)
        self.reason = reason
class Unsupported(Exception): pass
class HarnessFailure(Exception): pass


def require(condition, message):
    if not condition: raise Mismatch(message)


def digest(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def now(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def definition(snapshot): return next(row for row in snapshot[7] if row[0] == "function" and row[1] == snapshot[3])


def projection_binding(text, snapshot):
    """Read the compiler's constrained printed projection interface, fail closed.

    This is deliberately not an MLIR parser or projection algorithm. The retained
    text comes from a verified compiler pass; original indices are read verbatim.
    Future spelling/schema changes must update this reader and its controls.
    """
    lines = [line for line in text.splitlines() if '"protocol.projection"()' in line]
    if len(lines) != 1: raise Unsupported("one checked projection record required")
    line = lines[0]
    root = definition(snapshot)
    require(f'source = "{snapshot[3]}"' in line, "projection source root")
    pattern = (r'\{inputs = (\[[0-9, ]*\]), outputs = (\[[0-9, ]*\]), '
               r'participant = @([A-Za-z_0-9]+), role = ("[^"\\]*"), '
               r'service_inputs = (\[[0-9, ]*\])\}')
    rows = re.findall(pattern, line)
    if len(rows) != len(root[6][1]): raise Unsupported("projection interface spelling/roster")
    queries = {site: int(index) for index, site in re.findall(
        r'kind = "protocol.query", service = ([0-9]+) : i64, site = "([^"\\]+)"', line)}
    require(len(queries) == sum(row[0][0] == "draw" for row in root[9][1]), "projection query coverage")
    result = {}
    for inputs, outputs, participant, role, services in rows:
        role = json.loads(role)
        binding = dict(entry=snapshot[3], role=role, participant=participant,
                       inputs=json.loads(inputs), outputs=json.loads(outputs), service_inputs=json.loads(services),
                       input_types=root[4], output_types=root[5],
                       queries={site:index for site,index in queries.items() if index in json.loads(services)})
        require(role not in result, "duplicate projection role")
        for kind, service in (("inputs", False), ("service_inputs", True)):
            expected = [i for i, (ty, scope) in enumerate(zip(root[4], root[6][2], strict=True))
                        if role in scope and (ty[0] == "service") == service]
            require(binding[kind] == expected, "projection source input scopes")
        require(binding["outputs"] == [i for i, scope in enumerate(root[6][3]) if role in scope], "projection output scopes")
        result[role] = binding
    require(set(result) == set(root[6][1]), "projection role roster")
    return result


def bind_snapshot(original, retained, exported):
    require(retained[2] == "sha256:" + digest(original), "actual source bytes differ from retained identity")
    require(retained == exported, "complete structured subject differs from actual source export")


def pending(result):
    return (result[1][:2] == ["stopped", "incomplete"] and len(result[2]) >= 2
            and result[2][-2][0] == "request" and result[2][-1][0] == "stop"
            and result[2][-2][1] == result[3])


def validate_observation(native):
    if not isinstance(native, dict) or native.get("format") != "zkc.participant-observation/0":
        raise HarnessFailure("malformed native observation envelope")
    status = native.get("status")
    if status == "Unsupported": raise Unsupported(native.get("detail"))
    if status == "HarnessFailure": raise HarnessFailure(native.get("detail"))
    if status == "Mismatch": raise Mismatch(native.get("detail"), native.get("reason"))
    if status != "Pass" or not {"outcome","events","consumed"}.issubset(native):
        raise HarnessFailure("malformed native observation envelope")


def compare_arithmetic_mutation(native):
    """Only an unequal native/mapped value establishes this falsification."""
    try:
        validate_observation(native)
    except Mismatch as error:
        try:
            evidence = json.loads(str(error))
            valid = (error.reason == "value-relation" and evidence["actual"] != evidence["mapped"]
                     and all(bytes.fromhex(evidence[key]) for key in ("actual", "mapped")))
        except (ValueError, TypeError, KeyError): valid = False
        if not valid: raise HarnessFailure("arithmetic mutation did not reach unequal native values") from error
        raise
    except Unsupported as error:
        raise HarnessFailure("unsupported mutation is not arithmetic evidence") from error
    raise HarnessFailure("arithmetic mutation was not falsified")


def compare_result(source, native):
    validate_observation(native)
    outcome, events = source[1], source[2]
    if pending(source):
        outcome, events = ["pending", source[1][2]], events[:-1]
    require(native["outcome"] == outcome, "source/native outcome")
    require(native["events"] == events and native["consumed"] == source[3], "source/native ordered prefix")


def provider_expected(providers, replies, leased):
    expected = {p["handle"]: dict(generation=0, draws=0, budget=p["budget"], poisoned=False, leased=leased)
                for p in providers}
    for _, action, response in replies:
        if action[0] != "draw" or response == ["stop", "abort"]: continue
        state = expected[action[4]]
        state["draws"] += 1; state["generation"] += 1
        state["budget"] = max(0, state["budget"] - 1)
        if response[0] == "stop": state["poisoned"] = True
    return expected


def compare_providers(observed, expected):
    require(set(observed) == set(expected), "provider root set")
    for handle, want in expected.items():
        got = observed[handle]
        require(got["completion_known"] and got["state"] is not None, "provider completion knowledge")
        require(got["state"].get("stage") == "rng", "provider lifecycle stage")
        require(all(got[k] == want[k] for k in ("poisoned", "leased")), "provider poison/lease")
        require(all(got["state"][k] == want[k] for k in ("generation", "draws", "budget")), "provider residual state")


class Suite(structured.Suite):
    """Participant checks using the maintained structured Suite lifecycle."""

    def __init__(self, args):
        import evidence
        self.evidence = evidence
        self.detail = dict(format="zkc.participant-comparison/0", cases=[], controls=[],
                           affinity=sorted(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else None,
                           threads={k: os.environ.get(k) for k in ("CARGO_BUILD_JOBS", "RAYON_NUM_THREADS", "OMP_NUM_THREADS")},
                           scope="sampled native endpoint values, prefixes and operational residual state")
        # Shared run publishes running before allocation, Git or tool copies.
        super().__init__(args)

    def setup(self):
        super().setup()
        self.tools["native"] = self.tools["runtime"]
        self.detail["python"] = dict(path=str(Path(sys.executable).resolve()),
                                   sha256=digest(sys.executable), version=sys.version)
        harness = self.directory / "participant-harness"; harness.mkdir()
        self.detail["harness_sources"] = {}
        for filename in (__file__, structured.__file__, self.evidence.__file__):
            source = Path(filename).resolve(); retained = harness / source.name
            retained.write_bytes(source.read_bytes())
            self.detail["harness_sources"][source.name] = dict(source=str(source), path=str(retained), sha256=digest(retained))
        self.detail["external_sources"] = {}
        for name in ("compiler", "lean"):
            source_root = getattr(self.args, name + "_source").resolve()
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=source_root, text=True).strip()
            require(revision == getattr(self.args, name + "_revision"), name + " source revision changed")
            record = dict(root=str(source_root), revision=revision,
                worktree_status=subprocess.check_output(["git", "status", "--porcelain"], cwd=source_root, text=True),
                archive=self.evidence.archive_sources(source_root, self.directory / (name+"-source")),
                binding="operator-selected build source; hashes identify bytes, not executable derivation")
            self.detail["external_sources"][name] = record
            self.archives[name] = record["archive"]
        for name, record in self.tool_records.items():
            require(digest(record["source"]) == record["sha256"], "selected tool changed during copy")
            record["source_revision"] = (self.args.compiler_revision if name in ("compiler", "optimizer", "reference")
                                         else self.args.lean_revision if name == "lean" else self.revision)
        self.save()

    def publish(self, status):
        """Publish the detail with the same final status as the shared report."""
        for check in self.checks:
            check.setdefault("status", "Pass" if check["passed"] else "HarnessFailure")
            check.setdefault("kind", "setup")
        statuses = ("Pass", "Mismatch", "Unsupported", "HarnessFailure")
        self.detail["case_counts"] = {
            state: sum(row["status"] == state for row in self.detail["cases"]) for state in statuses}
        self.detail["control_counts"] = {
            state: sum(row["status"] == state for row in self.detail["controls"]) for state in statuses}
        self.detail["status"] = status
        if self.directory is not None:
            path = self.directory / "participant.json"
            # Remove stale evidence even if writing or hashing the new detail fails.
            self.sources[:] = [r for r in self.sources if r["name"] != "participant-observations"]
            try:
                self.evidence.atomic_json(path, self.detail)
                record = dict(name="participant-observations", path=str(path), sha256=digest(path))
            except BaseException as error:
                interrupted = status == "interrupted" or isinstance(error, KeyboardInterrupt)
                super().publish("interrupted" if interrupted else "failed")
                raise
            self.sources.append(record)
        super().publish(status)

    def save(self):
        self.publish("running")

    def verify_sources(self):
        super().verify_sources()
        for name, record in self.detail.get("external_sources", {}).items():
            check = self.evidence.check_sources(Path(record["root"]), record["archive"])
            check["name"] = name + "-source-stability"
            self.checks.append(check)

    def command(self, label, args, accepted=(0,)):
        started = now()
        try:
            try:
                return super().command(label,args,success=accepted != (1,))
            except AssertionError:
                record=self.commands[-1]
                if record["exit"] in accepted:
                    return Path(record["output"]).with_suffix(".stdout").read_text(encoding="utf-8")
                raise
        finally:
            if self.commands:
                self.commands[-1].update(startedUtc=started,finishedUtc=now())
            self.save()

    def subject(self, name, source=None, root="main"):
        folder = self.directory / name; folder.mkdir()
        if source is None:
            flags = ["--source-format=zkc", "--entry=example::Interactive",
                     f"--module=example={ROOT}/examples/projects/schnorr/main.zkc",
                     f"--module=schnorr={ROOT}/libraries/schnorr/lib.zkc"]
            source = self.command(name+":frontend", [self.tools["compiler"], "language-emit", *flags])
            interface = json.loads(self.command(name+":interface", [self.tools["compiler"], "language-interface", *flags]))
            self.evidence.atomic_json(folder / "interface.json", interface); root = interface["protocol"]
            for part in ("examples/projects/schnorr/main.zkc", "libraries/schnorr/lib.zkc"):
                (folder / ("example.zkc" if part.startswith("examples") else "library.zkc")).write_bytes((ROOT / part).read_bytes())
        original = folder / "source.mlir"; original.write_text(source, encoding="utf-8")
        exported = folder / "source.json"
        text = self.command(name+":structured", [self.tools["compiler"], "protocol-structured", original, "--symbol="+root])
        exported.write_text(text, encoding="utf-8"); snapshot = json.loads(text)
        require(snapshot[:4] == ["zkc.structured-source/0", "original", "sha256:"+digest(original), root], "source snapshot identity")
        self.command(name+":lean-check", [self.tools["lean"], "check", exported])
        reexported=json.loads(self.command(name+":reexport", [self.tools["compiler"], "protocol-structured", original, "--symbol="+root]))
        bind_snapshot(original,snapshot,reexported)
        projection = self.command(name+":project", [self.tools["optimizer"], original, "--verify-each", "--zkc-project-protocol"])
        (folder / "projected.mlir").write_text(projection, encoding="utf-8")
        bindings = projection_binding(projection, snapshot)
        self.evidence.atomic_json(folder / "bindings.json", bindings)
        options = ["--entry="+root, "--no-simplify"]
        bundle_text = self.command(name+":bundle", [self.tools["compiler"], "protocol-bundle", original, *options])
        bundle_path=folder / "bundle.json"; bundle_path.write_text(bundle_text, encoding="utf-8")
        bundle=json.loads(bundle_text); candidate=folder / "candidate.json"; candidate.write_text(bundle["candidate"], encoding="utf-8")
        # Rebuild the exact candidate from the retained checked projection. This
        # connects the side interface to the bundle rather than trusting names.
        physical = self.command(name+":physical", [self.tools["optimizer"], folder / "projected.mlir", "--verify-each",
                                "--zkc-eliminate-polynomials", "--zkc-lower-math", "--zkc-select-physical"])
        (folder / "physical.mlir").write_text(physical, encoding="utf-8")
        separate = self.command(name+":export", [self.tools["compiler"], "protocol-export", folder / "physical.mlir"])
        require(separate.rstrip("\n") == bundle["candidate"].rstrip("\n"), "projection pipeline candidate differs from bundle")
        self.sources.append(dict(name=name, root=root, options=options,
            files={p.name: dict(path=str(p), sha256=digest(p)) for p in folder.iterdir() if p.is_file()})); self.save()
        return dict(folder=folder, original=original, exported=exported, snapshot=snapshot, candidate=candidate, bindings=bindings)

    def observe(self, subject, request, label, lean=False):
        path = subject["folder"] / (label+".request.json"); self.evidence.atomic_json(path, request)
        cmd = ([self.tools["lean"], "open", subject["exported"], path] if lean else
               [self.tools["reference"], "open", subject["original"], subject["snapshot"][3], path])
        result = json.loads(self.command(label+(":lean" if lean else ":source"), cmd,accepted=(0,1)))
        if isinstance(result, dict) and result.get("status") == "refused":
            if result.get("code") in {"structured-open-capacity","structured-open-work-limit","structured-open-record-limit","structured-reference-capacity"}:
                raise Unsupported(str(result))
            raise HarnessFailure("source replay refused request: "+str(result))
        if not (isinstance(result, list) and len(result) == 4 and result[0] == "zkc.structured-open-result/0"):
            raise HarnessFailure("malformed source result envelope")
        return result

    def script(self, subject, label, role, inputs, receives, providers, stop=None, fault=None):
        replies=[]; received=iter(receives); cursors={p["handle"]: 0 for p in providers}; plans={p["handle"]: p for p in providers}
        prefixes=[]
        for position in range(128):
            request=[FORMAT,role,inputs,replies,1000000]
            result=self.observe(subject,request,f"{label}-generate-{position}")
            prefixes.append(result)
            if not pending(result): return request,result,prefixes
            action=result[2][-2][2]
            if stop == (position, "pending"): return copy.deepcopy(request),result,prefixes
            if stop == (position, "abort"): response=["stop","abort"]
            elif fault and fault["action"] == position and fault["mode"].startswith("complete-"): response=["stop","refused"]
            elif action[0] == "send": response=["unit"]
            elif action[0] == "receive": response=["value", next(received)]
            elif action[0] == "draw":
                handle=action[4]; p=plans[handle]; n=cursors[handle]; cursors[handle]+=1
                if n >= p["budget"] or n >= len(p["tape"]): response=["stop","exhausted"]
                elif fault and fault["action"] == position and fault["mode"] == "malformed-reply": response=["stop","refused"]
                else: response=["value",p["tape"][n]]
            else: raise Unsupported("source action "+str(action))
            replies.append(["reply",action,response])
        raise Unsupported("source action count")

    def case(self, subject, label, role, inputs, receives, providers, stop=None, fault=None, expected_output=None):
        record=dict(name=label,status="Running",passed=False,kind="endpoint"); self.detail["cases"].append(record); self.checks.append(record); self.save()
        try:
            require(subject["snapshot"][2] == "sha256:"+digest(subject["original"]),"source changed after binding")
            request,result,prefixes=self.script(subject,label,role,inputs,receives,providers,stop,fault)
            if expected_output is not None: require(result[1] == ["returned",expected_output],"decisive source output")
            formal=self.observe(subject,request,label+"-full",lean=True)
            require(formal == result,"Lean/native SSA full replay")
            for i,prefix in enumerate(prefixes[:-1]):
                sliced=copy.deepcopy(request); sliced[3]=sliced[3][:i]
                require(self.observe(subject,sliced,f"{label}-prefix-{i}",lean=True) == prefix,"Lean/source prefix")
            native_request=dict(format="zkc.participant-probe/0",binding=subject["bindings"][role],
                request=request,expected=result,providers=providers,fault=fault,session=f"participant-{self.identity}-{label}")
            path=subject["folder"] / (label+".native.json"); self.evidence.atomic_json(path,native_request)
            native=json.loads(self.command(label+":native",[self.tools["native"],subject["candidate"],path],accepted=(0,1)))
            self.evidence.atomic_json(subject["folder"] / (label+".observation.json"),native)
            compare_result(result,native)
            require(native["faults_applied"] == int(fault is not None),"requested fault application count")
            for checkpoint in native["checkpoints"]:
                i=checkpoint["position"]
                require(i >= native["consumed"] or checkpoint.get("stale_cut_refused"),"consumed cut stale check")
                require(prefixes[i][2][-2][2] == checkpoint["request"],"native pending action/source incomplete")
                compare_providers(checkpoint["state"]["providers"],provider_expected(providers,request[3][:i],True))
            compare_providers(native["after_cleanup"]["providers"],provider_expected(providers,request[3],False))
            for state in (native["initial"],native["before_cleanup"],native["after_cleanup"]):
                require(all(p["owner"] == role for p in state["providers"].values()),"provider owner")
                require({h:p["issued"] for h,p in state["providers"].items()} ==
                        {h:p["issued"] for h,p in native["initial"]["providers"].items()},"provider identity changed")
            poison=any(p["poisoned"] for p in native["after_cleanup"]["providers"].values())
            require(native["reacquired"] != poison,"poisoned provider reuse")
            bound=native["bindings"]
            require(sorted(p["source_index"] for p in bound) == subject["bindings"][role]["service_inputs"],"original service index coverage")
            expected_handles=[inputs[p["source_index"]] for p in bound]
            require([p["handle"] for p in bound] == expected_handles,"original service handle binding")
            require(all(p["issued"] == native["initial"]["providers"][h]["issued"] for p,h in zip(bound,expected_handles,strict=True)),"issued root binding")
            expected_aliases=[[a == b for b in expected_handles] for a in expected_handles]
            require(native["aliases"] == expected_aliases,"provider alias partition")
            record.update(status="Pass",actions=native["consumed"],outcome=native["outcome"],
                          request=str(path),observation=str(subject["folder"] / (label+".observation.json")))
        except (Mismatch,Unsupported,HarnessFailure) as error: record.update(status=type(error).__name__,detail=str(error))
        except Exception as error: record.update(status="HarnessFailure",detail=repr(error))
        record["passed"]=record["status"] == "Pass"
        self.save()

    def control(self, name, callback, status="Mismatch"):
        row=dict(name=name,status="Running",expected=status,passed=False,kind="control"); self.detail["controls"].append(row); self.checks.append(row)
        try: callback()
        except Exception as error:
            row.update(status="Pass" if type(error).__name__ == status else "HarnessFailure",observed=type(error).__name__,detail=str(error))
        else: row.update(status="Mismatch",detail="negative control was accepted")
        row["passed"]=row["status"] == "Pass"
        self.save()

    def exercise(self):
        schnorr=self.subject("schnorr")
        p,v=definition(schnorr["snapshot"])[6][1]
        def provider(handle,tape,budget=None): return dict(handle=handle,tape=list(map(str,tape)),budget=len(tape) if budget is None else budget)
        inputs={p:["1","13","13","17",None],v:["1","13",None,None,"29"]}
        plans={p:[provider("17",[17])],v:[provider("29",[19])]}
        receives={p:["19"],v:["17","264"]}
        for role in (p,v):
            self.case(schnorr,"honest-"+role,role,inputs[role],receives[role],plans[role],expected_output=[None] if role==p else [True])
            for i in range(4):
                for mode in ("pending","abort"):
                    self.case(schnorr,f"{role}-{mode}-{i}",role,inputs[role],receives[role],plans[role],stop=(i,mode))
        for label,role,values,received,plan,want in [
            ("prover-base",p,["2","13","13","17",None],["19"],plans[p],[None]),
            ("prover-point",p,["1","99","13","17",None],["19"],plans[p],[None]),
            ("verifier-base",v,["2","13",None,None,"29"],["17","264"],plans[v],[False]),
            ("verifier-point",v,["1","14",None,None,"29"],["17","264"],plans[v],[False]),
            ("received-challenge",p,inputs[p],["20"],plans[p],[None]),
            ("received-commitment",v,inputs[v],["18","264"],plans[v],[False]),
            ("received-response",v,inputs[v],["17","265"],plans[v],[False]),
            ("independent-challenge",v,inputs[v],["17","264"],[provider("29",[20])],[False]),
            ("identity-prover",p,["0","0","0","17",None],["0"],[provider("17",[0])],[None]),
            ("identity-verifier",v,["0","0",None,None,"29"],["0","0"],[provider("29",[0])],[True]),
            ("wrap-prover",p,[str(MODULUS-1),"1",str(MODULUS-1),"17",None],["2"],[provider("17",[MODULUS-1])],[None]),
            ("wrap-verifier",v,[str(MODULUS-1),"1",None,None,"29"],["1",str(MODULUS-3)],[provider("29",[2])],[True]),
        ]: self.case(schnorr,label,role,values,received,plan,expected_output=want)
        for role,positions in ((p,[2]),(v,[0,3])):
            for i in positions:
                modes=["length","noncanonical"]+(["noncanonical-identity"] if role==v and i==0 else ["modulus"])
                for mode in modes:
                    for complete in (False,True):
                        fault=dict(action=i,mode=("complete-" if complete else "")+mode)
                        self.case(schnorr,f"wire-{role}-{i}-{fault['mode']}",role,inputs[role],receives[role],plans[role],fault=fault)
        services=self.subject("services",(ROOT / "compiler/test/fixtures/structured-source/open-services.mlir").read_text(encoding="utf-8"))
        for label,values,plan,fault,want in [
            ("alias",["17","17",True],[provider("17",[3,8,11])],None,["3","8",None]),
            ("distinct",["17","29",True],[provider("17",[3,11]),provider("29",[8,19])],None,["3","8",None]),
            ("guard",["17","17",False],[provider("17",[3,8])],None,None),
            ("budget-exhaustion",["17","17",True],[provider("17",[3,8],1)],None,None),
            ("tape-exhaustion",["17","17",True],[provider("17",[3],2)],None,None),
            ("malformed-reply",["17","17",True],[provider("17",[3,8])],dict(action=0,mode="malformed-reply"),None),
        ]: self.case(services,label,"P",values,[],plan,fault=fault,expected_output=want)
        self.negative_controls(schnorr,services)

    def negative_controls(self, subject, services):
        changed=subject["original"].read_text(encoding="utf-8").replace('"algebra.field_multiply"','"algebra.field_add"',1)
        require(changed != subject["original"].read_text(encoding="utf-8"),"source mutation target")
        path=subject["folder"] / "changed-source.mlir"; path.write_text(changed, encoding="utf-8")
        fresh=json.loads(self.command("mutated-source:export",[self.tools["compiler"],"protocol-structured",path,"--symbol="+subject["snapshot"][3]]))
        fresh[2]=subject["snapshot"][2]
        self.evidence.atomic_json(subject["folder"] / "copied-provenance.json",fresh)
        self.command("mutated-source:lean-admit",[self.tools["lean"],"check",subject["folder"] / "copied-provenance.json"])
        self.control("actual-source-mutation-copied-provenance",lambda:bind_snapshot(path,subject["snapshot"],fresh))
        self.control("snapshot-body-copied-provenance",lambda:bind_snapshot(subject["original"],fresh,subject["snapshot"]))
        row=next(r for r in self.detail["cases"] if r["name"].startswith("honest-") and r["status"]=="Pass")
        native=json.loads(Path(row["observation"]).read_text(encoding="utf-8")); request=json.loads(Path(row["request"]).read_text(encoding="utf-8")); source=request["expected"]
        changed_bundle=json.loads(self.command("mutated-source:bundle",[self.tools["compiler"],"protocol-bundle",path,"--entry="+subject["snapshot"][3],"--no-simplify"]))
        changed_candidate=subject["folder"] / "changed-candidate.json"
        changed_candidate.write_text(changed_bundle["candidate"],encoding="utf-8")
        changed_native=json.loads(self.command("mutated-source:native",[self.tools["native"],changed_candidate,row["request"]],accepted=(0,1)))
        self.control("changed-source-native-values",lambda:compare_arithmetic_mutation(changed_native))
        for label,change,status in [
            ("malformed-query-root",lambda n:n["binding"]["queries"].__setitem__(n["request"][3][0][1][1],999),"HarnessFailure"),
            ("unsupported-type",lambda n:n["binding"]["input_types"].__setitem__(0,["group","bn254.g1"]),"Unsupported"),
            ("unknown-driver-field",lambda n:n.__setitem__("unknown",True),"HarnessFailure"),
            ("binding-input-range",lambda n:n["binding"].__setitem__("inputs",[999]),"HarnessFailure"),
            ("binding-output-range",lambda n:n["binding"].__setitem__("outputs",[999]),"HarnessFailure"),
            ("binding-duplicate-input",lambda n:n["binding"].__setitem__("inputs",[0,0]),"HarnessFailure"),
            ("binding-type-shape",lambda n:n["binding"]["input_types"].__setitem__(0,[]),"HarnessFailure"),
            ("expected-output-arity",lambda n:n["expected"][1].__setitem__(1,[]),"HarnessFailure"),
            ("truncated-script",lambda n:n["request"][3].__setitem__(0,["reply"]),"HarnessFailure"),
            ("draw-five-reply",lambda n:n["request"][3][0][1].pop(),"HarnessFailure"),
            ("draw-seven-reply",lambda n:n["request"][3][0][1].append("extra"),"HarnessFailure"),
            ("draw-five-expected",lambda n:n["expected"][2][0][2].pop(),"HarnessFailure"),
            ("draw-seven-expected",lambda n:n["expected"][2][0][2].append("extra"),"HarnessFailure"),
            ("fault-wire-on-send",lambda n:n.__setitem__("fault",dict(action=1,mode="length")),"HarnessFailure"),
            ("fault-unknown-draw",lambda n:n.__setitem__("fault",dict(action=0,mode="unknown")),"HarnessFailure"),
            ("fault-draw-on-receive",lambda n:n.__setitem__("fault",dict(action=2,mode="malformed-reply")),"HarnessFailure"),
        ]:
            bad=copy.deepcopy(request);change(bad);target=subject["folder"] / (label+".json");self.evidence.atomic_json(target,bad)
            observed=json.loads(self.command(label,[self.tools["native"],subject["candidate"],target],accepted=(1,)))
            require(observed["status"] == status,"driver classification: "+label)
            record=dict(name=label,status="Pass",observed=status,passed=True,kind="control")
            self.detail["controls"].append(record);self.checks.append(record)
        verifier=next(r for r in self.detail["cases"] if r["name"].startswith("honest-") and r["outcome"]==["returned",[True]])
        bad=json.loads(Path(verifier["request"]).read_text(encoding="utf-8"));bad["fault"]=dict(action=0,mode="modulus")
        target=subject["folder"] / "fault-modulus-on-group.json";self.evidence.atomic_json(target,bad)
        observed=json.loads(self.command("fault-modulus-on-group",[self.tools["native"],subject["candidate"],target],accepted=(1,)))
        require(observed["status"]=="HarnessFailure","scalar fault on group must fail configuration")
        record=dict(name="fault-modulus-on-group",status="Pass",observed="HarnessFailure",passed=True,kind="control")
        self.detail["controls"].append(record);self.checks.append(record)
        service_case=next(r for r in self.detail["cases"] if r["name"]=="distinct" and r["status"]=="Pass")
        wrong_root=json.loads(Path(service_case["request"]).read_text(encoding="utf-8"))
        wrong_root["binding"]["queries"]["first"]=1
        target=services["folder"] / "wrong-projection-root.json";self.evidence.atomic_json(target,wrong_root)
        observed=json.loads(self.command("wrong-projection-root",[self.tools["native"],services["candidate"],target],accepted=(1,)))
        require(observed["status"]=="Mismatch" and observed["detail"]=="query original root binding","valid but wrong original root must mismatch")
        record=dict(name="wrong-projection-root",status="Pass",observed="Mismatch",passed=True,kind="control")
        self.detail["controls"].append(record);self.checks.append(record)
        unreachable=json.loads(Path(service_case["request"]).read_text(encoding="utf-8"))
        unreachable["request"][3][0][2]=["stop","abort"]
        unreachable["request"][3][1][2]=["stop","refused"]
        unreachable["fault"]=dict(action=1,mode="malformed-reply")
        target=services["folder"] / "unreached-fault.json";self.evidence.atomic_json(target,unreachable)
        observed=json.loads(self.command("unreached-fault",[self.tools["native"],services["candidate"],target],accepted=(1,)))
        require(observed["status"]=="HarnessFailure" and "not applied exactly once" in observed["detail"],"unreached injection must fail coverage")
        record=dict(name="unreached-fault",status="Pass",observed="HarnessFailure",passed=True,kind="control")
        self.detail["controls"].append(record);self.checks.append(record)
        for label,mutate in [
            ("event-value",lambda n:n["events"][2][2].__setitem__(5,"999")),
            ("event-site",lambda n:n["events"][0][2].__setitem__(1,"wrong")),
            ("event-root",lambda n:n["events"][0][2].__setitem__(4,"999")),
        ]:
            bad=copy.deepcopy(native); mutate(bad)
            self.control(label,lambda n=bad:compare_result(source,n))
        bad=copy.deepcopy(native["after_cleanup"]["providers"]); handle=next(iter(bad)); bad[handle]["state"]["draws"]+=1
        self.control("residual-state",lambda:compare_providers(bad,provider_expected(request["providers"],request["request"][3],False)))
        self.control("unsupported-not-pass",lambda:compare_result(source,{"format":"zkc.participant-observation/0","status":"Unsupported"}),"Unsupported")


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name,default in (("compiler","build/compiler/zkc-compile"),("optimizer","build/compiler/zkc-opt"),
                         ("reference","build/compiler/test/zkc-structured_reference-test"),("lean","lean/.lake/build/bin/structured-source"),
                         ("native","target/release/participant_correspondence")):
        parser.add_argument("--"+name,type=Path,default=ROOT/default)
    parser.add_argument("--compiler-source",type=Path,default=ROOT)
    parser.add_argument("--lean-source",type=Path,default=ROOT)
    parser.add_argument("--compiler-revision",required=True)
    parser.add_argument("--lean-revision",required=True)
    parser.add_argument("--report",type=Path,required=True)
    args=parser.parse_args()
    args.seed,args.cases,args.runtime=0,1,args.native
    try:
        return Suite(args).run(lambda suite:suite.exercise())
    except Exception as error:
        print(f"HarnessFailure: {error}",file=sys.stderr); return 1



if __name__ == "__main__": sys.exit(main())
