"""Render data constructors for typed Lean claim resolution, never propositions."""

from pathlib import Path
import re
import sys

sys.path.append(str(Path(__file__).resolve().parents[2]))
from bridges.common.lean_render import Refused, require, text  # noqa: E402


def natural(value):
    require(type(value) is int and value >= 0, "expected a natural number in claim data")
    return str(value)


def fields(value, required, optional=()):
    require(isinstance(value, dict) and set(required) <= set(value) <= set(required) | set(optional),
            "unexpected claim data fields")


def identifier(value):
    fields(value, ("name", "version"), ("parameters",))
    return f"⟨{text(value['name'])}, {natural(value['version'])}⟩"


def arguments(values):
    require(isinstance(values, list), "claim arguments must be a list")
    result=[]
    for value in values:
        fields(value,("label","value"))
        label="none" if value["label"] is None else f"some {text(value['label'])}"
        result.append(f"({label}, {expression(value['value'])})")
    return "[" + ", ".join(result) + "]"


def application(value):
    fields(value,("kind","name","version","arguments"))
    require(value["kind"]=="application" and value["version"] is not None,
            "registry application requires an explicit version")
    return f"⟨⟨{text(value['name'])}, {natural(value['version'])}⟩, {arguments(value['arguments'])}⟩"


def expression(value):
    require(isinstance(value,dict),"claim expression must be an object")
    kind=value.get("kind")
    if kind=="natural":
        fields(value,("kind","value"))
        require(isinstance(value["value"],str) and re.fullmatch(r"0|[1-9][0-9]*",value["value"]),
                "claim natural must be a canonical decimal string")
        return f"(.natural {value['value']})"
    if kind=="reference":
        fields(value,("kind","name"));return f"(.reference {text(value['name'])})"
    if kind=="application":
        fields(value,("kind","name","version","arguments"))
        version="none" if value["version"] is None else f"(some {natural(value['version'])})"
        return f"(.application {text(value['name'])} {version} {arguments(value['arguments'])})"
    if kind=="binary":
        fields(value,("kind","operator","left","right"))
        operators={"+":"add","-":"sub","*":"mul","/":"div","^":"pow"}
        require(value["operator"] in operators,"unknown claim arithmetic operator")
        return f"(.binary .{operators[value['operator']]} {expression(value['left'])} {expression(value['right'])})"
    if kind=="unary":
        fields(value,("kind","operator","operand"))
        require(value["operator"]=="-","unknown unary claim operator")
        return f"(.neg {expression(value['operand'])})"
    if kind=="list":
        fields(value,("kind","items"))
        require(isinstance(value["items"],list),"claim list items must be a list")
        return "(.list ["+", ".join(expression(item) for item in value["items"])+"])"
    raise Refused(f"unsupported claim expression {kind!r}")


def quantity(value):
    require(isinstance(value,dict),"claim quantity must be an object")
    if value.get("kind")=="scalar":
        fields(value,("kind","expression"));return ".scalar " + expression(value["expression"])
    if value.get("kind")=="guarantee":
        fields(value,("kind","form"));return ".guarantee " + application(value["form"])
    if value.get("kind")=="charged":
        fields(value,("kind","charges"));result=[]
        require(isinstance(value["charges"],list),"claim charges must be a list")
        for charge in value["charges"]:
            fields(charge,("site","expression"))
            result.append(f"({text(charge['site'])}, {expression(charge['expression'])})")
        return ".charged ["+", ".join(result)+"]"
    raise Refused("unsupported claim quantity")


def request(value):
    fields(value,("subject","property","model","target","accept","quantity","capabilities"))
    subject=value["subject"];fields(subject,("unit","entry","stage","artifacts"))
    stages={"interactive":"interactive","compiled-ideal":"compiledIdeal","executable-bytes":"executableBytes"}
    require(subject["stage"] in stages,"unknown claim stage")
    artifacts=[]
    for artifact in subject["artifacts"]:
        fields(artifact,("role","digest"));artifacts.append(f"⟨{text(artifact['role'])}, {text(artifact['digest'])}⟩")
    target=value["target"]
    if "language" in target:
        fields(target,("protocol","language"))
        target_text=f".importedLanguage {text(target['protocol'])} {application(target['language'])}"
    else:
        fields(target,("protocol","clause","name"))
        target_text=f".retained {text(target['protocol'])} {natural(target['clause'])} {text(target['name'])}"
    accept=value["accept"];fields(accept,("output","port","role","path"))
    require(type(accept["output"]) is bool,"acceptance direction must be Boolean")
    path=", ".join(natural(part) for part in accept["path"])
    parameter=value["property"].get("parameters")
    parameters="none" if parameter is None else "some "+expression(parameter)
    caps=", ".join(application(capability) for capability in value["capabilities"])
    return f'''{{
  subject := ⟨{text(subject['unit'])}, {text(subject['entry'])}, .{stages[subject['stage']]}, [{', '.join(artifacts)}]⟩
  property := {identifier(value['property'])}
  parameters := {parameters}
  model := {application(value['model'])}
  target := {target_text}
  accept := ⟨{str(accept['output']).lower()}, {natural(accept['port'])}, {natural(accept['role'])}, [{path}]⟩
  quantity := {quantity(value['quantity'])}
  capabilities := [{caps}]
}}'''
