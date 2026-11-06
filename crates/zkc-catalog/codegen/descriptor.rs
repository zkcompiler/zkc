//! Independent exact admission and projection of installed structural schemes.
use super::{
    Result, array, boolean, choice, kind, list, number, object, quoted, record, string, variant,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};

pub(super) const FORMS: &[&str] = &[
    "Append",
    "Concat",
    "Replace",
    "ForgetExtent",
    "CheckExtent",
    "Fold",
];
pub(super) const HEADS: &[&str] = &[
    "OracleHandle",
    "OracleHandleSequence",
    "FiniteDescriptor",
    "DescriptorProduct",
    "DescriptorSequence",
];
fn require(ok: bool, message: &str) -> Result<()> {
    if ok { Ok(()) } else { Err(message.into()) }
}

fn pattern(v: &Value) -> Result<()> {
    let mut pending = vec![(v, 0)];
    let mut nodes = 0;
    while let Some((p, depth)) = pending.pop() {
        nodes += 1;
        require(nodes <= 1024 && depth <= 32, "scheme pattern limit")?;
        match string(&p["kind"])? {
            "contract" => {
                object(p, &["kind", "variable"], &[])?;
                number(&p["variable"])?;
            }
            "product" => {
                object(p, &["kind", "elements"], &[])?;
                let children = list(&p["elements"])?;
                require(
                    children.len() <= 1024 - nodes - pending.len(),
                    "scheme pattern limit",
                )?;
                pending.extend(children.iter().map(|c| (c, depth + 1)));
            }
            "sequence" => {
                object(p, &["kind", "element", "extent"], &[])?;
                let e = &p["extent"];
                match string(&e["kind"])? {
                    "unsized" => {
                        object(e, &["kind"], &[])?;
                    }
                    "extent" => {
                        object(e, &["kind", "variable"], &[])?;
                        number(&e["variable"])?;
                    }
                    "static" => {
                        object(e, &["kind", "index"], &[])?;
                        number(&e["index"])?;
                    }
                    _ => return Err("unknown scheme extent".into()),
                }
                require(nodes + pending.len() < 1024, "scheme pattern limit")?;
                pending.push((&p["element"], depth + 1));
            }
            _ => return Err("unknown scheme pattern".into()),
        }
    }
    Ok(())
}
fn port(v: &Value, named: bool) -> Result<()> {
    if named {
        string(&v["name"])?;
    }
    match string(&v["kind"])? {
        "descriptor" => {
            object(
                v,
                if named {
                    &["name", "kind", "contract"]
                } else {
                    &["kind", "contract"]
                },
                &[],
            )?;
            pattern(&v["contract"])
        }
        "selectedView" => {
            object(
                v,
                if named {
                    &["name", "kind", "context", "state"]
                } else {
                    &["kind", "context", "state"]
                },
                &[],
            )?;
            pattern(&v["context"])?;
            pattern(&v["state"])
        }
        _ => Err("unknown scheme port".into()),
    }
}
fn canonical(form: &str) -> Value {
    let c = json!({"kind":"contract","variable":0});
    let a = json!({"kind":"contract","variable":1});
    let seq = |extent: Value| json!({"kind":"sequence","element":c,"extent":extent});
    let d = |p: Value| json!({"kind":"descriptor","contract":p});
    let s = seq(json!({"kind":"unsized"}));
    let l = seq(json!({"kind":"extent","variable":1}));
    let (variables, statics, inputs, output) = match form {
        "Append" => (vec!["Contract"], 0, vec![d(s.clone()), d(c)], s),
        "Concat" => (vec!["Contract"], 0, vec![d(s.clone()), d(s.clone())], s),
        "Replace" => (
            vec!["Contract", "OptionalExtent"],
            1,
            vec![d(l.clone()), d(c)],
            l,
        ),
        "ForgetExtent" => (vec!["Contract", "OptionalExtent"], 0, vec![d(l)], s),
        "CheckExtent" => (
            vec!["Contract"],
            1,
            vec![d(s)],
            seq(json!({"kind":"static","index":0})),
        ),
        _ => (
            vec!["Contract", "Contract"],
            1,
            vec![
                json!({"kind":"selectedView","context":c,"state":a}),
                d(c),
                d(a.clone()),
            ],
            a,
        ),
    };
    json!({"variables":variables, "statics":if statics == 0 {vec![]} else {vec![json!({"kind":"Nat","sort":""})]}, "inputs":inputs,"output":output})
}
pub(super) fn validate(v: &Value) -> Result<()> {
    let mut schemes = BTreeMap::new();
    let mut forms = BTreeSet::new();
    for s in list(&v["frontendSchemes"])? {
        object(
            s,
            &["name", "form", "variables", "statics", "inputs", "output"],
            &[],
        )?;
        let name = string(&s["name"])?;
        let form = choice(&s["form"], FORMS)?;
        require(
            super::validation::identifier(name)
                && schemes.insert(name, s).is_none()
                && forms.insert(form),
            "duplicate descriptor scheme",
        )?;
        require(
            list(&s["variables"])?.len() <= 1024
                && list(&s["statics"])?.len() <= 1024
                && list(&s["inputs"])?.len() <= 1024,
            "scheme signature limit",
        )?;
        for p in list(&s["inputs"])? {
            port(p, false)?;
        }
        pattern(&s["output"])?;
        let expected = canonical(form);
        require(
            ["variables", "statics", "inputs", "output"]
                .iter()
                .all(|key| s[key] == expected[key]),
            "descriptor scheme form mismatch",
        )?;
    }
    require(forms.len() == FORMS.len(), "missing descriptor scheme form")?;
    let mut heads = BTreeMap::new();
    for h in list(&v["frontendConstructors"])? {
        heads.insert(string(&h["name"])?, string(&h["form"])?);
    }
    let mut used = BTreeSet::new();
    let mut used_heads = BTreeSet::new();
    for d in list(&v["frontendDeclarations"])? {
        object(
            d,
            &[
                "identity",
                "owner",
                "name",
                "kind",
                "association",
                "prelude",
            ],
            &["statics", "inputs", "output"],
        )?;
        let tag = string(&d["kind"])?;
        if tag != "ContractConstructor" {
            object(
                d,
                &[
                    "identity",
                    "owner",
                    "name",
                    "kind",
                    "association",
                    "prelude",
                    "statics",
                    "inputs",
                    "output",
                ],
                &[],
            )?;
        }
        object(&d["association"], &["kind", "target"], &[])?;
        let target = string(&d["association"]["target"])?;
        if tag == "ContractConstructor" {
            object(
                d,
                &[
                    "identity",
                    "owner",
                    "name",
                    "kind",
                    "association",
                    "prelude",
                ],
                &[],
            )?;
            require(
                d["association"]["kind"] == "constructor"
                    && !boolean(&d["prelude"])?
                    && matches!(
                        heads.get(target),
                        Some(&"DescriptorProduct" | &"DescriptorSequence")
                    )
                    && used_heads.insert(target),
                "invalid contract constructor association",
            )?;
        } else if tag == "View" {
            object(
                d,
                &[
                    "identity",
                    "owner",
                    "name",
                    "kind",
                    "statics",
                    "inputs",
                    "output",
                    "association",
                    "prelude",
                ],
                &[],
            )?;
            require(
                d["association"]["kind"] == "scheme"
                    && !boolean(&d["prelude"])?
                    && used.insert(target),
                "invalid View scheme association",
            )?;
            let s = schemes
                .get(target)
                .ok_or("invalid View scheme association")?;
            let statics = list(&d["statics"])?;
            require(
                statics.len() == list(&s["statics"])?.len()
                    && list(&d["inputs"])?.len() == list(&s["inputs"])?.len(),
                "View scheme declaration mismatch",
            )?;
            for st in statics {
                object(st, &["name", "parameter"], &[])?;
                kind(&st["parameter"])?;
            }
            let mut inputs = Vec::new();
            for p in list(&d["inputs"])? {
                port(p, true)?;
                let mut p = p.clone();
                p.as_object_mut().unwrap().remove("name");
                inputs.push(p);
            }
            pattern(&d["output"])?;
            require(
                statics
                    .iter()
                    .map(|st| &st["parameter"])
                    .eq(list(&s["statics"])?.iter())
                    && inputs == list(&s["inputs"])?
                    && d["output"] == s["output"],
                "View scheme declaration mismatch",
            )?;
        }
    }
    require(
        used.len() == schemes.len(),
        "unreferenced descriptor scheme",
    )?;
    require(
        used_heads.len()
            == heads
                .values()
                .filter(|&&f| f == "DescriptorProduct" || f == "DescriptorSequence")
                .count(),
        "unreferenced contract constructor",
    )
}
fn pattern_code(v: &Value) -> Result<String> {
    Ok(match string(&v["kind"])? {
        "contract" => format!("ContractPattern::Variable({})", number(&v["variable"])?),
        "product" => format!(
            "ContractPattern::Product({})",
            array(&v["elements"], pattern_code)?
        ),
        _ => {
            let e = &v["extent"];
            let extent = match string(&e["kind"])? {
                "unsized" => "ExtentPattern::Unsized".into(),
                "extent" => format!("ExtentPattern::Variable({})", number(&e["variable"])?),
                _ => format!("ExtentPattern::Static({})", number(&e["index"])?),
            };
            format!(
                "ContractPattern::Sequence(&{}, {extent})",
                pattern_code(&v["element"])?
            )
        }
    })
}
fn port_code(v: &Value) -> Result<String> {
    Ok(if string(&v["kind"])? == "descriptor" {
        format!("SchemePort::Descriptor({})", pattern_code(&v["contract"])?)
    } else {
        format!(
            "SchemePort::SelectedView{{context:{},state:{}}}",
            pattern_code(&v["context"])?,
            pattern_code(&v["state"])?
        )
    })
}
pub(super) fn schemes(v: &Value) -> Result<String> {
    array(v, |s| {
        Ok(record(
            "FrontendScheme",
            &[
                ("name", quoted(&s["name"])?),
                ("form", variant(&s["form"], "DescriptorForm", FORMS)?),
                (
                    "variables",
                    array(&s["variables"], |v| {
                        variant(v, "PatternSort", &["Contract", "OptionalExtent"])
                    })?,
                ),
                ("statics", array(&s["statics"], kind)?),
                ("inputs", array(&s["inputs"], port_code)?),
                ("output", pattern_code(&s["output"])?),
            ],
        ))
    })
}
pub(super) fn signature(d: &Value, v: &Value) -> Result<Option<String>> {
    Ok(match string(&d["kind"])? {
        "ContractConstructor" => Some(format!(
            "FrontendSignature::ContractHead{{constructor:{}}}",
            quoted(&d["association"]["target"])?
        )),
        "View" => Some(format!(
            "FrontendSignature::ViewScheme{{statics:{},inputs:{},output:{},scheme:SchemeId({})}}",
            statics(&d["statics"])?,
            array(&d["inputs"], |p| Ok(record(
                "NamedSchemePort",
                &[("name", quoted(&p["name"])?), ("port", port_code(p)?)]
            )))?,
            pattern_code(&d["output"])?,
            list(&v["frontendSchemes"])?
                .iter()
                .position(|s| s["name"] == d["association"]["target"])
                .ok_or("invalid View scheme association")?
        )),
        _ => None,
    })
}
pub(super) fn statics(v: &Value) -> Result<String> {
    array(v, |s| {
        object(s, &["name", "parameter"], &[])?;
        Ok(record(
            "SourceStatic",
            &[
                ("name", quoted(&s["name"])?),
                ("kind", kind(&s["parameter"])?),
            ],
        ))
    })
}
