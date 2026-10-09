//! Independently derive the source relation ABI from admitted Bundle contents.
//! This checks what each formal denotes, not whether supplied data satisfies it.
use crate::entry::interface::raw::{Kind, Purpose, Relation};
use zkc_runtime::relation::{Authority, Bundle, HeightAuthority};

pub(super) fn check(bundle: &Bundle, relation: &Relation) -> Result<(), String> {
    let mut inputs = relation.inputs.iter();
    let mut formal = |purpose, kind, logical: String| -> Result<(), String> {
        let input = inputs.next().ok_or("entry-asset-relation")?;
        if input.purpose != purpose
            || input.schema.kind != kind
            || input.native.len() != 1
            || input.schema.leaves != [logical]
        {
            return Err("entry-asset-relation".into());
        }
        Ok(())
    };
    for public in bundle.publics() {
        formal(
            Purpose::Statement,
            Kind::Field,
            format!("field:{}", public.field.name()),
        )?;
    }
    for table in bundle.tables() {
        if table.optional {
            formal(Purpose::Statement, Kind::Boolean, "bool".into())?;
        }
        match table.height.authority {
            HeightAuthority::Fixed => (),
            HeightAuthority::Config => formal(Purpose::Parameter, Kind::Index, "index".into())?,
            HeightAuthority::Instance => formal(Purpose::Statement, Kind::Index, "index".into())?,
        }
        for group in &table.groups {
            formal(
                match group.authority {
                    Authority::Witness => Purpose::Witness,
                    Authority::Config => Purpose::Parameter,
                    Authority::Public => Purpose::Statement,
                },
                Kind::Builtin,
                format!("vector:{}", group.field.name()),
            )?;
        }
    }
    if inputs.next().is_some() {
        return Err("entry-asset-relation".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::{Value, json};
    use zkc_runtime::{
        interactive::Identity,
        relation::{Group, Height, ReadModel, Slot, Table},
        ring::Expression,
    };

    fn fixture() -> Bundle {
        let group = |name: &str, authority, field| Group {
            name: name.into(),
            authority,
            field,
            width: 1,
        };
        let table = |name: &str, optional, authority, groups| Table {
            name: name.into(),
            optional,
            height: Height {
                authority,
                min: 1,
                max: 8,
                power_of_two: false,
            },
            read_model: ReadModel::Finite,
            groups,
            arena: Expression::new(vec![], vec![], vec![]).unwrap(),
            inputs: vec![],
            assertions: vec![],
            interactions: vec![],
        };
        Bundle::new(
            vec![
                Slot {
                    name: "x".into(),
                    field: Identity::KoalaBear,
                },
                Slot {
                    name: "y".into(),
                    field: Identity::KoalaBearExt8,
                },
            ],
            vec![],
            vec![
                table(
                    "rom",
                    false,
                    HeightAuthority::Config,
                    vec![
                        group("fixed", Authority::Config, Identity::KoalaBear),
                        group("trace", Authority::Witness, Identity::KoalaBearExt8),
                    ],
                ),
                table(
                    "optional",
                    true,
                    HeightAuthority::Instance,
                    vec![group("public", Authority::Public, Identity::KoalaBear)],
                ),
            ],
        )
        .unwrap()
    }
    fn declaration(bundle: &Bundle) -> Value {
        let formal = |name, purpose, kind, logical| {
            json!({
                "name":name,"purpose":purpose,"native":[0],
                "schema":{"kind":kind,"identity":"0".repeat(64),"type":logical,
                    "custody":false,"permissions":["Copy","Drop","Share","Wire"],
                    "fields":[],"alternatives":[],"leaves":[logical]},
            })
        };
        json!({"symbol":"Relation","definition":{"kind":"bundle","asset":bundle.identity()},
        "inputs":[
            formal("x","statement","field","field:koala-bear"),
            formal("y","statement","field","field:koala-bear.ext8-binomial3"),
            formal("height","parameter","index","index"),
            formal("fixed","parameter","builtin","vector:koala-bear"),
            formal("trace","witness","builtin","vector:koala-bear.ext8-binomial3"),
            formal("present","statement","boolean","bool"),
            formal("rows","statement","index","index"),
            formal("public","statement","builtin","vector:koala-bear"),
        ]})
    }
    #[test]
    fn derives_authority_field_presence_and_height_from_bundle() {
        let bundle = fixture();
        let declaration = declaration(&bundle);
        check(
            &bundle,
            &serde_json::from_value(declaration.clone()).unwrap(),
        )
        .unwrap();
        for (path, changed) in [
            ("/inputs/0/purpose", json!("witness")),
            ("/inputs/1/schema/leaves", json!(["koala-bear"])),
            ("/inputs/2/purpose", json!("statement")),
            (
                "/inputs/3/schema/leaves",
                json!(["vector:koala-bear.ext8-binomial3"]),
            ),
            ("/inputs/4/purpose", json!("parameter")),
            ("/inputs/5/schema/kind", json!("index")),
            ("/inputs/6/purpose", json!("parameter")),
            ("/inputs/7/native", json!([0, 1])),
        ] {
            let mut altered = declaration.clone();
            *altered.pointer_mut(path).unwrap() = changed;
            assert_eq!(
                check(&bundle, &serde_json::from_value(altered).unwrap()),
                Err("entry-asset-relation".into()),
                "{path}"
            );
        }
        for append in [false, true] {
            let mut altered = declaration.clone();
            let inputs = altered["inputs"].as_array_mut().unwrap();
            if append {
                inputs.push(inputs[0].clone());
            } else {
                inputs.pop();
            }
            assert_eq!(
                check(&bundle, &serde_json::from_value(altered).unwrap()),
                Err("entry-asset-relation".into())
            );
        }
    }
}
