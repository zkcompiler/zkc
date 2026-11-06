#[path = "../codegen/projection.rs"]
mod projection;

use serde_json::{Value, json};
use zkc_catalog::*;

fn pattern(p: ContractPattern) -> Value {
    match p {
        ContractPattern::Variable(variable) => json!({"kind":"contract", "variable":variable}),
        ContractPattern::Product(elements) => {
            json!({"kind":"product", "elements":elements.iter().copied().map(pattern).collect::<Vec<_>>()})
        }
        ContractPattern::Sequence(element, extent) => {
            let extent = match extent {
                ExtentPattern::Unsized => json!({"kind":"unsized"}),
                ExtentPattern::Variable(variable) => json!({"kind":"extent", "variable":variable}),
                ExtentPattern::Static(index) => json!({"kind":"static", "index":index}),
            };
            json!({"kind":"sequence", "element":pattern(*element), "extent":extent})
        }
    }
}
fn port(p: SchemePort) -> Value {
    match p {
        SchemePort::Descriptor(p) => json!({"kind":"descriptor", "contract":pattern(p)}),
        SchemePort::SelectedView { context, state } => {
            json!({"kind":"selectedView", "context":pattern(context), "state":pattern(state)})
        }
    }
}
fn kind(k: Kind) -> Value {
    match k {
        Kind::Type => json!({"kind":"Type", "sort":""}),
        Kind::Nat => json!({"kind":"Nat", "sort":""}),
        Kind::Domain(sort) => json!({"kind":"Domain", "sort":sort}),
    }
}
fn statics(values: &[SourceStatic]) -> Vec<Value> {
    values
        .iter()
        .map(|v| json!({"name":v.name, "parameter":kind(v.kind)}))
        .collect()
}
fn term(t: SourceTerm) -> Value {
    match t {
        SourceTerm::Constructor(constructor) => json!({"constructor":constructor}),
        SourceTerm::Static { index, member } => {
            let mut value = json!({"static":index});
            if let Some(member) = member {
                value["member"] = json!(member);
            }
            value
        }
    }
}
fn declarations() -> Value {
    serde_json::from_str(include_str!("../../../common/catalog/declarations.json")).unwrap()
}
fn validate(value: &Value) -> Result<String, String> {
    projection::generate(
        &serde_json::to_vec(value).unwrap(),
        include_bytes!("../../../common/catalog/installation.json"),
    )
}

#[test]
fn every_tagged_typed_row_exports_the_exact_authored_signature() {
    let source = declarations();
    for (row, model) in source["frontendSchemes"]
        .as_array()
        .unwrap()
        .iter()
        .zip(CATALOG.frontend_schemes)
    {
        let value = json!({"name":model.name, "form":format!("{:?}", model.form),
            "variables":model.variables.iter().map(|v| format!("{v:?}")).collect::<Vec<_>>(),
            "statics":model.statics.iter().copied().map(kind).collect::<Vec<_>>(),
            "inputs":model.inputs.iter().copied().map(port).collect::<Vec<_>>(),
            "output":pattern(model.output)});
        assert_eq!(*row, value);
    }
    for (row, model) in source["frontendDeclarations"]
        .as_array()
        .unwrap()
        .iter()
        .zip(CATALOG.frontend_declarations)
    {
        let mut value = json!({"identity":model.identity,"owner":model.owner,"name":model.name,
            "kind":format!("{:?}", model.kind), "prelude":model.prelude});
        match model.signature {
            FrontendSignature::ContractHead { constructor } => {
                value["association"] = json!({"kind":"constructor", "target":constructor});
            }
            FrontendSignature::ViewScheme {
                statics: slots,
                inputs,
                output,
                scheme,
            } => {
                value["association"] =
                    json!({"kind":"scheme", "target":CATALOG.frontend_schemes[scheme.0].name});
                value["statics"] = json!(statics(slots));
                value["inputs"] = json!(
                    inputs
                        .iter()
                        .map(|p| {
                            let mut value = port(p.port);
                            value["name"] = json!(p.name);
                            value
                        })
                        .collect::<Vec<_>>()
                );
                value["output"] = pattern(output);
            }
            FrontendSignature::Concrete(signature) => {
                let (tag, target) = match signature.association {
                    FrontendAssociation::Rule(target) => ("rule", target),
                    FrontendAssociation::Primitive(target) => ("primitive", target),
                };
                value["association"] = json!({"kind":tag,"target":target});
                value["statics"] = json!(statics(signature.statics));
                value["inputs"] = json!(
                    signature
                        .inputs
                        .iter()
                        .map(|p| json!({"name":p.name,"type":term(p.term)}))
                        .collect::<Vec<_>>()
                );
                value["output"] = signature.output.map(term).unwrap_or(Value::Null);
            }
        }
        assert_eq!(*row, value);
    }
    assert!(validate(&source).is_ok());
}

#[test]
fn bounded_recursive_patterns_and_exact_nested_fields_refuse_in_production() {
    let mut deep = json!({"kind":"contract", "variable":0});
    for _ in 0..34 {
        deep = json!({"kind":"sequence", "element":deep,"extent":{"kind":"unsized"}});
    }
    let wide =
        json!({"kind":"product","elements":vec![json!({"kind":"contract","variable":0});1025]});
    for malformed in [deep, wide] {
        let mut source = declarations();
        source["frontendSchemes"][0]["output"] = malformed;
        assert!(
            validate(&source)
                .unwrap_err()
                .contains("scheme pattern limit")
        );
    }
    let mut source = declarations();
    source["frontendSchemes"][0]["output"]["extent"]["unexpected"] = json!(true);
    assert!(
        validate(&source)
            .unwrap_err()
            .contains("unknown field unexpected")
    );
    let duplicate = include_str!("../../../common/catalog/declarations.json").replacen(
        "\"form\": \"Append\"",
        "\"form\": \"Append\", \"form\": \"Fold\"",
        1,
    );
    assert!(
        projection::generate(
            duplicate.as_bytes(),
            include_bytes!("../../../common/catalog/installation.json")
        )
        .unwrap_err()
        .contains("duplicate key form")
    );
}
