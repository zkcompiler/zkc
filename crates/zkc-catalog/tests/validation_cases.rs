//! The shared validation cases: the catalog generator, the zkc-tblgen backend
//! and this crate's build each accept the accepted cases and refuse every
//! refused case, each with its own diagnostic. `validation_cases.py` beside the
//! case list specifies the edits.
#[path = "../codegen/projection.rs"]
mod projection;

use serde_json::Value;

fn document(text: &str) -> Value {
    serde_json::from_str(text).unwrap()
}

/// The index of the row that `where` selects; exactly one row must match.
fn selected(rows: &[Value], filter: &Value) -> usize {
    let filter = filter.as_object().unwrap();
    let matches = rows
        .iter()
        .enumerate()
        .filter(|(_, row)| {
            filter
                .iter()
                .all(|(key, value)| row.get(key) == Some(value))
        })
        .map(|(index, _)| index)
        .collect::<Vec<_>>();
    assert_eq!(
        matches.len(),
        1,
        "edit selects {} rows: {filter:?}",
        matches.len()
    );
    matches[0]
}

fn at<'a>(mut value: &'a mut Value, path: &[Value]) -> &'a mut Value {
    for key in path {
        value = match key {
            Value::String(name) => &mut value[name.as_str()],
            index => &mut value[usize::try_from(index.as_u64().unwrap()).unwrap()],
        };
    }
    value
}

fn apply(edits: &Value, declarations: &mut Value, installation: &mut Value) {
    for edit in edits.as_array().unwrap() {
        let target = match edit["document"].as_str().unwrap() {
            "declarations" => &mut *declarations,
            "installation" => &mut *installation,
            other => panic!("unknown document {other}"),
        };
        let rows = target[edit["table"].as_str().unwrap()]
            .as_array_mut()
            .unwrap();
        let op = edit["op"].as_str().unwrap();
        if op == "insert" {
            rows.push(edit["value"].clone());
            continue;
        }
        let index = selected(rows, &edit["where"]);
        match op {
            "duplicate" => {
                let copy = rows[index].clone();
                rows.push(copy);
            }
            "delete" => {
                rows.remove(index);
            }
            _ => {
                let place = at(&mut rows[index], edit["path"].as_array().unwrap());
                match op {
                    "set" => *place = edit["value"].clone(),
                    "append" => place.as_array_mut().unwrap().push(edit["value"].clone()),
                    "remove" => {
                        let list = place.as_array_mut().unwrap();
                        let before = list.len();
                        list.retain(|item| *item != edit["value"]);
                        assert!(list.len() < before, "edit removes nothing: {edit}");
                    }
                    other => panic!("unknown edit operation {other}"),
                }
            }
        }
    }
}

fn validate(case: &Value) -> Result<String, String> {
    let mut declarations = document(include_str!("../../../common/catalog/declarations.json"));
    let mut installation = document(include_str!("../../../common/catalog/installation.json"));
    apply(&case["edits"], &mut declarations, &mut installation);
    projection::generate(
        &serde_json::to_vec(&declarations).unwrap(),
        &serde_json::to_vec(&installation).unwrap(),
    )
}

fn cases() -> Value {
    document(include_str!(
        "../../../common/catalog/validation-cases.json"
    ))
}

#[test]
fn accepted_cases_validate() {
    let cases = cases();
    let accepted = cases["accepted"].as_array().unwrap();
    assert!(!accepted.is_empty());
    for case in accepted {
        if let Err(error) = validate(case) {
            panic!("{} was refused: {error}", case["name"]);
        }
    }
}

#[test]
fn refused_cases_refuse_for_their_rule() {
    let cases = cases();
    let refused = cases["refused"].as_array().unwrap();
    assert!(!refused.is_empty());
    let mut failures = Vec::new();
    for case in refused {
        let expected = case["diagnostics"]["rust"].as_str().unwrap();
        match validate(case) {
            Ok(_) => failures.push(format!("{} was accepted", case["name"])),
            Err(error) if expected.is_empty() || !error.contains(expected) => {
                failures.push(format!(
                    "{}: expected {expected:?} in {error:?}",
                    case["name"]
                ));
            }
            Err(_) => {}
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
