//! The application supplies ceilings; carriers cannot raise them.
use serde_json::json;
use zkc_tools::proof::NativeCapacity;
fn parse(value: &serde_json::Value) -> Result<NativeCapacity, String> {
    NativeCapacity::parse(&serde_json::to_vec(value).unwrap())
}
#[test]
fn strict_capacity_record_and_hard_ceilings() {
    let default = NativeCapacity::default().record();
    assert_eq!(parse(&default).unwrap().record(), default);
    for (field, limit) in [(1, 1048576u64), (2, 32768), (3, 16777216), (4, 67108864)] {
        let mut at = default.clone();
        at[field] = json!(limit.to_string());
        assert!(parse(&at).is_ok());
        at[field] = json!((limit + 1).to_string());
        assert_eq!(parse(&at).unwrap_err(), "native-capacity-limit");
        for invalid in [
            json!("01"),
            json!("-1"),
            json!(1),
            json!("18446744073709551616"),
        ] {
            at[field] = invalid;
            assert!(parse(&at).is_err());
        }
    }
    for (field, index) in [(5, 0), (5, 1), (6, 0), (6, 1)] {
        let mut at = default.clone();
        let limit: u64 = at[field][index].as_str().unwrap().parse().unwrap();
        at[field][index] = json!((limit + 1).to_string());
        assert_eq!(parse(&at).unwrap_err(), "native-capacity-limit");
        at[field][index] = json!("0");
        assert!(parse(&at).is_ok());
    }
    let mut extra = default.clone();
    extra.as_array_mut().unwrap().push(json!("unknown"));
    assert!(parse(&extra).is_err());
    let mut version = default.clone();
    version[0] = json!("zkc.native-capacity/1");
    assert_eq!(parse(&version).unwrap_err(), "native-capacity-format");
    let mut legacy_work = default.clone();
    legacy_work[5].as_array_mut().unwrap().push(json!("0"));
    assert!(parse(&legacy_work).is_err());
    assert!(NativeCapacity::parse(&vec![b' '; 4097]).is_err());
}
