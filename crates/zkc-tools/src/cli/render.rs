//! Human presentation of the same command report exposed by --json.
use serde_json::Value;
use std::fmt::Write;

pub fn human(report: &Value) -> String {
    let mut text = String::new();
    for (key, label) in [
        ("project", "Project"),
        ("entry", "Entry"),
        ("session", "Session"),
    ] {
        if let Some(value) = report[key].as_str() {
            writeln!(text, "{label}: {value}").unwrap();
        }
    }
    if let Some(inputs) = report["inputs"].as_object() {
        for (name, path) in inputs {
            if let Some(path) = path.as_str() {
                writeln!(text, "Input {name}: {path}").unwrap();
            }
        }
    }
    for (key, label) in [
        ("output", "Output"),
        ("proof", "Proof"),
        ("results", "Results"),
        ("package_sha256", "Package SHA-256"),
        ("proof_sha256", "Proof SHA-256"),
    ] {
        if let Some(value) = report[key].as_str() {
            writeln!(text, "{label}: {value}").unwrap();
        }
    }
    for (key, action) in [("files", "Created"), ("preserved", "Preserved")] {
        if let Some(paths) = report[key].as_array() {
            for path in paths {
                if let Some(path) = path.as_str() {
                    writeln!(text, "{action} {path}").unwrap();
                }
            }
        }
    }
    if !super::succeeded(report) {
        writeln!(
            text,
            "Error [{}]: {}",
            report["code"].as_str().unwrap_or("execution-failed"),
            report["message"]
                .as_str()
                .unwrap_or("the requested operation did not complete")
        )
        .unwrap();
        for (key, label) in [
            ("diagnostics", "Diagnostics"),
            ("conflict", "Conflict"),
            ("input_file", "Input file"),
            ("input_path", "Input path"),
        ] {
            if let Some(value) = report[key].as_str() {
                writeln!(text, "{label}: {value}").unwrap();
            }
        }
        let execution = report.get("execution").unwrap_or(report);
        for key in ["outcome", "failure", "diagnostics"] {
            let value = &execution[key];
            if !value.is_null() && value.as_array().is_none_or(|v| !v.is_empty()) {
                // Compiler diagnostics above are already plain text. Native
                // details contain control observations, not returned values.
                if key != "diagnostics" || !value.is_string() {
                    writeln!(text, "{key}: {value}").unwrap();
                }
            }
        }
        if let Some(roles) = execution["roles"].as_array() {
            for role in roles {
                let stopped = [&role["before"], &role["after"]]
                    .into_iter()
                    .find(|state| state[0] == "stopped");
                if let (Some(state), Some(name)) = (stopped, role["role"].as_str()) {
                    stop(&mut text, report, name, &state[1]);
                }
            }
        }
        if let Some(role) = execution["stop"]["role"].as_str() {
            stop(&mut text, report, role, &execution["stop"]["kind"]);
        }
        if report["code"] == "entry-input-document" || report["code"] == "entry-input-missing" {
            text.push_str("Check the selected input paths; use zkc prepare to create missing project templates.\n");
        }
        if report["code"] == "source-project-exists" {
            text.push_str("Use zkc prepare for an existing project.\n");
        }
        if report["code"] == "source-directory-exists" {
            text.push_str("Use zkc init DIRECTORY to initialize the existing directory.\n");
        }
        if report["code"] == "entry-output-codec" {
            text.push_str("An output has no file codec. For run, use --no-results to execute without result publication.\n");
        }
        if let Some(published) = report["publication"]["published"]
            .as_array()
            .filter(|v| !v.is_empty())
        {
            writeln!(
                text,
                "Published before failure: {}",
                serde_json::to_string(published).unwrap()
            )
            .unwrap();
        } else if !report["execution"].is_null() {
            text.push_str(
                "No outputs were published; existing destination files were preserved.\n",
            );
        }
        return text;
    }
    let status = match report["status"].as_str().unwrap_or("") {
        "checked" => "Source checks passed.",
        "inputs-checked" => "Inputs checked; no protocol was executed.",
        "compiled" => "Entry compiled.",
        "initialized" => "Initialized. Fill the input values before execution.",
        "prepared" => "Prepared. Existing input values were preserved.",
        "produced" => "Proof produced.",
        "accepted" => "Proof accepted.",
        "executed" => "Execution completed.",
        "generated" => "Bindings generated.",
        "inspected" => "Entry inspected.",
        _ => "Completed.",
    };
    writeln!(text, "{status}").unwrap();
    if report["format"] == "zkc.bundle-result/0" {
        text.push_str("Use --json to read participant outputs and execution details.\n");
    }
    if let Some(entries) = report["entries"].as_array() {
        for entry in entries {
            if let Some(name) = entry["name"].as_str() {
                writeln!(text, "Entry: {name}").unwrap();
            }
            requirements(&entry["requirements"], &mut text);
        }
    }
    requirements(&report["requirements"], &mut text);
    if report["status"] == "checked" && report["entries"].as_array().is_some_and(|v| !v.is_empty())
    {
        text.push_str("Use zkc prepare when input templates are needed.\n");
    }
    for key in ["interface", "declarations", "notations"] {
        if !report[key].is_null() {
            writeln!(
                text,
                "{}",
                serde_json::to_string_pretty(&report[key]).unwrap()
            )
            .unwrap();
        }
    }
    if let Some(commands) = report["commands"].as_array() {
        for command in commands {
            writeln!(
                text,
                "Command arguments: {}",
                serde_json::to_string(command).unwrap()
            )
            .unwrap();
        }
    }
    text
}
fn stop(text: &mut String, report: &Value, native_role: &str, reason: &Value) {
    let name = report["role_names"][native_role]
        .as_str()
        .unwrap_or(native_role);
    writeln!(text, "Stopped {name}: {reason}").unwrap();
}
fn requirements(requirements: &Value, text: &mut String) {
    if requirements["allow_header_only"] == true {
        text.push_str("Authored proof: explicit --allow-header-only is required.\n");
    }
    if let Some(keys) = requirements["setups"].as_array().filter(|v| !v.is_empty()) {
        writeln!(
            text,
            "Provide --setups authority and --key material for: {}",
            serde_json::to_string(keys).unwrap()
        )
        .unwrap();
    }
}
