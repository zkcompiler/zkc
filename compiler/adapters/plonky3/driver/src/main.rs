//! Regenerate or check the maintained Plonky3 adapter fixtures byte for byte.
//!
//! ```text
//! zkc-plonky3-air-fixtures write NEW_DIRECTORY
//! zkc-plonky3-air-fixtures check FIXTURE_DIRECTORY
//! ```

use std::path::Path;
use std::process::ExitCode;
use zkc_plonky3_air_driver::{expected_text, files, fixtures, import_violations};

fn write(root: &Path) -> Result<(), String> {
    if root.exists() {
        return Err(format!("{} already exists", root.display()));
    }
    for fixture in fixtures().map_err(|e| e.to_string())? {
        let directory = root.join(fixture.name);
        std::fs::create_dir_all(&directory).map_err(|e| e.to_string())?;
        for (file, text) in files(&fixture) {
            std::fs::write(directory.join(file), text).map_err(|e| e.to_string())?;
        }
    }
    Ok(())
}

fn check(root: &Path) -> Result<(), String> {
    let fixtures = fixtures().map_err(|e| e.to_string())?;
    let mut expected_directories: Vec<String> =
        fixtures.iter().map(|f| f.name.to_string()).collect();
    let mut actual_directories: Vec<String> = std::fs::read_dir(root)
        .map_err(|e| e.to_string())?
        .map(|entry| {
            entry
                .map(|e| e.file_name().to_string_lossy().into_owned())
                .map_err(|e| e.to_string())
        })
        .collect::<Result<_, _>>()?;
    expected_directories.sort();
    actual_directories.sort();
    if expected_directories != actual_directories {
        return Err(format!(
            "fixture directories {actual_directories:?}, expected {expected_directories:?}"
        ));
    }
    for fixture in &fixtures {
        let directory = root.join(fixture.name);
        let read = |file: &str| {
            std::fs::read_to_string(directory.join(file)).map_err(|e| format!("{file}: {e}"))
        };
        for (file, text) in files(fixture) {
            if read(file)? != text {
                return Err(format!(
                    "{}/{file} differs from its regeneration",
                    fixture.name
                ));
            }
        }
        let imported = import_violations(
            &read("export.json")?,
            &read("instance.json")?,
            &read("witness.json")?,
        )
        .map_err(|e| format!("{}: {e}", fixture.name))?;
        if expected_text(&imported) != read("expected.json")? {
            return Err(format!(
                "{}: imported violations {imported:?} differ from upstream",
                fixture.name
            ));
        }
    }
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let result = match args.as_slice() {
        [_, command, path] if command == "write" => write(Path::new(path)),
        [_, command, path] if command == "check" => check(Path::new(path)),
        _ => Err(
            "usage: zkc-plonky3-air-fixtures (write NEW_DIRECTORY | check FIXTURE_DIRECTORY)"
                .into(),
        ),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("{message}");
            ExitCode::FAILURE
        }
    }
}
