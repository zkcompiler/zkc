//! Default project output naming. Publication remains owned by the Host.
use super::project::Inputs;

type Result<T> = std::result::Result<T, String>;

pub(super) fn default_path(inputs: &Inputs, entry: &str) -> Result<String> {
    let manifest = inputs.manifest.as_ref().ok_or("source-output-required")?;
    if !super::selection::canonical_name(entry) {
        return Err("source-entry-selection".into());
    }
    let name = format!("{}.zkpkg", entry.replace("::", "."));
    // Keep the convention usable on common filesystems. Callers can select a
    // shorter explicit output for long source names or reserved device names.
    let stem = name.split('.').next().unwrap().to_ascii_uppercase();
    if name.len() > 255
        || matches!(stem.as_str(), "CON" | "PRN" | "AUX" | "NUL")
        || ((stem.starts_with("COM") || stem.starts_with("LPT"))
            && stem.len() == 4
            && matches!(stem.as_bytes()[3], b'1'..=b'9'))
    {
        return Err("source-output-name".into());
    }
    let parent = manifest
        .parent()
        .ok_or("source-project-format")?
        .join("build/zkc");
    let path = parent.join(&name);
    let text = path
        .to_str()
        .filter(|s| s.len() <= 4096)
        .ok_or("source-output-name")?;
    std::fs::create_dir_all(&parent).map_err(|_| "source-output-directory")?;
    // The canonical name owns its exact filename, so obsolete or damaged build
    // output can be regenerated. Refuse case-folded collisions on every host to
    // keep the convention portable without interpreting previous package bytes.
    for existing in std::fs::read_dir(parent).map_err(|_| "source-output-directory")? {
        let existing = existing.map_err(|_| "source-output-directory")?.file_name();
        if existing
            .to_str()
            .is_some_and(|other| other != name && other.eq_ignore_ascii_case(&name))
        {
            return Err("source-output-collision".into());
        }
    }
    Ok(text.into())
}
