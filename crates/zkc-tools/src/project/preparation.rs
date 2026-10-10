//! Checked plans for source projects and input templates, without file publication.
use super::{Compiler, Error, Project, Selection, input_path};
use crate::entry::Interface;
use std::path::{Path, PathBuf};

/// A file to create, never an instruction to replace user data.
pub struct Template {
    pub path: PathBuf,
    pub contents: String,
}
impl Template {
    pub fn inputs(directory: &Path, interface: &Interface) -> Result<Vec<Self>, String> {
        let mut paths = std::collections::BTreeSet::new();
        interface
            .input_groups()
            .iter()
            .filter(|group| !group.is_empty())
            .map(|group| {
                let path = input_path(directory, group.name())?;
                if !paths.insert(path.to_string_lossy().to_ascii_lowercase()) {
                    return Err("source-output-collision".into());
                }
                Ok(Self {
                    path,
                    contents: serde_json::to_string_pretty(&group.template())
                        .expect("serializable template")
                        + "\n",
                })
            })
            .collect()
    }
    pub(crate) fn scaffold(directory: &Path) -> Vec<Self> {
        [
            ("zkc.toml", "format = \"zkc.project/0\"\n\n[modules]\nexample = \"main.zkc\"\nexample_protocol = \"protocol.zkc\"\n"),
            ("protocol.zkc", "module example_protocol;\n\npub protocol Echo roles(P)(value: index @P) -> (result: index @P) {\n  return value;\n}\n"),
            ("main.zkc", "module example;\nuse example_protocol::{Echo};\n\nrun Main = Echo;\n"),
        ].into_iter().map(|(name, contents)| Self { path: directory.join(name), contents: contents.into() }).collect()
    }
}

/// Every selected interface is checked before any template is published.
/// Existing input contents are deliberately outside this plan's authority.
pub struct Preparation {
    pub entries: Vec<Interface>,
    pub templates: Vec<Template>,
}
impl Compiler {
    pub fn prepare(&self, project: &Project, name: Option<&str>) -> Result<Preparation, Error> {
        let layout = project.layout().ok_or("source-project-required")?;
        let names = if let Some(name) = name {
            vec![name.to_owned()]
        } else {
            self.check(project, None, Default::default())?
                .entries
                .into_iter()
                .map(|entry| entry.name)
                .collect()
        };
        let mut plan = Preparation {
            entries: Vec::new(),
            templates: Vec::new(),
        };
        let mut directories = std::collections::BTreeSet::new();
        for name in names {
            let interface = self.inspect(
                project,
                Selection {
                    name: Some(&name),
                    kind: None,
                },
            )?;
            if interface
                .input_groups()
                .iter()
                .any(|group| !group.is_empty())
            {
                let directory = layout.inputs(interface.entry())?;
                if !directories.insert(directory.to_string_lossy().to_ascii_lowercase()) {
                    return Err("source-output-collision".into());
                }
                plan.templates
                    .extend(Template::inputs(&directory, &interface)?);
            }
            plan.entries.push(interface);
        }
        Ok(plan)
    }
}
