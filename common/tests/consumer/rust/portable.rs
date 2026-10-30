//! Independent consumer of the SDK's portable package and project surface.
use zkc::entry::{BoundInterface, FunctionInterface, Package};
include!("pins.rs");

fn main() -> Result<(), Box<dyn std::error::Error>> {
    for &(name, bytes, pin) in PACKAGES {
        let package = Package::capture(bytes, pin, Package::MAX_BYTES)?;
        assert_eq!(package.bytes(), bytes);
        let mut changed = bytes.to_vec();
        changed.push(b' ');
        assert_eq!(
            Package::capture(&changed, pin, Package::MAX_BYTES)
                .err()
                .unwrap()
                .to_string(),
            "entry-package-identity"
        );
        if name == "proof" {
            let view = BoundInterface::read(&package)?;
            assert!(view.is_proof());
            assert_eq!(view.input_groups()[0].name(), "public");
            assert!(!view.describe().is_null());
        } else {
            let view = FunctionInterface::read(&package)?;
            assert!(!view.signature().symbol.is_empty());
            assert!(!view.describe().is_null());
            assert!(view.input_group().template().is_object());
            let children = FunctionInterface::deployment_interfaces(&package)?;
            for child in children {
                assert!(!child.describe().is_null());
            }
        }
        #[cfg(feature = "files")]
        assert_eq!(zkc::files::digest(&zkc::files::hex(pin))?, *pin);
    }
    #[cfg(feature = "project")]
    project()?;
    println!("portable SDK capture and metadata passed");
    Ok(())
}

#[cfg(feature = "project")]
fn project() -> Result<(), Box<dyn std::error::Error>> {
    use zkc::project::{CheckedInterface, Compiler, Project, Selection};
    for (_, bytes, pin) in PACKAGES {
        let package = Package::capture(bytes, pin, Package::MAX_BYTES)?;
        let view = CheckedInterface::read(&package)?;
        assert!(!view.input_groups().is_empty());
    }
    // Preparation supplies an explicit compiler to exercise check/inspect/build
    // in a detached graph. Tool-free execution still covers all portable views.
    if let Some(path) = std::env::var_os("ZKC_PORTABLE_COMPILER") {
        let compiler = Compiler::new(path.to_str().ok_or("compiler path")?)?;
        let source = std::env::var("ZKC_PORTABLE_SOURCE")?;
        let project =
            Project::explicit([("application".into(), source)].into(), Default::default())?;
        let checked = compiler.check(&project, None, Default::default())?;
        assert!(
            checked
                .entries
                .iter()
                .any(|e| e.name == "application::Twice")
        );
        for (name, expected_bytes, expected_pin) in PACKAGES {
            let entry = match *name {
                "numerical" => "Twice",
                "joint" => "Echo",
                "proof" => "Core",
                "checked" => "Checked",
                "withhold" => "Withhold",
                _ => unreachable!(),
            };
            let name = format!("application::{entry}");
            let selection = Selection {
                name: Some(&name),
                kind: None,
            };
            let view = compiler.inspect(&project, selection)?;
            let package = compiler.compile(
                &project,
                selection,
                Package::capture(expected_bytes, expected_pin, Package::MAX_BYTES)?.options(),
            )?;
            assert_eq!(CheckedInterface::read(&package)?.entry(), view.entry());
            assert_eq!(
                package.bytes(),
                *expected_bytes,
                "compiler publication changed"
            );
        }
    }
    Ok(())
}
