//! Read witness locations from the pinned Circom fixture's canonical .sym file.
use std::path::Path;

pub fn witness_index(path: &Path, name: &str) -> usize {
    let symbols =
        std::fs::read_to_string(path).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
    symbols
        .lines()
        .find_map(|line| {
            let columns: Vec<_> = line.splitn(4, ',').collect();
            (columns.len() == 4 && columns[3] == name).then(|| {
                columns[1]
                    .parse::<usize>()
                    .expect("the control must use a retained witness cell")
            })
        })
        .unwrap_or_else(|| panic!("{} has no symbol {name}", path.display()))
}
